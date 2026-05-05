(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-512 single-block compression core: 80 rounds + state add-back.        *)
(*                                                                           *)
(* Proves correctness of a straight-line ARM64 implementation that uses      *)
(* SHA512H/SHA512H2/SHA512SU0/SHA512SU1 hardware instructions for 40 round  *)
(* groups (2 rounds each = 80 total), with final state add-back.             *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q0 = word_join b a, Q1 = word_join d c,                                *)
(*   Q2 = word_join f e, Q3 = word_join h g                                 *)
(*   Q16..Q23 = schedule pairs, Q(16+j) = word_join w(2j+1) w(2j)           *)
(*              (already byte-reversed from memory order)                    *)
(*   X3 = pointer to K table, 80 x int64 = 640 bytes                        *)
(*                                                                           *)
(* Output: Q0..Q3 = final state (compressed + initial add-back).             *)
(*                                                                           *)
(* Register rotation follows aws-lc's 5-phase cycle on v0..v4; after 40      *)
(* groups (40 mod 5 = 0) the state is back in v0..v3 ready for add-back.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha512_bridge.ml";;

(* ========================================================================= *)
(* Helper lemmas / conversions (SHA-256 analogues).                          *)
(* ========================================================================= *)

let EL_RECONSTRUCT_512 = end_itlist CONJ (List.map (fun n ->
  prove(subst[mk_small_numeral n, `n:num`]
    `!s:int64 list. EL n [EL 0 s; EL 1 s; EL 2 s; EL 3 s;
      EL 4 s; EL 5 s; EL 6 s; EL 7 s] = EL n s`,
    GEN_TAC THEN CONV_TAC(LAND_CONV EL_CONV) THEN REFL_TAC)) (0--7));;

let SHA512_COMPRESS_ROUND_EL_LIST = prove
 (`!K W s:int64 list.
    sha512_compress_round K W [EL 0 s; EL 1 s; EL 2 s; EL 3 s;
      EL 4 s; EL 5 s; EL 6 s; EL 7 s] = sha512_compress_round K W s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha512_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[EL_RECONSTRUCT_512]);;

(* Unroll sha512_compress n W state to n nested sha512_compress_round calls. *)
let rec SHA512_COMPRESS_UNROLL_CONV tm =
  let n_tm = rand(rator(rator tm)) in
  if n_tm = `0` then REWRITE_CONV[sha512_compress] tm
  else
    let n = dest_small_numeral n_tm in
    let arith_th = ARITH_RULE
      (mk_eq(n_tm, mk_comb(mk_comb(`(+)`, mk_small_numeral(n-1)), `1`))) in
    let step1 = ONCE_REWRITE_CONV[arith_th] tm in
    let step2 = CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[sha512_compress])) step1 in
    CONV_RULE(RAND_CONV(RAND_CONV SHA512_COMPRESS_UNROLL_CONV)) step2;;

(* ========================================================================= *)
(* Machine code and execution rule.                                          *)
(* ========================================================================= *)

let sha512_block_core_mc = define_from_elf "sha512_block_core_mc"
  (file_on_path !load_path "arm/sha2/sha512_block_core.o");;

let EXEC = ARM_MK_EXEC_RULE sha512_block_core_mc;;

(* ========================================================================= *)
(* Placeholder correctness theorem (Phase D work in progress).               *)
(* ========================================================================= *)

let SHA512_BLOCK_CORE_CORRECT = prove
 (`!(a:int64) b c d (e:int64) f g h
    (w0:int64) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    kptr pc ret_pc.
    nonoverlapping (kptr, 640) (word pc, LENGTH sha512_block_core_mc)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha512_block_core_mc /\
          read PC s = word pc /\
          read X30 s = word ret_pc /\
          read X3 s = kptr /\
          read Q0 s = (word_join:int64->int64->int128) b a /\
          read Q1 s = (word_join:int64->int64->int128) d c /\
          read Q2 s = (word_join:int64->int64->int128) f e /\
          read Q3 s = (word_join:int64->int64->int128) h g /\
          read Q16 s = (word_join:int64->int64->int128) w1 w0 /\
          read Q17 s = (word_join:int64->int64->int128) w3 w2 /\
          read Q18 s = (word_join:int64->int64->int128) w5 w4 /\
          read Q19 s = (word_join:int64->int64->int128) w7 w6 /\
          read Q20 s = (word_join:int64->int64->int128) w9 w8 /\
          read Q21 s = (word_join:int64->int64->int128) w11 w10 /\
          read Q22 s = (word_join:int64->int64->int128) w13 w12 /\
          read Q23 s = (word_join:int64->int64->int128) w15 w14 /\
          (!i. i < 40 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
            (word_join:int64->int64->int128)
              (EL (2 * i + 1) sha512_K) (EL (2 * i) sha512_K)))
     (\s. read PC s = word ret_pc /\
          (let M = [w0;w1;w2;w3;w4;w5;w6;w7;
                    w8;w9;w10;w11;w12;w13;w14;w15] in
           let H = [a;b;c;d;e;f;g;h] in
           let result = sha512_block M H in
           read Q0 s = (word_join:int64->int64->int128)
                         (EL 1 result) (EL 0 result) /\
           read Q1 s = (word_join:int64->int64->int128)
                         (EL 3 result) (EL 2 result) /\
           read Q2 s = (word_join:int64->int64->int128)
                         (EL 5 result) (EL 4 result) /\
           read Q3 s = (word_join:int64->int64->int128)
                         (EL 7 result) (EL 6 result)))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                 Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24;
                 Q28; Q29; Q30; Q31] ,,
      MAYCHANGE [events])`,
  CHEAT_TAC);;
