(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 2 rounds of SHA-512 compression, register-only (no memory ops).           *)
(*                                                                           *)
(* Smallest-meaningful-unit proof for SHA-512 HW verification: one           *)
(* SHA512H + SHA512H2 pair performs exactly 2 rounds of compression. This   *)
(* validates the SHA512H_BRIDGE and SHA512H2_BRIDGE lemmas end-to-end        *)
(* against the ARM64 symbolic executor before scaling to the full 80-round  *)
(* register-only core (Phase D).                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha512_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code extracted from the assembled .o file.                        *)
(*    0: 6e034045  ext      v5.16b, v2.16b, v3.16b, #8                       *)
(*    4: 6e024026  ext      v6.16b, v1.16b, v2.16b, #8                       *)
(*    8: 4ef88463  add      v3.2d, v3.2d, v24.2d                             *)
(*    c: ce6680a3  sha512h  q3, q5, v6.2d                                    *)
(*   10: 4ee38424  add      v4.2d, v1.2d, v3.2d                              *)
(*   14: ce608423  sha512h2 q3, q1, v0.2d                                    *)
(*   18: d65f03c0  ret                                                       *)
(* ------------------------------------------------------------------------- *)

let sha512_2rounds_reg_mc = define_assert_from_elf "sha512_2rounds_reg_mc"
  (file_on_path !load_path "arm/sha2/sha512_2rounds_reg.o")
  [0x6e034045;       (* arm_EXT Q5 Q2 Q3 64 *)
   0x6e024026;       (* arm_EXT Q6 Q1 Q2 64 *)
   0x4ef88463;       (* arm_ADD_VEC Q3 Q3 Q24 64 128 *)
   0xce6680a3;       (* arm_SHA512H Q3 Q5 Q6 *)
   0x4ee38424;       (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
   0xce608423;       (* arm_SHA512H2 Q3 Q1 Q0 *)
   0xd65f03c0        (* arm_RET X30 *)];;

let EXEC = ARM_MK_EXEC_RULE sha512_2rounds_reg_mc;;

(* ------------------------------------------------------------------------- *)
(* Helper: a 128-bit slice from bit 64 of a word_join of two 128-bit halves  *)
(* (each a word_join of two int64s) collapses to word_join of the two        *)
(* middle 64-bit words. Reduces the output of EXT #8 to the intended lane    *)
(* rearrangement.                                                            *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_MID64 = prove
 (`!(hi:int64) (mid1:int64) (mid2:int64) (lo:int64).
     word_subword ((word_join:int128->int128->256 word)
                    ((word_join:int64->int64->int128) hi mid1)
                    ((word_join:int64->int64->int128) mid2 lo))
                  (64,128) : int128 =
     (word_join:int64->int64->int128) mid1 mid2`,
  REPEAT GEN_TAC THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Correctness: the assembly computes 2 rounds of SHA-512 compression.       *)
(*                                                                           *)
(* Input:                                                                    *)
(*   Q0  = word_join b a          (state {b, a}, hi=b, lo=a)                 *)
(*   Q1  = word_join d c          (state {d, c})                             *)
(*   Q2  = word_join f e          (state {f, e})                             *)
(*   Q3  = word_join h g          (state {h, g})                             *)
(*   Q24 = word_join kw0 kw1      (pre-packed K+W for these two rounds)      *)
(*                                                                           *)
(* Output:                                                                   *)
(*   Q3 = word_join (EL 1 s2) (EL 0 s2)   (new {b', a'} half of state)       *)
(*   Q4 = word_join (EL 5 s2) (EL 4 s2)   (new {d', c'} half of state)       *)
(* where  s1 = sha512_compress_round kw0 (word 0) [a;b;c;d;e;f;g;h]          *)
(*        s2 = sha512_compress_round kw1 (word 0) s1.                        *)
(* ------------------------------------------------------------------------- *)

let SHA512_2ROUNDS_REG_CORRECT = prove
 (`!(a:int64) (b:int64) (c:int64) (d:int64) (e:int64) (f:int64)
    (g:int64) (h:int64) (kw0:int64) (kw1:int64)
    pc ret_pc.
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha512_2rounds_reg_mc /\
          read PC s = word pc /\
          read X30 s = word ret_pc /\
          read Q0 s = (word_join:int64->int64->int128) b a /\
          read Q1 s = (word_join:int64->int64->int128) d c /\
          read Q2 s = (word_join:int64->int64->int128) f e /\
          read Q3 s = (word_join:int64->int64->int128) h g /\
          read Q24 s = (word_join:int64->int64->int128) kw0 kw1)
     (\s. read PC s = word ret_pc /\
          read Q3 s =
            (let state = [a;b;c;d;e;f;g;h] in
             let s1 = sha512_compress_round kw0 (word 0) state in
             let s2 = sha512_compress_round kw1 (word 0) s1 in
             (word_join:int64->int64->int128) (EL 1 s2) (EL 0 s2)) /\
          read Q4 s =
            (let state = [a;b;c;d;e;f;g;h] in
             let s1 = sha512_compress_round kw0 (word 0) state in
             let s2 = sha512_compress_round kw1 (word 0) s1 in
             (word_join:int64->int64->int128) (EL 5 s2) (EL 4 s2)))
     (MAYCHANGE [PC] ,, MAYCHANGE [Q3; Q4; Q5; Q6] ,, MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_JOIN_64_HI_LO; WORD_JOIN_MID64] THEN
  REWRITE_TAC[SHA512H_BRIDGE_FLAT; WORD_JOIN_64_HI_LO] THEN
  REWRITE_TAC[SHA512H2_BRIDGE_FLAT] THEN
  REWRITE_TAC[sha512_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL; HD; TL] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REFL_TAC);;
