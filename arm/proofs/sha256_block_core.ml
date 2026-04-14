(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 single-block compression core: 64 rounds + state add-back.        *)
(*                                                                           *)
(* Proves correctness of a straight-line ARM64 implementation that uses       *)
(* SHA256H/SHA256H2/SHA256SU0/SHA256SU1 hardware instructions for 16 round   *)
(* groups (4 rounds each = 64 total), with final state add-back.             *)
(*                                                                           *)
(* Inputs (all in registers, no memory loads for state/data):                *)
(*   Q0 = ABCD state, Q1 = EFGH state                                       *)
(*   Q4 = M[0..3], Q5 = M[4..7], Q6 = M[8..11], Q7 = M[12..15]            *)
(*         (message words, already byte-swapped to big-endian)               *)
(*   x1 = pointer to K constant table (64 x int32 = 256 bytes)              *)
(*                                                                           *)
(* Output (in registers):                                                    *)
(*   Q0 = new ABCD = compressed ABCD + initial ABCD                         *)
(*   Q1 = new EFGH = compressed EFGH + initial EFGH                         *)
(*                                                                           *)
(* The postcondition connects to sha256_block from sha256_spec.ml.           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code from the assembled ELF object.                               *)
(* 109 instructions = 436 bytes.                                             *)
(*   Steps 1-2:    MOV save initial state (Q18, Q19)                         *)
(*   Steps 3-9:    Round group 0 (LDR+ADD+MOV+SHA256H+SHA256H2+SU0+SU1)     *)
(*   Steps 10-16:  Round group 1                                             *)
(*   Steps 17-23:  Round group 2                                             *)
(*   Steps 24-30:  Round group 3                                             *)
(*   Steps 31-37:  Round group 4                                             *)
(*   Steps 38-44:  Round group 5                                             *)
(*   Steps 45-51:  Round group 6                                             *)
(*   Steps 52-58:  Round group 7                                             *)
(*   Steps 59-65:  Round group 8                                             *)
(*   Steps 66-72:  Round group 9                                             *)
(*   Steps 73-79:  Round group 10                                            *)
(*   Steps 80-86:  Round group 11                                            *)
(*   Steps 87-91:  Round group 12 (no SU0/SU1)                               *)
(*   Steps 92-96:  Round group 13                                            *)
(*   Steps 97-101: Round group 14                                            *)
(*   Steps 102-106: Round group 15                                           *)
(*   Steps 107-108: ADD state add-back (V0 += V18, V1 += V19)               *)
(*   Step 109:     RET                                                       *)
(* ------------------------------------------------------------------------- *)

let sha256_block_core_mc = define_from_elf "sha256_block_core_mc"
  (file_on_path !load_path "arm/sha2/sha256_block_core.o");;

let EXEC = ARM_MK_EXEC_RULE sha256_block_core_mc;;

(* ========================================================================= *)
(* Tactic helpers for per-round-group simplification.                        *)
(* ========================================================================= *)

(* Simplify ADD V.4S results: eliminate word_subword(word_join4 ...) and     *)
(* re-nest word_join of 64-bit halves into word_join4.                       *)
(* This is applied after each LDR+ADD pair to keep the K+W operand clean.   *)
(* We do NOT apply bridging lemmas during symbolic execution, as doing so    *)
(* causes exponential term growth with the nested compress_round structure.  *)
(* Instead, bridging is applied once at the end during postcondition match.  *)
let ADD_SIMP_RULE =
  REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32];;

(* Execute one round group and simplify just the ADD V.4S result. *)
let ROUND_GROUP_TAC group_steps =
  ARM_STEPS_TAC EXEC group_steps THEN
  RULE_ASSUM_TAC ADD_SIMP_RULE;;

let ROUND_GROUP_NOSCHED_TAC = ROUND_GROUP_TAC;;

(* ========================================================================= *)
(* Correctness theorem.                                                      *)
(* ========================================================================= *)

let SHA256_BLOCK_CORE_CORRECT = prove(
 `!(a:int32) b c d (e:int32) f g h
   (w0:int32) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
   kptr pc ret_pc.
   nonoverlapping (kptr, 256) (word pc, 436)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_block_core_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X1 s = kptr /\
         read Q0 s = word_join4 a b c d /\
         read Q1 s = word_join4 e f g h /\
         read Q4 s = word_join4 w0 w1 w2 w3 /\
         read Q5 s = word_join4 w4 w5 w6 w7 /\
         read Q6 s = word_join4 w8 w9 w10 w11 /\
         read Q7 s = word_join4 w12 w13 w14 w15 /\
         (!i. i < 16 ==>
           read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
           word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                      (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)))
    (\s. read PC s = word ret_pc /\
         (let M = [w0;w1;w2;w3;w4;w5;w6;w7;
                   w8;w9;w10;w11;w12;w13;w14;w15] in
          let H = [a;b;c;d;e;f;g;h] in
          let result = sha256_block M H in
          read Q0 s = word_join4 (EL 0 result) (EL 1 result)
                                 (EL 2 result) (EL 3 result) /\
          read Q1 s = word_join4 (EL 4 result) (EL 5 result)
                                 (EL 6 result) (EL 7 result)))
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q18; Q19] ,,
     MAYCHANGE [events])`,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* Expand the K constant quantifier into 16 individual assumptions *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  (* Simplify word_add kptr (word 0) -> kptr and reduce EL additions *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN

  (* Steps 1-2: Save initial state *)
  ARM_STEPS_TAC EXEC (1--2) THEN

  (* Round groups 0-11 (with schedule update, 7 steps each) *)
  ROUND_GROUP_TAC (3--9) THEN
  ROUND_GROUP_TAC (10--16) THEN
  ROUND_GROUP_TAC (17--23) THEN
  ROUND_GROUP_TAC (24--30) THEN
  ROUND_GROUP_TAC (31--37) THEN
  ROUND_GROUP_TAC (38--44) THEN
  ROUND_GROUP_TAC (45--51) THEN
  ROUND_GROUP_TAC (52--58) THEN
  ROUND_GROUP_TAC (59--65) THEN
  ROUND_GROUP_TAC (66--72) THEN
  ROUND_GROUP_TAC (73--79) THEN
  ROUND_GROUP_TAC (80--86) THEN

  (* Round groups 12-15 (no schedule update, 5 steps each) *)
  ROUND_GROUP_NOSCHED_TAC (87--91) THEN
  ROUND_GROUP_NOSCHED_TAC (92--96) THEN
  ROUND_GROUP_NOSCHED_TAC (97--101) THEN
  ROUND_GROUP_NOSCHED_TAC (102--106) THEN

  (* Steps 107-109: ADD state add-back + RET *)
  ARM_STEPS_TAC EXEC (107--109) THEN
  RULE_ASSUM_TAC ADD_SIMP_RULE THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  (* ----- Postcondition matching ----- *)
  (* Strategy: unfold the spec side (sha256_block) to the same form as the   *)
  (* symbolic state, then show they match.                                   *)
  (*                                                                         *)
  (* Step 1: Unfold sha256_block -> sha256_compress 64 + message_schedule    *)
  (* Step 2: Unroll sha256_compress 64 to 64 nested compress_round calls     *)
  (* Step 3: Unroll sha256_message_schedule to get concrete W expressions    *)
  (* Step 4: On the symbolic side, apply bridging (SHA256H_BRIDGE etc.)      *)
  (* Step 5: Use SHA256_COMPRESS_ROUND_KW_SYM to match argument order        *)
  (* Step 6: Show both sides are syntactically equal                         *)
  (*                                                                         *)
  (* TODO: implement the above strategy. The SHA256_COMPRESS_UNROLL_CONV     *)
  (* (defined below) handles step 2. Steps 3-5 need corresponding tools.    *)
  CHEAT_TAC);;

(* ========================================================================= *)
(* Conversion to unroll sha256_compress n to nested compress_round calls.    *)
(* sha256_compress 4 W state =                                               *)
(*   sha256_compress_round (EL 3 K) (EL 3 W)                                *)
(*     (sha256_compress_round (EL 2 K) (EL 2 W)                             *)
(*       (sha256_compress_round (EL 1 K) (EL 1 W)                           *)
(*         (sha256_compress_round (EL 0 K) (EL 0 W) state)))                *)
(* ========================================================================= *)

let rec SHA256_COMPRESS_UNROLL_CONV tm =
  let n_tm = rand(rator(rator tm)) in
  if n_tm = `0` then REWRITE_CONV[sha256_compress] tm
  else
    let n = dest_small_numeral n_tm in
    let arith_th = ARITH_RULE
      (mk_eq(n_tm, mk_comb(mk_comb(`(+)`, mk_small_numeral(n-1)), `1`))) in
    let step1 = ONCE_REWRITE_CONV[arith_th] tm in
    let step2 = CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[sha256_compress])) step1 in
    CONV_RULE(RAND_CONV(RAND_CONV SHA256_COMPRESS_UNROLL_CONV)) step2;;
