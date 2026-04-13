(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* One complete SHA-256 round group: 4 compression rounds + schedule update.  *)
(*                                                                           *)
(* Combines K-constant loading, ADD V.4S pre-addition, SHA256H/SHA256H2      *)
(* compression, and SHA256SU0/SHA256SU1 message schedule update.             *)
(* The postcondition connects to the FIPS 180-4 spec with separate K and W   *)
(* (via SHA256H_BRIDGE + SHA256_COMPRESS_ROUND_PREADD) and the message       *)
(* schedule (via SHA256SU_BRIDGE).                                           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code.                                                             *)
(*   0: 3dc00030  ldr q16, [x1]                                             *)
(*   4: 4eb08482  add v2.4s, v4.4s, v16.4s                                  *)
(*   8: 4ea01c03  mov v3.16b, v0.16b                                        *)
(*   c: 5e024020  sha256h q0, q1, v2.4s                                     *)
(*  10: 5e025061  sha256h2 q1, q3, v2.4s                                    *)
(*  14: 5e2828a4  sha256su0 v4.4s, v5.4s                                    *)
(*  18: 5e0760c4  sha256su1 v4.4s, v6.4s, v7.4s                             *)
(*  1c: d65f03c0  ret                                                        *)
(* ------------------------------------------------------------------------- *)

let sha256_roundgroup_mc = define_assert_from_elf "sha256_roundgroup_mc"
  (file_on_path !load_path "arm/sha2/sha256_roundgroup.o")
  [0x3dc00030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 0)) *)
   0x4eb08482;       (* arm_ADD_VEC Q2 Q4 Q16 32 128 *)
   0x4ea01c03;       (* arm_MOV_VEC Q3 Q0 128 *)
   0x5e024020;       (* arm_SHA256H Q0 Q1 Q2 *)
   0x5e025061;       (* arm_SHA256H2 Q1 Q3 Q2 *)
   0x5e2828a4;       (* arm_SHA256SU0 Q4 Q5 *)
   0x5e0760c4;       (* arm_SHA256SU1 Q4 Q6 Q7 *)
   0xd65f03c0        (* arm_RET X30 *)];;

let EXEC = ARM_MK_EXEC_RULE sha256_roundgroup_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness: one SHA-256 round group (4 rounds + schedule update).        *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q0 = ABCD, Q1 = EFGH (state)                                           *)
(*   Q4..Q7 = W[0..15] (message schedule, 4 words per register)             *)
(*   x1 = pointer to K[0..3] constants                                      *)
(*                                                                           *)
(* Outputs:                                                                  *)
(*   Q0, Q1 = state after 4 compression rounds (with K[0..3] and W[0..3])   *)
(*   Q4 = W[16..19] (4 new message schedule words per FIPS 180-4)           *)
(* ------------------------------------------------------------------------- *)

let SHA256_ROUNDGROUP_CORRECT = prove(
 `!(a:int32) b c d (e:int32) f g h
   (k0:int32) k1 k2 k3
   (w0:int32) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
   kptr pc ret_pc.
   nonoverlapping (kptr, 16) (word pc, 32)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_roundgroup_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X1 s = kptr /\
         read Q0 s = word_join4 a b c d /\
         read Q1 s = word_join4 e f g h /\
         read Q4 s = word_join4 w0 w1 w2 w3 /\
         read Q5 s = word_join4 w4 w5 w6 w7 /\
         read Q6 s = word_join4 w8 w9 w10 w11 /\
         read Q7 s = word_join4 w12 w13 w14 w15 /\
         read (memory :> bytes128 kptr) s = word_join4 k0 k1 k2 k3)
    (\s. read PC s = word ret_pc /\
         read Q0 s =
           (let state = [a;b;c;d;e;f;g;h] in
            let s1 = sha256_compress_round k0 w0 state in
            let s2 = sha256_compress_round k1 w1 s1 in
            let s3 = sha256_compress_round k2 w2 s2 in
            let s4 = sha256_compress_round k3 w3 s3 in
            word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)) /\
         read Q1 s =
           (let state = [a;b;c;d;e;f;g;h] in
            let s1 = sha256_compress_round k0 w0 state in
            let s2 = sha256_compress_round k1 w1 s1 in
            let s3 = sha256_compress_round k2 w2 s2 in
            let s4 = sha256_compress_round k3 w3 s3 in
            word_join4 (EL 4 s4) (EL 5 s4) (EL 6 s4) (EL 7 s4)) /\
         read Q4 s =
           (let w16 = word_add (sha256_sigma1 w14)
                        (word_add w9 (word_add (sha256_sigma0 w1) w0)) in
            let w17 = word_add (sha256_sigma1 w15)
                        (word_add w10 (word_add (sha256_sigma0 w2) w1)) in
            let w18 = word_add (sha256_sigma1 w16)
                        (word_add w11 (word_add (sha256_sigma0 w3) w2)) in
            let w19 = word_add (sha256_sigma1 w17)
                        (word_add w12 (word_add (sha256_sigma0 w4) w3)) in
            word_join4 w16 w17 w18 w19))
    (MAYCHANGE [PC] ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q16] ,,
     MAYCHANGE [events])`,

  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-2: LDR K constants + ADD V.4S pre-addition *)
  ARM_STEPS_TAC EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32]) THEN

  (* Steps 3-8: MOV + SHA256H + SHA256H2 + SHA256SU0 + SHA256SU1 + RET *)
  ARM_STEPS_TAC EXEC (3--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  (* Connect to spec:
     1. Expand let bindings
     2. Bridging lemmas: sha256h → compress_round, sha256su → schedule
     3. Pre-addition: (word_add K W, word 0) → (K, W)
     4. Commutativity: compress_round W K = compress_round K W *)
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;
              CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE;
              CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256SU_BRIDGE] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_KW_SYM]);;
