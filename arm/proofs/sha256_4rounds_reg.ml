(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 4 rounds of SHA-256 compression, register-only (no memory ops).          *)
(*                                                                           *)
(* Proves that a 4-instruction sequence (MOV + SHA256H + SHA256H2 + RET)     *)
(* correctly implements 4 rounds of sha256_compress_round from the           *)
(* algorithmic spec, using the bridging lemmas from sha256_bridge.ml.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code extracted from the assembled .o file.                        *)
(*   0: 4ea01c03  mov v3.16b, v0.16b      (ORR_VEC Q3 Q0 Q0 128)           *)
(*   4: 5e024020  sha256h q0, q1, v2.4s   (SHA256H Q0 Q1 Q2)               *)
(*   8: 5e025061  sha256h2 q1, q3, v2.4s  (SHA256H2 Q1 Q3 Q2)              *)
(*   c: d65f03c0  ret                      (RET X30)                         *)
(* ------------------------------------------------------------------------- *)

let sha256_4rounds_reg_mc = define_assert_from_elf "sha256_4rounds_reg_mc"
  (file_on_path !load_path "arm/sha2/sha256_4rounds_reg.o")
  [0x4ea01c03;       (* arm_MOV_VEC Q3 Q0 128 *)
   0x5e024020;       (* arm_SHA256H Q0 Q1 Q2 *)
   0x5e025061;       (* arm_SHA256H2 Q1 Q3 Q2 *)
   0xd65f03c0        (* arm_RET X30 *)];;

let EXEC = ARM_MK_EXEC_RULE sha256_4rounds_reg_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness: the assembly computes 4 rounds of SHA-256 compression.       *)
(*                                                                           *)
(* Input registers:                                                          *)
(*   Q0 = word_join4 a b c d     (state ABCD, packed)                        *)
(*   Q1 = word_join4 e f g h     (state EFGH, packed)                        *)
(*   Q2 = word_join4 kw0 kw1 kw2 kw3  (pre-added K[t]+W[t], packed)         *)
(*                                                                           *)
(* Output registers:                                                         *)
(*   Q0 = ABCD half of state after 4 rounds of sha256_compress_round         *)
(*   Q1 = EFGH half of state after 4 rounds of sha256_compress_round         *)
(*                                                                           *)
(* The round keys kw0..kw3 are pre-added (K[t]+W[t]); the spec's W_t        *)
(* argument is word 0, so sha256_compress_round kw (word 0) state gives      *)
(* T1 = h + Sigma1(e) + Ch(e,f,g) + kw + 0 = h + Sigma1(e) + Ch(e,f,g)+kw. *)
(* ------------------------------------------------------------------------- *)

let SHA256_4ROUNDS_REG_CORRECT = prove(
 `!(a:int32) (b:int32) (c:int32) (d:int32) (e:int32) (f:int32)
   (g:int32) (h:int32) (kw0:int32) (kw1:int32) (kw2:int32) (kw3:int32)
   pc ret_pc.
   ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_4rounds_reg_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read Q0 s = word_join4 a b c d /\
         read Q1 s = word_join4 e f g h /\
         read Q2 s = word_join4 kw0 kw1 kw2 kw3)
    (\s. read PC s = word ret_pc /\
         read Q0 s =
           (let state = [a;b;c;d;e;f;g;h] in
            let s1 = sha256_compress_round kw0 (word 0) state in
            let s2 = sha256_compress_round kw1 (word 0) s1 in
            let s3 = sha256_compress_round kw2 (word 0) s2 in
            let s4 = sha256_compress_round kw3 (word 0) s3 in
            word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)) /\
         read Q1 s =
           (let state = [a;b;c;d;e;f;g;h] in
            let s1 = sha256_compress_round kw0 (word 0) state in
            let s2 = sha256_compress_round kw1 (word 0) s1 in
            let s3 = sha256_compress_round kw2 (word 0) s2 in
            let s4 = sha256_compress_round kw3 (word 0) s3 in
            word_join4 (EL 4 s4) (EL 5 s4) (EL 6 s4) (EL 7 s4)))
    (MAYCHANGE [PC] ,, MAYCHANGE [Q0; Q1; Q3] ,, MAYCHANGE [events])`,

  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;
              CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE]);;
