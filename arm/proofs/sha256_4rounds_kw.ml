(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 4 rounds of SHA-256 with K-constant loading from memory + ADD V.4S        *)
(* pre-addition of round keys and message schedule words.                    *)
(*                                                                           *)
(* Demonstrates the full pipeline: load K constants from memory, vector-add  *)
(* K+W, then SHA256H/SHA256H2 for 4 compression rounds. The postcondition   *)
(* uses sha256_compress_round with separate K and W arguments, connected to  *)
(* the hardware via SHA256H_BRIDGE + SHA256_COMPRESS_ROUND_PREADD.           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code.                                                             *)
(*   0: 3dc00024  ldr q4, [x1]              -- Load K[0..3]                 *)
(*   4: 4ea58482  add v2.4s, v4.4s, v5.4s   -- Q2 = K + W                  *)
(*   8: 4ea01c03  mov v3.16b, v0.16b        -- Save ABCD                   *)
(*   c: 5e024020  sha256h q0, q1, v2.4s     -- New ABCD                    *)
(*  10: 5e025061  sha256h2 q1, q3, v2.4s    -- New EFGH                    *)
(*  14: d65f03c0  ret                                                        *)
(* ------------------------------------------------------------------------- *)

let sha256_4rounds_kw_mc = define_assert_from_elf "sha256_4rounds_kw_mc"
  (file_on_path !load_path "arm/sha2/sha256_4rounds_kw.o")
  [0x3dc00024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 0)) *)
   0x4ea58482;       (* arm_ADD_VEC Q2 Q4 Q5 32 128 *)
   0x4ea01c03;       (* arm_MOV_VEC Q3 Q0 128 *)
   0x5e024020;       (* arm_SHA256H Q0 Q1 Q2 *)
   0x5e025061;       (* arm_SHA256H2 Q1 Q3 Q2 *)
   0xd65f03c0        (* arm_RET X30 *)];;

let EXEC = ARM_MK_EXEC_RULE sha256_4rounds_kw_mc;;

(* WORD_JOIN_4x32, SHA256_COMPRESS_ROUND_PREADD are in sha256_bridge.ml *)

(* ------------------------------------------------------------------------- *)
(* Correctness: loads K constants, pre-adds K+W, computes 4 SHA-256 rounds.  *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q0 = state ABCD, Q1 = state EFGH                                       *)
(*   Q5 = message words W[0..3]                                              *)
(*   x1 = pointer to K constants (16 bytes in memory)                        *)
(*                                                                           *)
(* Postcondition uses sha256_compress_round k_i w_i with separate K and W.   *)
(* The proof connects: LDR → ADD V.4S → SHA256H bridge → pre-add equiv.     *)
(* ------------------------------------------------------------------------- *)

let SHA256_4ROUNDS_KW_CORRECT = prove(
 `!(a:int32) (b:int32) (c:int32) (d:int32) (e:int32) (f:int32)
   (g:int32) (h:int32) (k0:int32) (k1:int32) (k2:int32) (k3:int32)
   (w0:int32) (w1:int32) (w2:int32) (w3:int32) kptr pc ret_pc.
   nonoverlapping (kptr, 16) (word pc, 24)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_4rounds_kw_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X1 s = kptr /\
         read Q0 s = word_join4 a b c d /\
         read Q1 s = word_join4 e f g h /\
         read Q5 s = word_join4 w0 w1 w2 w3 /\
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
            word_join4 (EL 4 s4) (EL 5 s4) (EL 6 s4) (EL 7 s4)))
    (MAYCHANGE [PC] ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,,
     MAYCHANGE [events])`,

  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-2: LDR K constants + ADD V.4S pre-addition *)
  ARM_STEPS_TAC EXEC (1--2) THEN

  (* Simplify the ADD V.4S result:
     word_subword(word_join4 k0 k1 k2 k3, (n,32)) -> k_n
     then re-nest word_joins into word_join4 *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32]) THEN

  (* Steps 3-6: MOV + SHA256H + SHA256H2 + RET *)
  ARM_STEPS_TAC EXEC (3--6) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  (* Connect to spec:
     1. Expand let bindings in postcondition
     2. Apply bridging lemmas (sha256h -> compress_round (word_add k w) (word 0))
     3. Simplify pre-added form to separate K, W *)
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;
              CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD]);;
