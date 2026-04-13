(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 4 rounds of SHA-256 compression with state load/store from memory.        *)
(*                                                                           *)
(* Extends sha256_4rounds_reg by adding LDR/STR Q instructions to load the   *)
(* 8-word SHA-256 state from memory and write back the updated state.        *)
(* The pre-added round keys (K[t]+W[t]) are still passed in register Q2.     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code extracted from the assembled .o file.                        *)
(*   0: 3dc00000  ldr q0, [x0]                                              *)
(*   4: 3dc00401  ldr q1, [x0, #16]                                         *)
(*   8: 4ea01c03  mov v3.16b, v0.16b                                        *)
(*   c: 5e024020  sha256h q0, q1, v2.4s                                     *)
(*  10: 5e025061  sha256h2 q1, q3, v2.4s                                    *)
(*  14: 3d800000  str q0, [x0]                                              *)
(*  18: 3d800401  str q1, [x0, #16]                                         *)
(*  1c: d65f03c0  ret                                                        *)
(* ------------------------------------------------------------------------- *)

let sha256_4rounds_mem_mc = define_assert_from_elf "sha256_4rounds_mem_mc"
  (file_on_path !load_path "arm/sha2/sha256_4rounds_mem.o")
  [0x3dc00000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 0)) *)
   0x3dc00401;       (* arm_LDR Q1 X0 (Immediate_Offset (word 16)) *)
   0x4ea01c03;       (* arm_MOV_VEC Q3 Q0 128 *)
   0x5e024020;       (* arm_SHA256H Q0 Q1 Q2 *)
   0x5e025061;       (* arm_SHA256H2 Q1 Q3 Q2 *)
   0x3d800000;       (* arm_STR Q0 X0 (Immediate_Offset (word 0)) *)
   0x3d800401;       (* arm_STR Q1 X0 (Immediate_Offset (word 16)) *)
   0xd65f03c0        (* arm_RET X30 *)];;

let EXEC = ARM_MK_EXEC_RULE sha256_4rounds_mem_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness: loads state from memory, computes 4 rounds, stores back.     *)
(*                                                                           *)
(* Precondition:                                                             *)
(*   x0 = state_ptr (pointer to 8 x int32 state in memory)                  *)
(*   Q2 = word_join4 kw0 kw1 kw2 kw3 (pre-added K[t]+W[t])                 *)
(*   memory at state_ptr: word_join4 a b c d (ABCD, 128 bits)               *)
(*   memory at state_ptr+16: word_join4 e f g h (EFGH, 128 bits)            *)
(*   nonoverlapping: state buffer does not overlap code                      *)
(*                                                                           *)
(* Postcondition:                                                            *)
(*   memory at state_ptr: ABCD half of state after 4 compression rounds      *)
(*   memory at state_ptr+16: EFGH half of state after 4 compression rounds   *)
(* ------------------------------------------------------------------------- *)

let SHA256_4ROUNDS_MEM_CORRECT = prove(
 `!(a:int32) (b:int32) (c:int32) (d:int32) (e:int32) (f:int32)
   (g:int32) (h:int32) (kw0:int32) (kw1:int32) (kw2:int32) (kw3:int32)
   state_ptr pc ret_pc.
   nonoverlapping (state_ptr, 32) (word pc, 32)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_4rounds_mem_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X0 s = state_ptr /\
         read Q2 s = word_join4 kw0 kw1 kw2 kw3 /\
         read (memory :> bytes128 state_ptr) s =
           word_join4 a b c d /\
         read (memory :> bytes128 (word_add state_ptr (word 16))) s =
           word_join4 e f g h)
    (\s. read PC s = word ret_pc /\
         read (memory :> bytes128 state_ptr) s =
           (let state = [a;b;c;d;e;f;g;h] in
            let s1 = sha256_compress_round kw0 (word 0) state in
            let s2 = sha256_compress_round kw1 (word 0) s1 in
            let s3 = sha256_compress_round kw2 (word 0) s2 in
            let s4 = sha256_compress_round kw3 (word 0) s3 in
            word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)) /\
         read (memory :> bytes128 (word_add state_ptr (word 16))) s =
           (let state = [a;b;c;d;e;f;g;h] in
            let s1 = sha256_compress_round kw0 (word 0) state in
            let s2 = sha256_compress_round kw1 (word 0) s1 in
            let s3 = sha256_compress_round kw2 (word 0) s2 in
            let s4 = sha256_compress_round kw3 (word 0) s3 in
            word_join4 (EL 4 s4) (EL 5 s4) (EL 6 s4) (EL 7 s4)))
    (MAYCHANGE [PC] ,,
     MAYCHANGE [Q0; Q1; Q3] ,,
     MAYCHANGE [memory :> bytes(state_ptr, 32)] ,,
     MAYCHANGE [events])`,

  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;
              CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE]);;
