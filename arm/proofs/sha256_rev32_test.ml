(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* REV32 byte-swapping test for SHA-256 message data loading.                *)
(*                                                                           *)
(* Proves that LDR Q + REV32.16B produces word_bytereverse of each 32-bit    *)
(* lane. SHA-256 operates on big-endian 32-bit words, but ARM memory is      *)
(* little-endian, so REV32 converts between the two byte orders.             *)
(*                                                                           *)
(* IMPORTANT: Requires the s2n-arm checkpoint built from the s2n-bignum      *)
(* commit that adds REV32 VEC to the ISA model (683cf88a or later).          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code.                                                             *)
(*   0: 3dc00004  ldr q4, [x0]                                              *)
(*   4: 6e200884  rev32 v4.16b, v4.16b                                      *)
(*   8: d65f03c0  ret                                                        *)
(* ------------------------------------------------------------------------- *)

let sha256_rev32_test_mc = define_assert_from_elf "sha256_rev32_test_mc"
  (file_on_path !load_path "arm/sha2/sha256_rev32_test.o")
  [0x3dc00004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 0)) *)
   0x6e200884;       (* arm_REV32_VEC Q4 Q4 8 128 *)
   0xd65f03c0        (* arm_RET X30 *)];;

let EXEC = ARM_MK_EXEC_RULE sha256_rev32_test_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness: LDR + REV32 produces byte-reversed 32-bit lanes.             *)
(*                                                                           *)
(* Input: 4 little-endian int32 words packed as word_join4 in memory.        *)
(* Output: Q4 = word_join4 of byte-reversed words.                           *)
(*                                                                           *)
(* The REV32 expansion produces a huge intermediate term (~1200 lines).      *)
(* BITBLAST closes the proof at the bit level.                               *)
(* ------------------------------------------------------------------------- *)

let SHA256_REV32_TEST_CORRECT = prove(
 `!(w0:int32) (w1:int32) (w2:int32) (w3:int32) dptr pc ret_pc.
   nonoverlapping (dptr, 16) (word pc, 12)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_rev32_test_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X0 s = dptr /\
         read (memory :> bytes128 dptr) s = word_join4 w0 w1 w2 w3)
    (\s. read PC s = word ret_pc /\
         read Q4 s = word_join4 (word_bytereverse w0) (word_bytereverse w1)
                                (word_bytereverse w2) (word_bytereverse w3))
    (MAYCHANGE [PC] ,, MAYCHANGE [Q4] ,, MAYCHANGE [events])`,

  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[word_join4] THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;
