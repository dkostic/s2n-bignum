(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* One-buffer LDP+CRC+CRC+STP block-of-16 unit. This is exactly one slice of *)
(* the main loop body in crc32c_octo_zerofill_xor.S (.Lxzf_loop16); the      *)
(* 8-buffer body is 8 such slices in sequence (Phase 6 of the                *)
(* crc32c_octo_zerofill_xor plan). It validates: 128-bit memory load via     *)
(* LDP X (split into two int64 reads), two chained CRC32CX bridges, 128-bit  *)
(* zerofill via STP XZR (split into two int64 writes), post-immediate        *)
(* writeback, and the crc32c_bytes_APPEND fusion of two 8-byte folds into    *)
(* one 16-byte fold.                                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_bridge.ml";;

(**** print_literal_from_elf "arm/crc32/crc32c_block16_one.o";;
 ****)

let crc32c_block16_one_mc = define_assert_from_elf
 "crc32c_block16_one_mc" "arm/crc32/crc32c_block16_one.o"
[
  0xa9404410;       (* arm_LDP X16 X17 X0 (Immediate_Offset (iword (&0))) *)
  0x9ad05d08;       (* arm_CRC32CX W8 W8 X16 *)
  0x9ad15d08;       (* arm_CRC32CX W8 W8 X17 *)
  0xa8817c1f;       (* arm_STP XZR XZR X0 (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CRC32C_BLOCK16_ONE_EXEC = ARM_MK_EXEC_RULE crc32c_block16_one_mc;;

(* ------------------------------------------------------------------------- *)
(* Core correctness: PC starts at the function entry, ends just before the   *)
(* RET. Starting with X0 = a, X8 holding init (zero-extended) and 16 bytes   *)
(* of memory at a equal to (m_lo, m_hi), end with:                           *)
(*   - X0 advanced by 16,                                                    *)
(*   - X8 = crc32c_bytes init [LE bytes of m_lo ++ LE bytes of m_hi],        *)
(*   - 16 bytes at original a are zero.                                      *)
(* ------------------------------------------------------------------------- *)

let CRC32C_BLOCK16_ONE_CORRECT = prove
 (`!a init m_lo m_hi pc.
        nonoverlapping (word pc, LENGTH crc32c_block16_one_mc) (a, 16)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) crc32c_block16_one_mc /\
                  read PC s = word pc /\
                  read X0 s = a /\
                  read X8 s = word_zx (init:int32) /\
                  read (memory :> bytes64 a) s = m_lo /\
                  read (memory :> bytes64 (word_add a (word 8))) s = m_hi)
             (\s. read PC s = word(pc + 16) /\
                  read X0 s = word_add a (word 16) /\
                  read X8 s =
                    word_zx
                     (crc32c_bytes init
                       [word_subword m_lo (0,8); word_subword m_lo (8,8);
                        word_subword m_lo (16,8); word_subword m_lo (24,8);
                        word_subword m_lo (32,8); word_subword m_lo (40,8);
                        word_subword m_lo (48,8); word_subword m_lo (56,8);
                        word_subword m_hi (0,8); word_subword m_hi (8,8);
                        word_subword m_hi (16,8); word_subword m_hi (24,8);
                        word_subword m_hi (32,8); word_subword m_hi (40,8);
                        word_subword m_hi (48,8); word_subword m_hi (56,8)]) /\
                  read (memory :> bytes64 a) s = word 0 /\
                  read (memory :> bytes64 (word_add a (word 8))) s = word 0)
          (MAYCHANGE [PC; X0; X8; X16; X17] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a, 16)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fst CRC32C_BLOCK16_ONE_EXEC]) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC CRC32C_BLOCK16_ONE_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                  CRC32CX_BRIDGE; GSYM crc32c_bytes_APPEND; APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper: leaf function, X30 holds returnaddress on entry,     *)
(* PC returns to returnaddress on exit. ABI MAYCHANGE.                      *)
(* ------------------------------------------------------------------------- *)

let CRC32C_BLOCK16_ONE_SUBROUTINE_CORRECT = prove
 (`!a init m_lo m_hi pc returnaddress.
        nonoverlapping (word pc, LENGTH crc32c_block16_one_mc) (a, 16)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) crc32c_block16_one_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  read X0 s = a /\
                  read X8 s = word_zx (init:int32) /\
                  read (memory :> bytes64 a) s = m_lo /\
                  read (memory :> bytes64 (word_add a (word 8))) s = m_hi)
             (\s. read PC s = returnaddress /\
                  read X0 s = word_add a (word 16) /\
                  read X8 s =
                    word_zx
                     (crc32c_bytes init
                       [word_subword m_lo (0,8); word_subword m_lo (8,8);
                        word_subword m_lo (16,8); word_subword m_lo (24,8);
                        word_subword m_lo (32,8); word_subword m_lo (40,8);
                        word_subword m_lo (48,8); word_subword m_lo (56,8);
                        word_subword m_hi (0,8); word_subword m_hi (8,8);
                        word_subword m_hi (16,8); word_subword m_hi (24,8);
                        word_subword m_hi (32,8); word_subword m_hi (40,8);
                        word_subword m_hi (48,8); word_subword m_hi (56,8)]) /\
                  read (memory :> bytes64 a) s = word 0 /\
                  read (memory :> bytes64 (word_add a (word 8))) s = word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a, 16)])`,
  REWRITE_TAC[fst CRC32C_BLOCK16_ONE_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC CRC32C_BLOCK16_ONE_EXEC
    (REWRITE_RULE[fst CRC32C_BLOCK16_ONE_EXEC] CRC32C_BLOCK16_ONE_CORRECT));;
