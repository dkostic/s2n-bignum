(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tiny register-only kernel exercising CRC32CX in a real proof context.     *)
(*                                                                           *)
(* The kernel `crc32c_step_reg` initialises an accumulator to 0xFFFFFFFF,    *)
(* feeds the 8-byte source operand X1 through one CRC32CX instruction, and  *)
(* returns the resulting 32-bit accumulator in W0. This validates the full  *)
(* Phase 0c -> Phase 4 stack (decode + ARM_OPERATION + CRC32CX_BRIDGE) on a *)
(* real ARM_STEPS_TAC simulation, before we move on to memory-touching       *)
(* proofs in Phase 6.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_bridge.ml";;

(**** print_literal_from_elf "arm/crc32/crc32c_step_reg.o";;
 ****)

let crc32c_step_reg_mc = define_assert_from_elf
 "crc32c_step_reg_mc" "arm/crc32/crc32c_step_reg.o"
[
  0x12800000;       (* arm_MOVN W0 (word 0) 0 *)
  0x9ac15c00;       (* arm_CRC32CX W0 W0 X1 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CRC32C_STEP_REG_EXEC = ARM_MK_EXEC_RULE crc32c_step_reg_mc;;

(* ------------------------------------------------------------------------- *)
(* Core correctness: PC starts at the function entry, ends just before the   *)
(* RET. W0 contains the CRC32C of the 8 little-endian source bytes of X1,   *)
(* zero-extended into X0.                                                   *)
(* ------------------------------------------------------------------------- *)

let CRC32C_STEP_REG_CORRECT = prove
 (`!v pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) crc32c_step_reg_mc /\
               read PC s = word pc /\
               read X1 s = v)
          (\s. read PC s = word(pc + 8) /\
               read X0 s =
                 word_zx (crc32c_bytes (word 0xFFFFFFFF)
                   [word_subword v (0,8); word_subword v (8,8);
                    word_subword v (16,8); word_subword v (24,8);
                    word_subword v (32,8); word_subword v (40,8);
                    word_subword v (48,8); word_subword v (56,8)]))
          (MAYCHANGE [PC; X0] ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC CRC32C_STEP_REG_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[CRC32CX_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper: leaf function, X30 holds returnaddress on entry,     *)
(* PC returns to returnaddress on exit. ABI MAYCHANGE.                      *)
(* ------------------------------------------------------------------------- *)

let CRC32C_STEP_REG_SUBROUTINE_CORRECT = prove
 (`!v pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) crc32c_step_reg_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               read X1 s = v)
          (\s. read PC s = returnaddress /\
               read X0 s =
                 word_zx (crc32c_bytes (word 0xFFFFFFFF)
                   [word_subword v (0,8); word_subword v (8,8);
                    word_subword v (16,8); word_subword v (24,8);
                    word_subword v (32,8); word_subword v (40,8);
                    word_subword v (48,8); word_subword v (56,8)]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC CRC32C_STEP_REG_EXEC CRC32C_STEP_REG_CORRECT);;
