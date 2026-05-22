(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 8-buffer single-iteration loop16 body: one full iteration of .Lxzf_loop16 *)
(* in crc32c_octo_zerofill_xor.S. This is exactly 8 copies of the Phase 6    *)
(* one-buffer (LDP+CRC+CRC+STP) slice — one per buffer/accumulator pair      *)
(* (X0,W8)..(X7,W15) — followed by `sub x19, x19, #16` to advance the        *)
(* remaining-byte counter. The cmp/b.ge that close the loop are NOT included *)
(* here; they belong to Phase 8's loop tactic.                               *)
(*                                                                           *)
(* This is Phase 7 of the crc32c_octo_zerofill_xor plan.                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_bridge.ml";;

(**** print_literal_from_elf "arm/crc32/crc32c_loop16_body.o";;
 ****)

let crc32c_loop16_body_mc = define_assert_from_elf
 "crc32c_loop16_body_mc" "arm/crc32/crc32c_loop16_body.o"
[
  0xa9404410;       (* arm_LDP X16 X17 X0 (Immediate_Offset (iword (&0))) *)
  0x9ad05d08;       (* arm_CRC32CX W8 W8 X16 *)
  0x9ad15d08;       (* arm_CRC32CX W8 W8 X17 *)
  0xa8817c1f;       (* arm_STP XZR XZR X0 (Postimmediate_Offset (iword (&16))) *)
  0xa9404430;       (* arm_LDP X16 X17 X1 (Immediate_Offset (iword (&0))) *)
  0x9ad05d29;       (* arm_CRC32CX W9 W9 X16 *)
  0x9ad15d29;       (* arm_CRC32CX W9 W9 X17 *)
  0xa8817c3f;       (* arm_STP XZR XZR X1 (Postimmediate_Offset (iword (&16))) *)
  0xa9404450;       (* arm_LDP X16 X17 X2 (Immediate_Offset (iword (&0))) *)
  0x9ad05d4a;       (* arm_CRC32CX W10 W10 X16 *)
  0x9ad15d4a;       (* arm_CRC32CX W10 W10 X17 *)
  0xa8817c5f;       (* arm_STP XZR XZR X2 (Postimmediate_Offset (iword (&16))) *)
  0xa9404470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&0))) *)
  0x9ad05d6b;       (* arm_CRC32CX W11 W11 X16 *)
  0x9ad15d6b;       (* arm_CRC32CX W11 W11 X17 *)
  0xa8817c7f;       (* arm_STP XZR XZR X3 (Postimmediate_Offset (iword (&16))) *)
  0xa9404490;       (* arm_LDP X16 X17 X4 (Immediate_Offset (iword (&0))) *)
  0x9ad05d8c;       (* arm_CRC32CX W12 W12 X16 *)
  0x9ad15d8c;       (* arm_CRC32CX W12 W12 X17 *)
  0xa8817c9f;       (* arm_STP XZR XZR X4 (Postimmediate_Offset (iword (&16))) *)
  0xa94044b0;       (* arm_LDP X16 X17 X5 (Immediate_Offset (iword (&0))) *)
  0x9ad05dad;       (* arm_CRC32CX W13 W13 X16 *)
  0x9ad15dad;       (* arm_CRC32CX W13 W13 X17 *)
  0xa8817cbf;       (* arm_STP XZR XZR X5 (Postimmediate_Offset (iword (&16))) *)
  0xa94044d0;       (* arm_LDP X16 X17 X6 (Immediate_Offset (iword (&0))) *)
  0x9ad05dce;       (* arm_CRC32CX W14 W14 X16 *)
  0x9ad15dce;       (* arm_CRC32CX W14 W14 X17 *)
  0xa8817cdf;       (* arm_STP XZR XZR X6 (Postimmediate_Offset (iword (&16))) *)
  0xa94044f0;       (* arm_LDP X16 X17 X7 (Immediate_Offset (iword (&0))) *)
  0x9ad05def;       (* arm_CRC32CX W15 W15 X16 *)
  0x9ad15def;       (* arm_CRC32CX W15 W15 X17 *)
  0xa8817cff;       (* arm_STP XZR XZR X7 (Postimmediate_Offset (iword (&16))) *)
  0xd1004273;       (* arm_SUB X19 X19 (rvalue (word 16)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CRC32C_LOOP16_BODY_EXEC = ARM_MK_EXEC_RULE crc32c_loop16_body_mc;;

(* ------------------------------------------------------------------------- *)
(* Helper: the 16-byte LE byte enumeration of two int64s, in order. The      *)
(* postcondition feeds the lo/hi pair of bytes into crc32c_bytes; this is    *)
(* exactly the pattern from Phase 6, repeated 8 times.                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Core correctness: starting at the first LDP, ending after the SUB         *)
(* (PC = pc + 132 = pc + 33*4). For each buffer/accumulator pair             *)
(* (X_n, W_{n+8}), the buffer pointer advances by 16, the accumulator        *)
(* gets folded with 16 LE bytes from the buffer, and the buffer's 16 bytes   *)
(* become zero. X19 decrements by 16.                                        *)
(* ------------------------------------------------------------------------- *)

let CRC32C_LOOP16_BODY_CORRECT = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7
    init0 init1 init2 init3 init4 init5 init6 init7
    m0_lo m0_hi m1_lo m1_hi m2_lo m2_hi m3_lo m3_hi
    m4_lo m4_hi m5_lo m5_hi m6_lo m6_hi m7_lo m7_hi
    len pc.
        PAIRWISE nonoverlapping
         [(word pc, LENGTH crc32c_loop16_body_mc);
          (a0,16); (a1,16); (a2,16); (a3,16);
          (a4,16); (a5,16); (a6,16); (a7,16)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) crc32c_loop16_body_mc /\
                  read PC s = word pc /\
                  read X0 s = a0 /\ read X1 s = a1 /\
                  read X2 s = a2 /\ read X3 s = a3 /\
                  read X4 s = a4 /\ read X5 s = a5 /\
                  read X6 s = a6 /\ read X7 s = a7 /\
                  read X8 s = word_zx (init0:int32) /\
                  read X9 s = word_zx (init1:int32) /\
                  read X10 s = word_zx (init2:int32) /\
                  read X11 s = word_zx (init3:int32) /\
                  read X12 s = word_zx (init4:int32) /\
                  read X13 s = word_zx (init5:int32) /\
                  read X14 s = word_zx (init6:int32) /\
                  read X15 s = word_zx (init7:int32) /\
                  read X19 s = len /\
                  read (memory :> bytes64 a0) s = m0_lo /\
                  read (memory :> bytes64 (word_add a0 (word 8))) s = m0_hi /\
                  read (memory :> bytes64 a1) s = m1_lo /\
                  read (memory :> bytes64 (word_add a1 (word 8))) s = m1_hi /\
                  read (memory :> bytes64 a2) s = m2_lo /\
                  read (memory :> bytes64 (word_add a2 (word 8))) s = m2_hi /\
                  read (memory :> bytes64 a3) s = m3_lo /\
                  read (memory :> bytes64 (word_add a3 (word 8))) s = m3_hi /\
                  read (memory :> bytes64 a4) s = m4_lo /\
                  read (memory :> bytes64 (word_add a4 (word 8))) s = m4_hi /\
                  read (memory :> bytes64 a5) s = m5_lo /\
                  read (memory :> bytes64 (word_add a5 (word 8))) s = m5_hi /\
                  read (memory :> bytes64 a6) s = m6_lo /\
                  read (memory :> bytes64 (word_add a6 (word 8))) s = m6_hi /\
                  read (memory :> bytes64 a7) s = m7_lo /\
                  read (memory :> bytes64 (word_add a7 (word 8))) s = m7_hi)
             (\s. read PC s = word(pc + 132) /\
                  read X0 s = word_add a0 (word 16) /\
                  read X1 s = word_add a1 (word 16) /\
                  read X2 s = word_add a2 (word 16) /\
                  read X3 s = word_add a3 (word 16) /\
                  read X4 s = word_add a4 (word 16) /\
                  read X5 s = word_add a5 (word 16) /\
                  read X6 s = word_add a6 (word 16) /\
                  read X7 s = word_add a7 (word 16) /\
                  read X8 s =
                    word_zx
                     (crc32c_bytes init0
                       [word_subword m0_lo (0,8); word_subword m0_lo (8,8);
                        word_subword m0_lo (16,8); word_subword m0_lo (24,8);
                        word_subword m0_lo (32,8); word_subword m0_lo (40,8);
                        word_subword m0_lo (48,8); word_subword m0_lo (56,8);
                        word_subword m0_hi (0,8); word_subword m0_hi (8,8);
                        word_subword m0_hi (16,8); word_subword m0_hi (24,8);
                        word_subword m0_hi (32,8); word_subword m0_hi (40,8);
                        word_subword m0_hi (48,8); word_subword m0_hi (56,8)]) /\
                  read X9 s =
                    word_zx
                     (crc32c_bytes init1
                       [word_subword m1_lo (0,8); word_subword m1_lo (8,8);
                        word_subword m1_lo (16,8); word_subword m1_lo (24,8);
                        word_subword m1_lo (32,8); word_subword m1_lo (40,8);
                        word_subword m1_lo (48,8); word_subword m1_lo (56,8);
                        word_subword m1_hi (0,8); word_subword m1_hi (8,8);
                        word_subword m1_hi (16,8); word_subword m1_hi (24,8);
                        word_subword m1_hi (32,8); word_subword m1_hi (40,8);
                        word_subword m1_hi (48,8); word_subword m1_hi (56,8)]) /\
                  read X10 s =
                    word_zx
                     (crc32c_bytes init2
                       [word_subword m2_lo (0,8); word_subword m2_lo (8,8);
                        word_subword m2_lo (16,8); word_subword m2_lo (24,8);
                        word_subword m2_lo (32,8); word_subword m2_lo (40,8);
                        word_subword m2_lo (48,8); word_subword m2_lo (56,8);
                        word_subword m2_hi (0,8); word_subword m2_hi (8,8);
                        word_subword m2_hi (16,8); word_subword m2_hi (24,8);
                        word_subword m2_hi (32,8); word_subword m2_hi (40,8);
                        word_subword m2_hi (48,8); word_subword m2_hi (56,8)]) /\
                  read X11 s =
                    word_zx
                     (crc32c_bytes init3
                       [word_subword m3_lo (0,8); word_subword m3_lo (8,8);
                        word_subword m3_lo (16,8); word_subword m3_lo (24,8);
                        word_subword m3_lo (32,8); word_subword m3_lo (40,8);
                        word_subword m3_lo (48,8); word_subword m3_lo (56,8);
                        word_subword m3_hi (0,8); word_subword m3_hi (8,8);
                        word_subword m3_hi (16,8); word_subword m3_hi (24,8);
                        word_subword m3_hi (32,8); word_subword m3_hi (40,8);
                        word_subword m3_hi (48,8); word_subword m3_hi (56,8)]) /\
                  read X12 s =
                    word_zx
                     (crc32c_bytes init4
                       [word_subword m4_lo (0,8); word_subword m4_lo (8,8);
                        word_subword m4_lo (16,8); word_subword m4_lo (24,8);
                        word_subword m4_lo (32,8); word_subword m4_lo (40,8);
                        word_subword m4_lo (48,8); word_subword m4_lo (56,8);
                        word_subword m4_hi (0,8); word_subword m4_hi (8,8);
                        word_subword m4_hi (16,8); word_subword m4_hi (24,8);
                        word_subword m4_hi (32,8); word_subword m4_hi (40,8);
                        word_subword m4_hi (48,8); word_subword m4_hi (56,8)]) /\
                  read X13 s =
                    word_zx
                     (crc32c_bytes init5
                       [word_subword m5_lo (0,8); word_subword m5_lo (8,8);
                        word_subword m5_lo (16,8); word_subword m5_lo (24,8);
                        word_subword m5_lo (32,8); word_subword m5_lo (40,8);
                        word_subword m5_lo (48,8); word_subword m5_lo (56,8);
                        word_subword m5_hi (0,8); word_subword m5_hi (8,8);
                        word_subword m5_hi (16,8); word_subword m5_hi (24,8);
                        word_subword m5_hi (32,8); word_subword m5_hi (40,8);
                        word_subword m5_hi (48,8); word_subword m5_hi (56,8)]) /\
                  read X14 s =
                    word_zx
                     (crc32c_bytes init6
                       [word_subword m6_lo (0,8); word_subword m6_lo (8,8);
                        word_subword m6_lo (16,8); word_subword m6_lo (24,8);
                        word_subword m6_lo (32,8); word_subword m6_lo (40,8);
                        word_subword m6_lo (48,8); word_subword m6_lo (56,8);
                        word_subword m6_hi (0,8); word_subword m6_hi (8,8);
                        word_subword m6_hi (16,8); word_subword m6_hi (24,8);
                        word_subword m6_hi (32,8); word_subword m6_hi (40,8);
                        word_subword m6_hi (48,8); word_subword m6_hi (56,8)]) /\
                  read X15 s =
                    word_zx
                     (crc32c_bytes init7
                       [word_subword m7_lo (0,8); word_subword m7_lo (8,8);
                        word_subword m7_lo (16,8); word_subword m7_lo (24,8);
                        word_subword m7_lo (32,8); word_subword m7_lo (40,8);
                        word_subword m7_lo (48,8); word_subword m7_lo (56,8);
                        word_subword m7_hi (0,8); word_subword m7_hi (8,8);
                        word_subword m7_hi (16,8); word_subword m7_hi (24,8);
                        word_subword m7_hi (32,8); word_subword m7_hi (40,8);
                        word_subword m7_hi (48,8); word_subword m7_hi (56,8)]) /\
                  read X19 s = word_sub len (word 16) /\
                  read (memory :> bytes64 a0) s = word 0 /\
                  read (memory :> bytes64 (word_add a0 (word 8))) s = word 0 /\
                  read (memory :> bytes64 a1) s = word 0 /\
                  read (memory :> bytes64 (word_add a1 (word 8))) s = word 0 /\
                  read (memory :> bytes64 a2) s = word 0 /\
                  read (memory :> bytes64 (word_add a2 (word 8))) s = word 0 /\
                  read (memory :> bytes64 a3) s = word 0 /\
                  read (memory :> bytes64 (word_add a3 (word 8))) s = word 0 /\
                  read (memory :> bytes64 a4) s = word 0 /\
                  read (memory :> bytes64 (word_add a4 (word 8))) s = word 0 /\
                  read (memory :> bytes64 a5) s = word 0 /\
                  read (memory :> bytes64 (word_add a5 (word 8))) s = word 0 /\
                  read (memory :> bytes64 a6) s = word 0 /\
                  read (memory :> bytes64 (word_add a6 (word 8))) s = word 0 /\
                  read (memory :> bytes64 a7) s = word 0 /\
                  read (memory :> bytes64 (word_add a7 (word 8))) s = word 0)
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7;
                      X8; X9; X10; X11; X12; X13; X14; X15;
                      X16; X17; X19] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a0, 16); memory :> bytes(a1, 16);
                      memory :> bytes(a2, 16); memory :> bytes(a3, 16);
                      memory :> bytes(a4, 16); memory :> bytes(a5, 16);
                      memory :> bytes(a6, 16); memory :> bytes(a7, 16)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fst CRC32C_LOOP16_BODY_EXEC]) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC CRC32C_LOOP16_BODY_EXEC (1--33) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                  CRC32CX_BRIDGE; GSYM crc32c_bytes_APPEND; APPEND]);;
