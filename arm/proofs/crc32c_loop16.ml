(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multi-iteration loop16 kernel for crc32c_octo_zerofill_xor.               *)
(* Wraps the Phase 7 single-iteration body in ENSURES_WHILE_UP_TAC.          *)
(*                                                                           *)
(* This is Phase 8 of the crc32c_octo_zerofill_xor plan.                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_bridge.ml";;
needs "arm/proofs/crc32c_loop16_body.ml";;

(**** print_literal_from_elf "arm/crc32/crc32c_loop16.o";;
 ****)

let crc32c_loop16_mc = define_assert_from_elf
 "crc32c_loop16_mc" "arm/crc32/crc32c_loop16.o"
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
  0xf100427f;       (* arm_CMP X19 (rvalue (word 16)) *)
  0x54fffbca;       (* arm_BGE (word 2097044) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CRC32C_LOOP16_EXEC = ARM_MK_EXEC_RULE crc32c_loop16_mc;;
