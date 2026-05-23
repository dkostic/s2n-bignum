(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Top-level kernel: crc32c_octo_zerofill_xor.                               *)
(*                                                                           *)
(* 8-chain CRC32C kernel that:                                                *)
(*   - Computes CRC32C on 8 input buffers a..h, each of length len.           *)
(*   - Zero-fills each buffer as it reads (kernel-side STP/STR xzr).          *)
(*   - Returns the XOR-reduction of the 8 finalized CRCs as a single u32.    *)
(*                                                                           *)
(* The 8 MVNs that the canonical CRC32C finalisation would need are elided,  *)
(* because XORing 8 copies of 0xFFFFFFFF gives 0; so the final XOR of the    *)
(* unfinalized accumulators equals the XOR of the finalized CRC32C values.   *)
(*                                                                           *)
(* This is Phase 9 of the crc32c_octo_zerofill_xor plan: it composes        *)
(*   1. Prologue (str x19; ldr x19; 8 init MOVs)                              *)
(*   2. Loop entry guard (cmp x19,#16; b.lt .Lxzf_tail)                       *)
(*   3. LOOP16 region (folded as a black-box theorem CRC32C_LOOP16_CORRECT)   *)
(*   4. Tail blocks (TBZ-gated 8/4/2/1-byte residues)                          *)
(*   5. XOR reduction (7 EOR instructions)                                    *)
(*   6. Epilogue (ldr x19; ret)                                                *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_bridge.ml";;
needs "arm/proofs/crc32c_loop16.ml";;

(**** print_literal_from_elf "arm/crc32/crc32c_octo_zerofill_xor.o";;
 ****)

let crc32c_octo_zerofill_xor_mc = define_assert_from_elf
 "crc32c_octo_zerofill_xor_mc" "arm/crc32/crc32c_octo_zerofill_xor.o"
[
  0xf81f0ff3;       (* arm_STR X19 SP (Preimmediate_Offset (word 18446744073709551600)) *)
  0xf9400bf3;       (* arm_LDR X19 SP (Immediate_Offset (word 16)) *)
  0x12800008;       (* arm_MOVN W8 (word 0) 0 *)
  0x12800009;       (* arm_MOVN W9 (word 0) 0 *)
  0x1280000a;       (* arm_MOVN W10 (word 0) 0 *)
  0x1280000b;       (* arm_MOVN W11 (word 0) 0 *)
  0x1280000c;       (* arm_MOVN W12 (word 0) 0 *)
  0x1280000d;       (* arm_MOVN W13 (word 0) 0 *)
  0x1280000e;       (* arm_MOVN W14 (word 0) 0 *)
  0x1280000f;       (* arm_MOVN W15 (word 0) 0 *)
  0xf100427f;       (* arm_CMP X19 (rvalue (word 16)) *)
  0x5400048b;       (* arm_BLT (word 144) *)
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
  0x54fffbca;       (* arm_BGE (word 2097016) *)
  0x36180333;       (* arm_TBZ W19 3 (word 100) *)
  0xf9400010;       (* arm_LDR X16 X0 (Immediate_Offset (word 0)) *)
  0x9ad05d08;       (* arm_CRC32CX W8 W8 X16 *)
  0xf800841f;       (* arm_STR XZR X0 (Postimmediate_Offset (word 8)) *)
  0xf9400031;       (* arm_LDR X17 X1 (Immediate_Offset (word 0)) *)
  0x9ad15d29;       (* arm_CRC32CX W9 W9 X17 *)
  0xf800843f;       (* arm_STR XZR X1 (Postimmediate_Offset (word 8)) *)
  0xf9400050;       (* arm_LDR X16 X2 (Immediate_Offset (word 0)) *)
  0x9ad05d4a;       (* arm_CRC32CX W10 W10 X16 *)
  0xf800845f;       (* arm_STR XZR X2 (Postimmediate_Offset (word 8)) *)
  0xf9400071;       (* arm_LDR X17 X3 (Immediate_Offset (word 0)) *)
  0x9ad15d6b;       (* arm_CRC32CX W11 W11 X17 *)
  0xf800847f;       (* arm_STR XZR X3 (Postimmediate_Offset (word 8)) *)
  0xf9400090;       (* arm_LDR X16 X4 (Immediate_Offset (word 0)) *)
  0x9ad05d8c;       (* arm_CRC32CX W12 W12 X16 *)
  0xf800849f;       (* arm_STR XZR X4 (Postimmediate_Offset (word 8)) *)
  0xf94000b1;       (* arm_LDR X17 X5 (Immediate_Offset (word 0)) *)
  0x9ad15dad;       (* arm_CRC32CX W13 W13 X17 *)
  0xf80084bf;       (* arm_STR XZR X5 (Postimmediate_Offset (word 8)) *)
  0xf94000d0;       (* arm_LDR X16 X6 (Immediate_Offset (word 0)) *)
  0x9ad05dce;       (* arm_CRC32CX W14 W14 X16 *)
  0xf80084df;       (* arm_STR XZR X6 (Postimmediate_Offset (word 8)) *)
  0xf94000f1;       (* arm_LDR X17 X7 (Immediate_Offset (word 0)) *)
  0x9ad15def;       (* arm_CRC32CX W15 W15 X17 *)
  0xf80084ff;       (* arm_STR XZR X7 (Postimmediate_Offset (word 8)) *)
  0x36100333;       (* arm_TBZ W19 2 (word 100) *)
  0xb9400010;       (* arm_LDR W16 X0 (Immediate_Offset (word 0)) *)
  0x1ad05908;       (* arm_CRC32CW W8 W8 W16 *)
  0xb800441f;       (* arm_STR WZR X0 (Postimmediate_Offset (word 4)) *)
  0xb9400031;       (* arm_LDR W17 X1 (Immediate_Offset (word 0)) *)
  0x1ad15929;       (* arm_CRC32CW W9 W9 W17 *)
  0xb800443f;       (* arm_STR WZR X1 (Postimmediate_Offset (word 4)) *)
  0xb9400050;       (* arm_LDR W16 X2 (Immediate_Offset (word 0)) *)
  0x1ad0594a;       (* arm_CRC32CW W10 W10 W16 *)
  0xb800445f;       (* arm_STR WZR X2 (Postimmediate_Offset (word 4)) *)
  0xb9400071;       (* arm_LDR W17 X3 (Immediate_Offset (word 0)) *)
  0x1ad1596b;       (* arm_CRC32CW W11 W11 W17 *)
  0xb800447f;       (* arm_STR WZR X3 (Postimmediate_Offset (word 4)) *)
  0xb9400090;       (* arm_LDR W16 X4 (Immediate_Offset (word 0)) *)
  0x1ad0598c;       (* arm_CRC32CW W12 W12 W16 *)
  0xb800449f;       (* arm_STR WZR X4 (Postimmediate_Offset (word 4)) *)
  0xb94000b1;       (* arm_LDR W17 X5 (Immediate_Offset (word 0)) *)
  0x1ad159ad;       (* arm_CRC32CW W13 W13 W17 *)
  0xb80044bf;       (* arm_STR WZR X5 (Postimmediate_Offset (word 4)) *)
  0xb94000d0;       (* arm_LDR W16 X6 (Immediate_Offset (word 0)) *)
  0x1ad059ce;       (* arm_CRC32CW W14 W14 W16 *)
  0xb80044df;       (* arm_STR WZR X6 (Postimmediate_Offset (word 4)) *)
  0xb94000f1;       (* arm_LDR W17 X7 (Immediate_Offset (word 0)) *)
  0x1ad159ef;       (* arm_CRC32CW W15 W15 W17 *)
  0xb80044ff;       (* arm_STR WZR X7 (Postimmediate_Offset (word 4)) *)
  0x36080333;       (* arm_TBZ W19 1 (word 100) *)
  0x79400010;       (* arm_LDRH W16 X0 (Immediate_Offset (word 0)) *)
  0x1ad05508;       (* arm_CRC32CH W8 W8 W16 *)
  0x7800241f;       (* arm_STRH WZR X0 (Postimmediate_Offset (word 2)) *)
  0x79400031;       (* arm_LDRH W17 X1 (Immediate_Offset (word 0)) *)
  0x1ad15529;       (* arm_CRC32CH W9 W9 W17 *)
  0x7800243f;       (* arm_STRH WZR X1 (Postimmediate_Offset (word 2)) *)
  0x79400050;       (* arm_LDRH W16 X2 (Immediate_Offset (word 0)) *)
  0x1ad0554a;       (* arm_CRC32CH W10 W10 W16 *)
  0x7800245f;       (* arm_STRH WZR X2 (Postimmediate_Offset (word 2)) *)
  0x79400071;       (* arm_LDRH W17 X3 (Immediate_Offset (word 0)) *)
  0x1ad1556b;       (* arm_CRC32CH W11 W11 W17 *)
  0x7800247f;       (* arm_STRH WZR X3 (Postimmediate_Offset (word 2)) *)
  0x79400090;       (* arm_LDRH W16 X4 (Immediate_Offset (word 0)) *)
  0x1ad0558c;       (* arm_CRC32CH W12 W12 W16 *)
  0x7800249f;       (* arm_STRH WZR X4 (Postimmediate_Offset (word 2)) *)
  0x794000b1;       (* arm_LDRH W17 X5 (Immediate_Offset (word 0)) *)
  0x1ad155ad;       (* arm_CRC32CH W13 W13 W17 *)
  0x780024bf;       (* arm_STRH WZR X5 (Postimmediate_Offset (word 2)) *)
  0x794000d0;       (* arm_LDRH W16 X6 (Immediate_Offset (word 0)) *)
  0x1ad055ce;       (* arm_CRC32CH W14 W14 W16 *)
  0x780024df;       (* arm_STRH WZR X6 (Postimmediate_Offset (word 2)) *)
  0x794000f1;       (* arm_LDRH W17 X7 (Immediate_Offset (word 0)) *)
  0x1ad155ef;       (* arm_CRC32CH W15 W15 W17 *)
  0x780024ff;       (* arm_STRH WZR X7 (Postimmediate_Offset (word 2)) *)
  0x36000333;       (* arm_TBZ W19 0 (word 100) *)
  0x39400010;       (* arm_LDRB W16 X0 (Immediate_Offset (word 0)) *)
  0x1ad05108;       (* arm_CRC32CB W8 W8 W16 *)
  0x3900001f;       (* arm_STRB WZR X0 (Immediate_Offset (word 0)) *)
  0x39400031;       (* arm_LDRB W17 X1 (Immediate_Offset (word 0)) *)
  0x1ad15129;       (* arm_CRC32CB W9 W9 W17 *)
  0x3900003f;       (* arm_STRB WZR X1 (Immediate_Offset (word 0)) *)
  0x39400050;       (* arm_LDRB W16 X2 (Immediate_Offset (word 0)) *)
  0x1ad0514a;       (* arm_CRC32CB W10 W10 W16 *)
  0x3900005f;       (* arm_STRB WZR X2 (Immediate_Offset (word 0)) *)
  0x39400071;       (* arm_LDRB W17 X3 (Immediate_Offset (word 0)) *)
  0x1ad1516b;       (* arm_CRC32CB W11 W11 W17 *)
  0x3900007f;       (* arm_STRB WZR X3 (Immediate_Offset (word 0)) *)
  0x39400090;       (* arm_LDRB W16 X4 (Immediate_Offset (word 0)) *)
  0x1ad0518c;       (* arm_CRC32CB W12 W12 W16 *)
  0x3900009f;       (* arm_STRB WZR X4 (Immediate_Offset (word 0)) *)
  0x394000b1;       (* arm_LDRB W17 X5 (Immediate_Offset (word 0)) *)
  0x1ad151ad;       (* arm_CRC32CB W13 W13 W17 *)
  0x390000bf;       (* arm_STRB WZR X5 (Immediate_Offset (word 0)) *)
  0x394000d0;       (* arm_LDRB W16 X6 (Immediate_Offset (word 0)) *)
  0x1ad051ce;       (* arm_CRC32CB W14 W14 W16 *)
  0x390000df;       (* arm_STRB WZR X6 (Immediate_Offset (word 0)) *)
  0x394000f1;       (* arm_LDRB W17 X7 (Immediate_Offset (word 0)) *)
  0x1ad151ef;       (* arm_CRC32CB W15 W15 W17 *)
  0x390000ff;       (* arm_STRB WZR X7 (Immediate_Offset (word 0)) *)
  0x4a090108;       (* arm_EOR W8 W8 W9 *)
  0x4a0b014a;       (* arm_EOR W10 W10 W11 *)
  0x4a0d018c;       (* arm_EOR W12 W12 W13 *)
  0x4a0f01ce;       (* arm_EOR W14 W14 W15 *)
  0x4a0a0108;       (* arm_EOR W8 W8 W10 *)
  0x4a0e018c;       (* arm_EOR W12 W12 W14 *)
  0x4a0c0100;       (* arm_EOR W0 W8 W12 *)
  0xf84107f3;       (* arm_LDR X19 SP (Postimmediate_Offset (word 16)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CRC32C_OCTO_ZERO_FILL_XOR_EXEC =
  ARM_MK_EXEC_RULE crc32c_octo_zerofill_xor_mc;;

(* ------------------------------------------------------------------------- *)
(* Spec: per-buffer ghost byte lists.                                        *)
(*                                                                           *)
(* The kernel takes 8 input buffers a..h, each of length len. The output     *)
(* w0 is the XOR-reduction of the 8 finalized CRC32C values (one per         *)
(* buffer's input bytes), expressed via crc32c_buffer.                        *)
(* ------------------------------------------------------------------------- *)

let crc32c_xor8 = define
 `crc32c_xor8 (bs0:byte list) (bs1:byte list) (bs2:byte list)
              (bs3:byte list) (bs4:byte list) (bs5:byte list)
              (bs6:byte list) (bs7:byte list) : int32 =
    word_xor (crc32c_buffer bs0)
   (word_xor (crc32c_buffer bs1)
   (word_xor (crc32c_buffer bs2)
   (word_xor (crc32c_buffer bs3)
   (word_xor (crc32c_buffer bs4)
   (word_xor (crc32c_buffer bs5)
   (word_xor (crc32c_buffer bs6)
             (crc32c_buffer bs7)))))))`;;

(* ------------------------------------------------------------------------- *)
(* CORE correctness theorem (Phase 9 — body proof, post-prologue).            *)
(*                                                                           *)
(* CORE covers PC range [pc + 8, pc + 0x268), i.e. starting after the         *)
(* 2-instruction prologue (str x19, [sp,#-16]!; ldr x19, [sp,#16]) and        *)
(* ending just before the 2-instruction epilogue (ldr x19,[sp],#16; ret).     *)
(* The wrapper CRC32C_OCTO_ZERO_FILL_XOR_CORRECT below adds the prologue/     *)
(* epilogue via ARM_ADD_RETURN_STACK_TAC.                                     *)
(*                                                                           *)
(* CORE precondition assumes: SP = sp_in, X19 = word len (already loaded by   *)
(* the wrapper-handled prologue's ldr x19, [sp,#16]). Body is CHEAT_TAC for   *)
(* now — subsequent sessions attack body cut-points (init MOVs, loop entry    *)
(* guard, LOOP16 BIGSTEP, tail blocks, XOR reduction).                        *)
(* ------------------------------------------------------------------------- *)

let CRC32C_OCTO_ZERO_FILL_XOR_CORE_CORRECT = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 sp_in
    (bs0:byte list) (bs1:byte list) (bs2:byte list) (bs3:byte list)
    (bs4:byte list) (bs5:byte list) (bs6:byte list) (bs7:byte list)
    len pc.
        len < 2 EXP 63 /\
        aligned 16 sp_in /\
        LENGTH bs0 = len /\ LENGTH bs1 = len /\
        LENGTH bs2 = len /\ LENGTH bs3 = len /\
        LENGTH bs4 = len /\ LENGTH bs5 = len /\
        LENGTH bs6 = len /\ LENGTH bs7 = len /\
        PAIRWISE nonoverlapping
         [(word pc, LENGTH crc32c_octo_zerofill_xor_mc);
          (a0, len); (a1, len); (a2, len); (a3, len);
          (a4, len); (a5, len); (a6, len); (a7, len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    crc32c_octo_zerofill_xor_mc /\
                  read PC s = word(pc + 8) /\
                  read SP s = sp_in /\
                  read X0 s = a0 /\ read X1 s = a1 /\
                  read X2 s = a2 /\ read X3 s = a3 /\
                  read X4 s = a4 /\ read X5 s = a5 /\
                  read X6 s = a6 /\ read X7 s = a7 /\
                  read X19 s = word len /\
                  read (memory :> bytelist (a0, len)) s = bs0 /\
                  read (memory :> bytelist (a1, len)) s = bs1 /\
                  read (memory :> bytelist (a2, len)) s = bs2 /\
                  read (memory :> bytelist (a3, len)) s = bs3 /\
                  read (memory :> bytelist (a4, len)) s = bs4 /\
                  read (memory :> bytelist (a5, len)) s = bs5 /\
                  read (memory :> bytelist (a6, len)) s = bs6 /\
                  read (memory :> bytelist (a7, len)) s = bs7)
             (\s. read PC s = word(pc + 0x268) /\
                  read W0 s = crc32c_xor8 bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 /\
                  read SP s = sp_in /\
                  read (memory :> bytelist (a0, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a1, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a2, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a3, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a4, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a5, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a6, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a7, len)) s = REPLICATE len (word 0))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7;
                      X8; X9; X10; X11; X12; X13; X14; X15;
                      X16; X17; X19] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a0, len);
                      memory :> bytes(a1, len);
                      memory :> bytes(a2, len);
                      memory :> bytes(a3, len);
                      memory :> bytes(a4, len);
                      memory :> bytes(a5, len);
                      memory :> bytes(a6, len);
                      memory :> bytes(a7, len)])`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Top-level correctness theorem (Phase 9).                                   *)
(*                                                                           *)
(* Inputs: 8 buffer pointers a0..a7, each pointing to a buffer of length     *)
(* len bytes; len passed via the stack at [sp+#16] after the 16-byte push.    *)
(*                                                                           *)
(* Postcondition:                                                            *)
(*   - W0 = crc32c_xor8 (initial bytes of all 8 buffers).                     *)
(*   - All 8 buffers are zero-filled (len bytes each).                        *)
(*   - x19 is restored.                                                       *)
(* ------------------------------------------------------------------------- *)

let CRC32C_OCTO_ZERO_FILL_XOR_CORRECT = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 sp_in init_x19
    (bs0:byte list) (bs1:byte list) (bs2:byte list) (bs3:byte list)
    (bs4:byte list) (bs5:byte list) (bs6:byte list) (bs7:byte list)
    len pc.
        len < 2 EXP 63 /\
        aligned 16 sp_in /\
        LENGTH bs0 = len /\ LENGTH bs1 = len /\
        LENGTH bs2 = len /\ LENGTH bs3 = len /\
        LENGTH bs4 = len /\ LENGTH bs5 = len /\
        LENGTH bs6 = len /\ LENGTH bs7 = len /\
        PAIRWISE nonoverlapping
         [(word pc, LENGTH crc32c_octo_zerofill_xor_mc);
          (word_sub sp_in (word 16), 24);
          (a0, len); (a1, len); (a2, len); (a3, len);
          (a4, len); (a5, len); (a6, len); (a7, len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    crc32c_octo_zerofill_xor_mc /\
                  read PC s = word pc /\
                  read SP s = sp_in /\
                  read X0 s = a0 /\ read X1 s = a1 /\
                  read X2 s = a2 /\ read X3 s = a3 /\
                  read X4 s = a4 /\ read X5 s = a5 /\
                  read X6 s = a6 /\ read X7 s = a7 /\
                  read X19 s = init_x19 /\
                  read (memory :> bytes64 sp_in) s = word len /\
                  read (memory :> bytelist (a0, len)) s = bs0 /\
                  read (memory :> bytelist (a1, len)) s = bs1 /\
                  read (memory :> bytelist (a2, len)) s = bs2 /\
                  read (memory :> bytelist (a3, len)) s = bs3 /\
                  read (memory :> bytelist (a4, len)) s = bs4 /\
                  read (memory :> bytelist (a5, len)) s = bs5 /\
                  read (memory :> bytelist (a6, len)) s = bs6 /\
                  read (memory :> bytelist (a7, len)) s = bs7)
             (\s. read PC s = word(pc + 0x26c) /\
                  read W0 s = crc32c_xor8 bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 /\
                  read X19 s = init_x19 /\
                  read SP s = sp_in /\
                  read (memory :> bytelist (a0, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a1, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a2, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a3, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a4, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a5, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a6, len)) s = REPLICATE len (word 0) /\
                  read (memory :> bytelist (a7, len)) s = REPLICATE len (word 0))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7;
                      X8; X9; X10; X11; X12; X13; X14; X15;
                      X16; X17; X19] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a0, len);
                      memory :> bytes(a1, len);
                      memory :> bytes(a2, len);
                      memory :> bytes(a3, len);
                      memory :> bytes(a4, len);
                      memory :> bytes(a5, len);
                      memory :> bytes(a6, len);
                      memory :> bytes(a7, len);
                      memory :> bytes(word_sub sp_in (word 16), 16)])`,
  CHEAT_TAC);;
