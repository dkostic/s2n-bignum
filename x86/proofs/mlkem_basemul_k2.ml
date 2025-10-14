(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication of 2-element polynomial vectors in NTT domain.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

print_literal_from_elf "x86/mlkem/mlkem_basemul_k2.o";;

let mlkem_basemul_k2_mc2 =
  define_assert_from_elf "mlkem_basemul_k2_mc2" "x86/mlkem/mlkem_basemul_k2.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0x66; 0x0f; 0x6e; 0xc0;  (* MOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x01; 0xf3; 0x01; 0xf3;
                           (* MOV (% eax) (Imm32 (word 4076991233)) *)
  0x66; 0x0f; 0x6e; 0xc8;  (* MOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc3                     (* RET *)
];;

let mlkem_basemul_k2_tmc2 = define_trimmed "mlkem_basemul_k2_tmc2" mlkem_basemul_k2_mc2;;
let mlkem_basemul_k2_tmc2_EXEC = X86_MK_CORE_EXEC_RULE mlkem_basemul_k2_tmc2;;

(* Enable simplification of word_subwords by default.
   Nedded to prevent the symbolic simulation to explode
   as we add more instructions. *)
let org_extra_word_conv = !extra_word_CONV;;
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ !extra_word_CONV;;

let montmul_x86 = define
  `montmul_x86 (x : int16) (y :int16) =
  word_sub
    (word_subword (word_mul (word_sx y : int32) (word_sx x)) (16,16) : int16)
    (word_subword
     (word_mul (word 3329) (word_sx (word_mul y (word_mul (word 62209) x)) : int32))
     (16,16))
  `;;

(*  
      (a + bX) * (c + dX) = (a*c + b*dz) + (a*d + b*c)X
                                YMM7           YMM9
*)

let SIMPLE_SPEC = prove(
  `!a b c d dz x pc.
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) (BUTLAST mlkem_basemul_k2_tmc2) /\
         read RIP s = word pc /\
         read YMM2 s = word a /\
         read YMM3 s = word b /\
         read YMM4 s = word c /\
         read YMM5 s = word d /\
         read YMM6 s = word dz)
    // Postcondition
    (\s. read RIP s = word (pc+119) /\
         read YMM7 s = part1 /\
         read YMM9 s = part2
         )
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,, MAYCHANGE[ZMM0; ZMM1; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14])`,

  REPEAT STRIP_TAC THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN

  ENSURES_INIT_TAC "s0" THEN

  (* Symbolically run one instruction *)
  X86_STEPS_TAC mlkem_basemul_k2_tmc2_EXEC (1--26) THEN 
    
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  REWRITE_TAC [WORD_BLAST `(word_zx:int256->int128) x = word_subword x (0,128)`] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(WORD_REDUCE_CONV) THEN

  ASM_REWRITE_TAC[GSYM montmul_x86] THEN

    );;