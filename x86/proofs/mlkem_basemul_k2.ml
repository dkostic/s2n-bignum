(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication of 2-element polynomial vectors in NTT domain.      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

print_literal_from_elf "x86/mlkem/mlkem_basemul_k2.o";;

let mlkem_basemul_k2_mc =
  define_assert_from_elf "mlkem_basemul_k2_mc" "x86/mlkem/mlkem_basemul_k2.o"
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
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x5e; 0x20;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x22;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfd; 0x6f; 0x6a; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xfd; 0x6f; 0x31;  (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,0))) *)
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
  0xc5; 0xfd; 0x7f; 0x3f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm9) *)
  0xc3                     (* RET *)
];;

let mlkem_basemul_k2_tmc = define_trimmed "mlkem_basemul_k2_tmc" mlkem_basemul_k2_mc;;
let mlkem_basemul_k2_tmc_EXEC = X86_MK_CORE_EXEC_RULE mlkem_basemul_k2_tmc;;

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

let montmuladd_x86 = define
  `montmuladd_x86 (x0 : int16) (x1 : int16) (y0 : int16) (y1 : int16) =
    word_add (montmul_x86 x0 x1) (montmul_x86 y0 y1)
  `;;

(*  
      (a + bX) * (c + dX) = (a*c + b*dz) + (a*d + b*c)X
                                YMM7           YMM9
*)

let SIMPLE_SPEC = prove(
  `!src1 src2 src2t dst a b c d dz pc.
        aligned 32 src1 /\
        aligned 32 src2 /\
        aligned 32 src2t /\
        aligned 32 dst /\
        ALL (nonoverlapping (dst, 512))
            [(word pc, 150);
             (src1, 1024); (src2, 1024); (src2t, 512)]
        ==> ensures x86
              (\s. bytes_loaded s (word pc) (BUTLAST mlkem_basemul_k2_tmc) /\
                   read RIP s = word pc /\
                   C_ARGUMENTS [dst; src1; src2; src2t] s /\
                   (!i. i < 16
                        ==> read(memory :> bytes16
                             (word_add src1 (word (2*i)))) s = a i) /\
                   (!i. i < 16
                        ==> read(memory :> bytes16
                             (word_add src1 (word (32 + 2*i)))) s = b i) /\
                   (!i. i < 16
                        ==> read(memory :> bytes16
                             (word_add src2 (word (2*i)))) s = c i) /\
                   (!i. i < 16
                        ==> read(memory :> bytes16
                             (word_add src2 (word (32 + 2*i)))) s = d i) /\
                   (!i. i < 16
                        ==> read(memory :> bytes16
                             (word_add src2t (word (2*i)))) s = dz i))
              (\s. read RIP s = word (pc+150) /\
                   (!i. i < 16
                        ==> read(memory :> bytes16
                             (word_add dst (word (2*i)))) s =
                                montmuladd_x86 (b i) (dz i) (a i) (c i)) /\
                   (!i. i < 16
                        ==> read(memory :> bytes16
                             (word_add dst (word (32 + 2*i)))) s =
                                montmuladd_x86 (b i) (c i) (a i) (d i)))
              (MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,, MAYCHANGE [events] ,,
               MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14] ,,
               MAYCHANGE [memory :> bytes(dst, 512)])`,

  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst mlkem_basemul_k2_tmc_EXEC] THEN
  REPEAT STRIP_TAC THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
           ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
(* 
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    ONCE_DEPTH_CONV NUM_ADD_CONV)))) THEN *)

  ENSURES_INIT_TAC "s0" THEN

  MEMORY_256_FROM_16_TAC "src1" 32 THEN
  MEMORY_256_FROM_16_TAC "src2" 32 THEN
  MEMORY_256_FROM_16_TAC "src2t" 16 THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN
  (* Forget original shape of assumption *)
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 any) s = x`] THEN
  REPEAT STRIP_TAC THEN

  (* Symbolically run one instruction *)
  (let lemma = WORD_BLAST
  `(word_zx:int256->int128) x = word_subword x (0,128)` in
  MAP_EVERY (fun n -> X86_STEPS_TAC mlkem_basemul_k2_tmc_EXEC [n] THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[lemma]) THEN
                      SIMD_SIMPLIFY_TAC [montmul_x86; montmuladd_x86])
            (1--33)) THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
           ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0]
);;