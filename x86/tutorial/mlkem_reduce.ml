(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Proving a simple property about program 'simple.S'
******************************************************************************)

(* Please copy this file to the root directory of s2n-bignum, then
   follow the instructions. *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

print_literal_from_elf "x86/tutorial/mlkem_reduce.o";;

(* Or, you can read .o file and store the byte list as follows:
*)
let poly_reduce_mc = define_assert_from_elf "poly_reduce_mc" "x86/tutorial/mlkem_reduce.o"
[
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0x66; 0x0f; 0x6e; 0xc0;  (* MOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0x66; 0x0f; 0x6e; 0xc8;  (* MOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xfd; 0x6f; 0x17;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x5f; 0x20;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x40;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x60;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0x6d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xed; 0xf9; 0xd0;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0xe5; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xdc;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xdd; 0xf9; 0xe0;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe4;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xd5; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xec;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xcd; 0xf9; 0xf0;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe6; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf4;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0xc5; 0xf9; 0xf8;  (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe7; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm7) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfc;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xf9; 0xc0;  (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe0; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm8) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xf9; 0xc8;  (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe1; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm9) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x5f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x6d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xed; 0xf9; 0xd0;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0xe5; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xdc;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xdd; 0xf9; 0xe0;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe4;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xd5; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xec;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xcd; 0xf9; 0xf0;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe6; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf4;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0xc5; 0xf9; 0xf8;  (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe7; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm7) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfc;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xf9; 0xc0;  (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe0; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm8) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xf9; 0xc8;  (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe1; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm9) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xfd; 0x7f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x01; 0x00; 0x00
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm9) *)
];;
let MLKEM_POLY_REDUCE_EXEC = X86_MK_EXEC_RULE poly_reduce_mc;;

(* Enable simplification of word_subwords by default.
   Nedded to prevent the symbolic simulation to explode
   as we add more instructions. *)
let org_extra_word_conv = !extra_word_CONV;;
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ !extra_word_CONV;;

let lemma_rem = prove
 (`(y == x) (mod &3329) /\
   &0 <= y /\ y < &6658
   ==> x rem &3329 = if y >= &3329 then y - &3329 else y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
  SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE);;

let overall_lemma = prove
 (`!x:int16.
        ival(word_add (word_sub (barred_x86 x) (word 3329))
                      (word_and (word_ishr (word_sub (barred_x86 x) (word 3329)) 15)
                                (word 3329))) =
        ival x rem &3329`,
  REWRITE_TAC[MATCH_MP lemma_rem (CONGBOUND_RULE `barred_x86 x`)] THEN
  GEN_TAC THEN MP_TAC(CONGBOUND_RULE `barred_x86 x`) THEN
  BITBLAST_TAC);;

let overall_lemma2 = SPEC_ALL overall_lemma;;
let overall_lemma3 = AP_TERM `iword:int -> (16)word` overall_lemma2 ;;
let overall_lemma4 = REWRITE_RULE[IWORD_IVAL] overall_lemma3;;

let SIMD_SIMPLIFY_TAC_LOCAL unfold_defs = RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV unfold_defs));;

let helper_lemma = prove
 (`!x:int16. ival(iword(ival x rem &3329):int16) = ival x rem &3329`,
  GEN_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN INT_ARITH_TAC);;

let MLKEM_REDUCE_CORRECT = prove(
  `forall pc a b.
  nonoverlapping (word pc, LENGTH poly_reduce_mc) (a, 512) /\
  aligned 32 a ==>
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) poly_reduce_mc /\
         read RIP s = word pc /\
         C_ARGUMENTS [a] s /\
         !i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i)
    // Postcondition
    (\s. read RIP s = word (pc+854) /\
         !i. i < 256
               ==> ival(read(memory :> bytes16(word_add a (word(2 * i)))) s)= ival(x i) rem &3329)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [memory :> bytes(a,512)] ,, MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,, MAYCHANGE [ZMM0] ,, MAYCHANGE [ZMM1] ,, MAYCHANGE[ZMM12] ,, MAYCHANGE[ZMM2] ,,
     MAYCHANGE[ZMM3] ,, MAYCHANGE[ZMM4] ,, MAYCHANGE[ZMM5] ,, MAYCHANGE[ZMM6] ,, MAYCHANGE[ZMM7] ,, MAYCHANGE[ZMM8] ,, MAYCHANGE[ZMM9])`,


  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REWRITE_TAC[fst MLKEM_POLY_REDUCE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS] THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN

  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add a (word n))) s0`))
            (0--15))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN


  (let lemma = WORD_BLAST `(word_zx:int256->int128) x = word_subword x (0,128)` in
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_REDUCE_EXEC [n] THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[lemma]) THEN
                      SIMD_SIMPLIFY_TAC_LOCAL[barred_x86])
            (1--166)) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN


  RULE_ASSUM_TAC(REWRITE_RULE[GSYM barred_x86]) THEN
  SIMD_SIMPLIFY_TAC_LOCAL [] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[overall_lemma4]) THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  (*** Now the result is just a replicated instance of our lemma ***)

  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s166" THEN
  REWRITE_TAC[GSYM barred_x86; overall_lemma4] THEN
  REWRITE_TAC[helper_lemma] THEN
);;