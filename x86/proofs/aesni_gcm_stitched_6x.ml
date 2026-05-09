(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Stitched 6-way AES-128-CTR + GHASH loop body (Milestone 7).               *)
(*                                                                           *)
(* Proves correctness of `aesni_gcm_stitched_6x.S`, the fast-path AES-128    *)
(* body of `.Loop6x` in aws-lc's aesni_gcm_encrypt, packaged as a            *)
(* straight-line VEX-only routine by `tools/extract_stitched_6x.py`.  See    *)
(* the .S for the derivation and the ABI comment block.                      *)
(*                                                                           *)
(* System V ABI used by the body:                                            *)
(*                                                                           *)
(*   %iptr  plaintext pointer       (6 blocks at iptr + {0,16,..,80})          *)
(*   %optr  ciphertext pointer      (6 blocks at optr + {0,16,..,80})          *)
(*   %kptr  key schedule pointer biased by -128                               *)
(*                                 (k_i at (16*i - 128)(%kptr))               *)
(*   %hptr   H-table pointer biased by -32                                     *)
(*                                 (H-power j at (16*j - 32)(%hptr))           *)
(*   %cbptr   counter-block output    (16 bytes, inc32^6 icb after body)        *)
(*   %cptr  constants pointer       (16(%cptr)=reduction-poly selector,        *)
(*                                  32(%cptr)=+1-step constant)               *)
(*                                                                           *)
(* Entry register state (matching the original `.Loop6x` entry fan-out):     *)
(*                                                                           *)
(*   xmm9  = k0 XOR icb                                                      *)
(*   xmm10 = inc32  icb                                                      *)
(*   xmm11 = inc32^2 icb                                                     *)
(*   xmm12 = inc32^3 icb                                                     *)
(*   xmm13 = inc32^4 icb                                                     *)
(*   xmm14 = inc32^5 icb                                                     *)
(*   xmm15 = k0                                                              *)
(*   xmm7  = prior-iter GHASH high accumulator                               *)
(*   xmm8  = prior-iter GHASH low accumulator                                *)
(*   xmm4  = prior-iter residue                                              *)
(*   xmm2  = +1-step constant for counter fan-out                            *)
(*   stack 16(%sptr)..112(%sptr) = prior-iter ciphertext blocks                *)
(*                                                                           *)
(* Correctness scope.  Proves the 6 ciphertext-block stores end-to-end:      *)
(* each store at `bytes128 (optr + 16*j)` equals                              *)
(*   stitched_6x_ct_block [k0;...;k10] cb_j p_j                               *)
(*     = word_xor p_j (aes128_ctr_lane_m7 cb_j [k0;...;k10])                  *)
(* The GHASH and new-counter half of the body (stores at cbptr and sptr+16)  *)
(* are still schematic — they will be resolved in a later milestone when M7  *)
(* is composed into the full .Loop6x loop invariant.                         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/aes_fips197_bridge.ml";;
needs "x86/proofs/utils/gcm_simd_simplify.ml";;
needs "common/polyval_ghash.ml";;    (* polyval_dot, h_power, ghash_wide   *)
needs "common/karatsuba_pmul.ml";;   (* PMUL_KARATSUBA                     *)

(* ------------------------------------------------------------------------- *)
(* Machine code.                                                             *)
(*                                                                           *)
(* 168 steppable VEX+scalar instructions + ret, 850 bytes total (pre-ret is  *)
(* at pc + 0x351; RIP after ret is pc + 0x351).  Instruction mix:            *)
(*                                                                           *)
(*   54  vaesenc        (9 AES rounds, 6 lanes)                              *)
(*    6  vaesenclast    (round 10, 6 lanes)                                  *)
(*   38  vpxor          (GHASH XORs, CTR XORs, reduction)                    *)
(*   32  vmovdqu        (key loads, Htable loads, ciphertext stores,         *)
(*                        new counter store, stash spill)                    *)
(*   26  vpclmulqdq     (6 Karatsuba quadruples + 2 reductions)              *)
(*    6  vpaddb         (6-lane counter increment for next iter)             *)
(*    2  vpalignr       (mid-lane carry)                                     *)
(*    1  vpsrldq / 1 vpslldq (reduction byte shifts)                         *)
(*    2  leaq           (%rdi and %rsi pointer advance by 96)                *)
(* ------------------------------------------------------------------------- *)

let aesni_gcm_stitched_6x_mc = define_assert_word_list "aesni_gcm_stitched_6x_mc"
  `[word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x59; word 0xe0;
   word 0xc5; word 0x89; word 0xfc; word 0xca; word 0xc4; word 0x41;
   word 0x29; word 0xef; word 0xd7; word 0xc4; word 0x41; word 0x21;
   word 0xef; word 0xdf; word 0xc4; word 0xc1; word 0x7a; word 0x7f;
   word 0x08; word 0xc4; word 0xe3; word 0x41; word 0x44; word 0xeb;
   word 0x10; word 0xc4; word 0x41; word 0x19; word 0xef; word 0xe7;
   word 0xc5; word 0xfa; word 0x6f; word 0x51; word 0x90; word 0xc4;
   word 0xe3; word 0x41; word 0x44; word 0xf3; word 0x01; word 0xc4;
   word 0x62; word 0x31; word 0xdc; word 0xca; word 0xc5; word 0xfa;
   word 0x6f; word 0x44; word 0x24; word 0x30; word 0xc4; word 0x41;
   word 0x11; word 0xef; word 0xef; word 0xc4; word 0xe3; word 0x41;
   word 0x44; word 0xcb; word 0x00; word 0xc4; word 0x62; word 0x29;
   word 0xdc; word 0xd2; word 0xc4; word 0x41; word 0x09; word 0xef;
   word 0xf7; word 0xc4; word 0xe3; word 0x41; word 0x44; word 0xfb;
   word 0x11; word 0xc4; word 0x62; word 0x21; word 0xdc; word 0xda;
   word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x59; word 0xf0;
   word 0xc4; word 0x62; word 0x19; word 0xdc; word 0xe2; word 0xc5;
   word 0xc9; word 0xef; word 0xf5; word 0xc4; word 0xe3; word 0x79;
   word 0x44; word 0xeb; word 0x00; word 0xc5; word 0x39; word 0xef;
   word 0xc4; word 0xc4; word 0x62; word 0x11; word 0xdc; word 0xea;
   word 0xc5; word 0xf1; word 0xef; word 0xe5; word 0xc5; word 0x7a;
   word 0x6f; word 0x79; word 0xa0; word 0xc4; word 0xe3; word 0x79;
   word 0x44; word 0xcb; word 0x10; word 0xc4; word 0x62; word 0x09;
   word 0xdc; word 0xf2; word 0xc4; word 0xe3; word 0x79; word 0x44;
   word 0xd3; word 0x01; word 0xc4; word 0x42; word 0x31; word 0xdc;
   word 0xcf; word 0xc5; word 0x39; word 0xef; word 0x44; word 0x24;
   word 0x10; word 0xc4; word 0xe3; word 0x79; word 0x44; word 0xdb;
   word 0x11; word 0xc5; word 0xfa; word 0x6f; word 0x44; word 0x24;
   word 0x40; word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7;
   word 0xc4; word 0x42; word 0x21; word 0xdc; word 0xdf; word 0xc4;
   word 0x42; word 0x19; word 0xdc; word 0xe7; word 0xc4; word 0x42;
   word 0x11; word 0xdc; word 0xef; word 0xc4; word 0xc1; word 0x7a;
   word 0x6f; word 0x69; word 0x10; word 0xc4; word 0x42; word 0x09;
   word 0xdc; word 0xf7; word 0xc5; word 0x7a; word 0x6f; word 0x79;
   word 0xb0; word 0xc5; word 0xc9; word 0xef; word 0xf1; word 0xc4;
   word 0xe3; word 0x79; word 0x44; word 0xcd; word 0x00; word 0xc4;
   word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc5; word 0xc9;
   word 0xef; word 0xf2; word 0xc4; word 0xe3; word 0x79; word 0x44;
   word 0xd5; word 0x10; word 0xc4; word 0x42; word 0x29; word 0xdc;
   word 0xd7; word 0xc5; word 0xc1; word 0xef; word 0xfb; word 0xc4;
   word 0xe3; word 0x79; word 0x44; word 0xdd; word 0x01; word 0xc4;
   word 0x42; word 0x21; word 0xdc; word 0xdf; word 0xc4; word 0xe3;
   word 0x79; word 0x44; word 0xed; word 0x11; word 0xc5; word 0xfa;
   word 0x6f; word 0x44; word 0x24; word 0x50; word 0xc4; word 0x42;
   word 0x19; word 0xdc; word 0xe7; word 0xc4; word 0x42; word 0x11;
   word 0xdc; word 0xef; word 0xc5; word 0xd9; word 0xef; word 0xe1;
   word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x49; word 0x20;
   word 0xc4; word 0x42; word 0x09; word 0xdc; word 0xf7; word 0xc5;
   word 0x7a; word 0x6f; word 0x79; word 0xc0; word 0xc5; word 0xc9;
   word 0xef; word 0xf2; word 0xc4; word 0xe3; word 0x79; word 0x44;
   word 0xd1; word 0x00; word 0xc4; word 0x42; word 0x31; word 0xdc;
   word 0xcf; word 0xc5; word 0xc9; word 0xef; word 0xf3; word 0xc4;
   word 0xe3; word 0x79; word 0x44; word 0xd9; word 0x10; word 0xc4;
   word 0x42; word 0x29; word 0xdc; word 0xd7; word 0xc5; word 0xc1;
   word 0xef; word 0xfd; word 0xc4; word 0xe3; word 0x79; word 0x44;
   word 0xe9; word 0x01; word 0xc4; word 0x42; word 0x21; word 0xdc;
   word 0xdf; word 0xc4; word 0xe3; word 0x79; word 0x44; word 0xc9;
   word 0x11; word 0xc5; word 0xfa; word 0x6f; word 0x44; word 0x24;
   word 0x60; word 0xc4; word 0x42; word 0x19; word 0xdc; word 0xe7;
   word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0xc5;
   word 0xd9; word 0xef; word 0xe2; word 0xc4; word 0xc1; word 0x7a;
   word 0x6f; word 0x51; word 0x40; word 0xc4; word 0x42; word 0x09;
   word 0xdc; word 0xf7; word 0xc5; word 0x7a; word 0x6f; word 0x79;
   word 0xd0; word 0xc5; word 0xc9; word 0xef; word 0xf3; word 0xc4;
   word 0xe3; word 0x79; word 0x44; word 0xda; word 0x00; word 0xc4;
   word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc5; word 0xc9;
   word 0xef; word 0xf5; word 0xc4; word 0xe3; word 0x79; word 0x44;
   word 0xea; word 0x10; word 0xc4; word 0x42; word 0x29; word 0xdc;
   word 0xd7; word 0xc5; word 0xc1; word 0xef; word 0xf9; word 0xc4;
   word 0xe3; word 0x79; word 0x44; word 0xca; word 0x01; word 0xc5;
   word 0x39; word 0xef; word 0x44; word 0x24; word 0x70; word 0xc4;
   word 0x42; word 0x21; word 0xdc; word 0xdf; word 0xc4; word 0xe3;
   word 0x79; word 0x44; word 0xd2; word 0x11; word 0xc4; word 0x42;
   word 0x19; word 0xdc; word 0xe7; word 0xc4; word 0x42; word 0x11;
   word 0xdc; word 0xef; word 0xc5; word 0xd9; word 0xef; word 0xe3;
   word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x59; word 0x50;
   word 0xc4; word 0x42; word 0x09; word 0xdc; word 0xf7; word 0xc5;
   word 0x7a; word 0x6f; word 0x79; word 0xe0; word 0xc5; word 0xc9;
   word 0xef; word 0xf5; word 0xc4; word 0xe3; word 0x39; word 0x44;
   word 0xeb; word 0x10; word 0xc4; word 0x42; word 0x31; word 0xdc;
   word 0xcf; word 0xc5; word 0xc9; word 0xef; word 0xf1; word 0xc4;
   word 0xe3; word 0x39; word 0x44; word 0xcb; word 0x01; word 0xc4;
   word 0x42; word 0x29; word 0xdc; word 0xd7; word 0xc5; word 0xc1;
   word 0xef; word 0xfa; word 0xc4; word 0xe3; word 0x39; word 0x44;
   word 0xd3; word 0x00; word 0xc4; word 0x42; word 0x21; word 0xdc;
   word 0xdf; word 0xc4; word 0x63; word 0x39; word 0x44; word 0xc3;
   word 0x11; word 0xc4; word 0x42; word 0x19; word 0xdc; word 0xe7;
   word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0xc5;
   word 0xc9; word 0xef; word 0xf5; word 0xc4; word 0x42; word 0x09;
   word 0xdc; word 0xf7; word 0xc5; word 0xc9; word 0xef; word 0xf1;
   word 0xc5; word 0x7a; word 0x6f; word 0x79; word 0xf0; word 0xc5;
   word 0xd1; word 0x73; word 0xfe; word 0x08; word 0xc5; word 0xd9;
   word 0xef; word 0xe2; word 0xc4; word 0xc1; word 0x7a; word 0x6f;
   word 0x5b; word 0x10; word 0xc4; word 0x42; word 0x31; word 0xdc;
   word 0xcf; word 0xc4; word 0xc1; word 0x41; word 0xef; word 0xf8;
   word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7; word 0xc5;
   word 0xd9; word 0xef; word 0xe5; word 0xc4; word 0x42; word 0x21;
   word 0xdc; word 0xdf; word 0xc4; word 0xe3; word 0x59; word 0x0f;
   word 0xc4; word 0x08; word 0xc4; word 0xe3; word 0x59; word 0x44;
   word 0xe3; word 0x10; word 0xc4; word 0x42; word 0x19; word 0xdc;
   word 0xe7; word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef;
   word 0xc5; word 0xfa; word 0x6f; word 0x09; word 0xc4; word 0x42;
   word 0x09; word 0xdc; word 0xf7; word 0xc4; word 0x62; word 0x31;
   word 0xdc; word 0xc9; word 0xc5; word 0x7a; word 0x6f; word 0x79;
   word 0x10; word 0xc4; word 0x62; word 0x29; word 0xdc; word 0xd1;
   word 0xc5; word 0xc9; word 0x73; word 0xde; word 0x08; word 0xc4;
   word 0x62; word 0x21; word 0xdc; word 0xd9; word 0xc5; word 0xc1;
   word 0xef; word 0xfe; word 0xc4; word 0x62; word 0x19; word 0xdc;
   word 0xe1; word 0xc5; word 0xd9; word 0xef; word 0xe0; word 0xc4;
   word 0x62; word 0x11; word 0xdc; word 0xe9; word 0xc4; word 0x62;
   word 0x09; word 0xdc; word 0xf1; word 0xc5; word 0xfa; word 0x6f;
   word 0x49; word 0x20; word 0xc4; word 0x42; word 0x31; word 0xdc;
   word 0xcf; word 0xc5; word 0xfa; word 0x7f; word 0x7c; word 0x24;
   word 0x10; word 0xc4; word 0x63; word 0x59; word 0x0f; word 0xc4;
   word 0x08; word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7;
   word 0xc4; word 0xe3; word 0x59; word 0x44; word 0xe3; word 0x10;
   word 0xc5; word 0xf1; word 0xef; word 0x17; word 0xc4; word 0x42;
   word 0x21; word 0xdc; word 0xdf; word 0xc5; word 0xf1; word 0xef;
   word 0x47; word 0x10; word 0xc4; word 0x42; word 0x19; word 0xdc;
   word 0xe7; word 0xc5; word 0xf1; word 0xef; word 0x6f; word 0x20;
   word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0xc5;
   word 0xf1; word 0xef; word 0x77; word 0x30; word 0xc4; word 0x42;
   word 0x09; word 0xdc; word 0xf7; word 0xc5; word 0xf1; word 0xef;
   word 0x7f; word 0x40; word 0xc5; word 0xf1; word 0xef; word 0x5f;
   word 0x50; word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x08;
   word 0xc4; word 0x62; word 0x31; word 0xdd; word 0xca; word 0xc4;
   word 0xc1; word 0x7a; word 0x6f; word 0x53; word 0x20; word 0xc4;
   word 0x62; word 0x29; word 0xdd; word 0xd0; word 0xc5; word 0xf1;
   word 0xfc; word 0xc2; word 0x48; word 0x8d; word 0x7f; word 0x60;
   word 0xc4; word 0x62; word 0x21; word 0xdd; word 0xdd; word 0xc5;
   word 0xf9; word 0xfc; word 0xea; word 0x48; word 0x8d; word 0x76;
   word 0x60; word 0xc5; word 0x7a; word 0x6f; word 0x79; word 0x80;
   word 0xc4; word 0x62; word 0x19; word 0xdd; word 0xe6; word 0xc5;
   word 0xd1; word 0xfc; word 0xf2; word 0xc4; word 0x62; word 0x11;
   word 0xdd; word 0xef; word 0xc5; word 0xc9; word 0xfc; word 0xfa;
   word 0xc4; word 0x62; word 0x09; word 0xdd; word 0xf3; word 0xc5;
   word 0xc1; word 0xfc; word 0xda; word 0xc5; word 0x7a; word 0x7f;
   word 0x4e; word 0xa0; word 0xc5; word 0x7a; word 0x7f; word 0x56;
   word 0xb0; word 0xc5; word 0x7a; word 0x7f; word 0x5e; word 0xc0;
   word 0xc5; word 0x7a; word 0x7f; word 0x66; word 0xd0; word 0xc5;
   word 0x7a; word 0x7f; word 0x6e; word 0xe0; word 0xc5; word 0x7a;
   word 0x7f; word 0x76; word 0xf0; word 0xc3]:byte list`
  [0xc4; 0xc1; 0x7a; 0x6f; 0x59; 0xe0; 0xc5; 0x89; 0xfc; 0xca; 0xc4; 0x41;
   0x29; 0xef; 0xd7; 0xc4; 0x41; 0x21; 0xef; 0xdf; 0xc4; 0xc1; 0x7a; 0x7f;
   0x08; 0xc4; 0xe3; 0x41; 0x44; 0xeb; 0x10; 0xc4; 0x41; 0x19; 0xef; 0xe7;
   0xc5; 0xfa; 0x6f; 0x51; 0x90; 0xc4; 0xe3; 0x41; 0x44; 0xf3; 0x01; 0xc4;
   0x62; 0x31; 0xdc; 0xca; 0xc5; 0xfa; 0x6f; 0x44; 0x24; 0x30; 0xc4; 0x41;
   0x11; 0xef; 0xef; 0xc4; 0xe3; 0x41; 0x44; 0xcb; 0x00; 0xc4; 0x62; 0x29;
   0xdc; 0xd2; 0xc4; 0x41; 0x09; 0xef; 0xf7; 0xc4; 0xe3; 0x41; 0x44; 0xfb;
   0x11; 0xc4; 0x62; 0x21; 0xdc; 0xda; 0xc4; 0xc1; 0x7a; 0x6f; 0x59; 0xf0;
   0xc4; 0x62; 0x19; 0xdc; 0xe2; 0xc5; 0xc9; 0xef; 0xf5; 0xc4; 0xe3; 0x79;
   0x44; 0xeb; 0x00; 0xc5; 0x39; 0xef; 0xc4; 0xc4; 0x62; 0x11; 0xdc; 0xea;
   0xc5; 0xf1; 0xef; 0xe5; 0xc5; 0x7a; 0x6f; 0x79; 0xa0; 0xc4; 0xe3; 0x79;
   0x44; 0xcb; 0x10; 0xc4; 0x62; 0x09; 0xdc; 0xf2; 0xc4; 0xe3; 0x79; 0x44;
   0xd3; 0x01; 0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc5; 0x39; 0xef; 0x44; 0x24;
   0x10; 0xc4; 0xe3; 0x79; 0x44; 0xdb; 0x11; 0xc5; 0xfa; 0x6f; 0x44; 0x24;
   0x40; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4;
   0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc4; 0xc1; 0x7a;
   0x6f; 0x69; 0x10; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x79;
   0xb0; 0xc5; 0xc9; 0xef; 0xf1; 0xc4; 0xe3; 0x79; 0x44; 0xcd; 0x00; 0xc4;
   0x42; 0x31; 0xdc; 0xcf; 0xc5; 0xc9; 0xef; 0xf2; 0xc4; 0xe3; 0x79; 0x44;
   0xd5; 0x10; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc5; 0xc1; 0xef; 0xfb; 0xc4;
   0xe3; 0x79; 0x44; 0xdd; 0x01; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4; 0xe3;
   0x79; 0x44; 0xed; 0x11; 0xc5; 0xfa; 0x6f; 0x44; 0x24; 0x50; 0xc4; 0x42;
   0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc5; 0xd9; 0xef; 0xe1;
   0xc4; 0xc1; 0x7a; 0x6f; 0x49; 0x20; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5;
   0x7a; 0x6f; 0x79; 0xc0; 0xc5; 0xc9; 0xef; 0xf2; 0xc4; 0xe3; 0x79; 0x44;
   0xd1; 0x00; 0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc5; 0xc9; 0xef; 0xf3; 0xc4;
   0xe3; 0x79; 0x44; 0xd9; 0x10; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc5; 0xc1;
   0xef; 0xfd; 0xc4; 0xe3; 0x79; 0x44; 0xe9; 0x01; 0xc4; 0x42; 0x21; 0xdc;
   0xdf; 0xc4; 0xe3; 0x79; 0x44; 0xc9; 0x11; 0xc5; 0xfa; 0x6f; 0x44; 0x24;
   0x60; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc5;
   0xd9; 0xef; 0xe2; 0xc4; 0xc1; 0x7a; 0x6f; 0x51; 0x40; 0xc4; 0x42; 0x09;
   0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x79; 0xd0; 0xc5; 0xc9; 0xef; 0xf3; 0xc4;
   0xe3; 0x79; 0x44; 0xda; 0x00; 0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc5; 0xc9;
   0xef; 0xf5; 0xc4; 0xe3; 0x79; 0x44; 0xea; 0x10; 0xc4; 0x42; 0x29; 0xdc;
   0xd7; 0xc5; 0xc1; 0xef; 0xf9; 0xc4; 0xe3; 0x79; 0x44; 0xca; 0x01; 0xc5;
   0x39; 0xef; 0x44; 0x24; 0x70; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4; 0xe3;
   0x79; 0x44; 0xd2; 0x11; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11;
   0xdc; 0xef; 0xc5; 0xd9; 0xef; 0xe3; 0xc4; 0xc1; 0x7a; 0x6f; 0x59; 0x50;
   0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x79; 0xe0; 0xc5; 0xc9;
   0xef; 0xf5; 0xc4; 0xe3; 0x39; 0x44; 0xeb; 0x10; 0xc4; 0x42; 0x31; 0xdc;
   0xcf; 0xc5; 0xc9; 0xef; 0xf1; 0xc4; 0xe3; 0x39; 0x44; 0xcb; 0x01; 0xc4;
   0x42; 0x29; 0xdc; 0xd7; 0xc5; 0xc1; 0xef; 0xfa; 0xc4; 0xe3; 0x39; 0x44;
   0xd3; 0x00; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4; 0x63; 0x39; 0x44; 0xc3;
   0x11; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc5;
   0xc9; 0xef; 0xf5; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0xc9; 0xef; 0xf1;
   0xc5; 0x7a; 0x6f; 0x79; 0xf0; 0xc5; 0xd1; 0x73; 0xfe; 0x08; 0xc5; 0xd9;
   0xef; 0xe2; 0xc4; 0xc1; 0x7a; 0x6f; 0x5b; 0x10; 0xc4; 0x42; 0x31; 0xdc;
   0xcf; 0xc4; 0xc1; 0x41; 0xef; 0xf8; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc5;
   0xd9; 0xef; 0xe5; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4; 0xe3; 0x59; 0x0f;
   0xc4; 0x08; 0xc4; 0xe3; 0x59; 0x44; 0xe3; 0x10; 0xc4; 0x42; 0x19; 0xdc;
   0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc5; 0xfa; 0x6f; 0x09; 0xc4; 0x42;
   0x09; 0xdc; 0xf7; 0xc4; 0x62; 0x31; 0xdc; 0xc9; 0xc5; 0x7a; 0x6f; 0x79;
   0x10; 0xc4; 0x62; 0x29; 0xdc; 0xd1; 0xc5; 0xc9; 0x73; 0xde; 0x08; 0xc4;
   0x62; 0x21; 0xdc; 0xd9; 0xc5; 0xc1; 0xef; 0xfe; 0xc4; 0x62; 0x19; 0xdc;
   0xe1; 0xc5; 0xd9; 0xef; 0xe0; 0xc4; 0x62; 0x11; 0xdc; 0xe9; 0xc4; 0x62;
   0x09; 0xdc; 0xf1; 0xc5; 0xfa; 0x6f; 0x49; 0x20; 0xc4; 0x42; 0x31; 0xdc;
   0xcf; 0xc5; 0xfa; 0x7f; 0x7c; 0x24; 0x10; 0xc4; 0x63; 0x59; 0x0f; 0xc4;
   0x08; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0xe3; 0x59; 0x44; 0xe3; 0x10;
   0xc5; 0xf1; 0xef; 0x17; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc5; 0xf1; 0xef;
   0x47; 0x10; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc5; 0xf1; 0xef; 0x6f; 0x20;
   0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc5; 0xf1; 0xef; 0x77; 0x30; 0xc4; 0x42;
   0x09; 0xdc; 0xf7; 0xc5; 0xf1; 0xef; 0x7f; 0x40; 0xc5; 0xf1; 0xef; 0x5f;
   0x50; 0xc4; 0xc1; 0x7a; 0x6f; 0x08; 0xc4; 0x62; 0x31; 0xdd; 0xca; 0xc4;
   0xc1; 0x7a; 0x6f; 0x53; 0x20; 0xc4; 0x62; 0x29; 0xdd; 0xd0; 0xc5; 0xf1;
   0xfc; 0xc2; 0x48; 0x8d; 0x7f; 0x60; 0xc4; 0x62; 0x21; 0xdd; 0xdd; 0xc5;
   0xf9; 0xfc; 0xea; 0x48; 0x8d; 0x76; 0x60; 0xc5; 0x7a; 0x6f; 0x79; 0x80;
   0xc4; 0x62; 0x19; 0xdd; 0xe6; 0xc5; 0xd1; 0xfc; 0xf2; 0xc4; 0x62; 0x11;
   0xdd; 0xef; 0xc5; 0xc9; 0xfc; 0xfa; 0xc4; 0x62; 0x09; 0xdd; 0xf3; 0xc5;
   0xc1; 0xfc; 0xda; 0xc5; 0x7a; 0x7f; 0x4e; 0xa0; 0xc5; 0x7a; 0x7f; 0x56;
   0xb0; 0xc5; 0x7a; 0x7f; 0x5e; 0xc0; 0xc5; 0x7a; 0x7f; 0x66; 0xd0; 0xc5;
   0x7a; 0x7f; 0x6e; 0xe0; 0xc5; 0x7a; 0x7f; 0x76; 0xf0; 0xc3];;

let AESNI_GCM_STITCHED_6X_EXEC = X86_MK_CORE_EXEC_RULE aesni_gcm_stitched_6x_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness statement (ciphertext-store half of the body).                *)
(*                                                                           *)
(* The 166 instructions produce the following observable side effects:       *)
(*                                                                           *)
(*   - 6 ciphertext blocks at memory :> bytes128 (optr + 16*j), j=0..5.       *)
(*   - 1 new-counter block at memory :> bytes128 cbptr.                         *)
(*   - 1 stash block at memory :> bytes128 (sptr + 16) (this is the per-iter  *)
(*     cipherblock-XOR-GHASH value saved for the NEXT iteration's dot).      *)
(*                                                                           *)
(* The ABI inputs we expose as preconditions:                                *)
(*                                                                           *)
(*   k_i                for i = 0..10     (AES-128 round keys)               *)
(*   h_j  :int128        for j = 0..5     (6 Htable entries used in-body)    *)
(*   p_j  :int128        for j = 0..5     (6 plaintext blocks at iptr+16*j)   *)
(*   cb0..cb5            (6 pre-shuffled counter blocks c0..c5)              *)
(*   new_cb = icb + 6    (the +1 step constant at 32(%cptr) and its +6        *)
(*                        result are derived from the 6 vpaddb chain)        *)
(*   red  :int128        (reduction-poly operand at 16(%cptr))                *)
(*   plus :int128        (+1-step counter-increment pattern at 32(%cptr))     *)
(*   xi8, xi7, xi4       (prior-iter GHASH and residue registers)            *)
(*   sp16..sp112         (prior-iter stash slots at 16(%sptr)..112(%sptr))     *)
(*                                                                           *)
(* The postcondition uses the same spec shape as Milestone 5's               *)
(* `aes128_ctr_lane`: each ciphertext block is the XOR of the plaintext       *)
(* block with AES-128 applied to the pre-shuffled counter.  The GHASH and    *)
(* new-counter halves of the body — the stores at cbptr and sptr+16 — are    *)
(* MAYCHANGE'd but their values are not asserted here; they will be pinned   *)
(* down when M7 is composed into the .Loop6x loop invariant.                 *)
(* ------------------------------------------------------------------------- *)

(* Local copy of Milestone 5's `aes128_ctr_lane` spec helper — inlined here  *)
(* so this file depends only on `aes_fips197_bridge.ml`, not on the M5 proof *)
(* module.  Identical body.                                                  *)

let aes128_ctr_lane_m7 = new_definition
  `aes128_ctr_lane_m7 (c:int128) (ks:int128 list) =
     word_reversefields 8
       (aes128_cipher (word_reversefields 8 c)
                      (MAP (word_reversefields 8) ks))`;;

let stitched_6x_ct_block = new_definition
  `stitched_6x_ct_block (ks:int128 list) (c:int128) (p:int128) : int128 =
     word_xor p (aes128_ctr_lane_m7 c ks)`;;

(* Local copy of `WORD_REVERSEFIELDS_XOR_128` from Milestone 5's               *)
(* `aesni_ctr32_6x_core.ml` so this file does not need to `needs` that proof.  *)

let WORD_REVERSEFIELDS_XOR_128 = WORD_BLAST
  `!(a:int128) b. word_reversefields 8 (word_xor a b) =
                  word_xor (word_reversefields 8 a) (word_reversefields 8 b)`;;

(* Correctness.                                                              *)

let AESNI_GCM_STITCHED_6X_CORRECT = prove
 (`!optr iptr kptr hptr cbptr cptr sptr
      p0 p1 p2 p3 p4 p5
      cb0 cb1 cb2 cb3 cb4 cb5
      k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
      h0 h1 h3 h4 h6 h7
      xi4 xi7 xi8
      sp16 sp32 sp48 sp64 sp80 sp96 sp112
      red plus
      pc.
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (optr,96) /\
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (cbptr,16) /\
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (word_add sptr (word 16),16) /\
      nonoverlapping (optr,96) (iptr,16) /\
      nonoverlapping (optr,96) (word_add iptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 48),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (optr,96) (kptr,16) /\
      nonoverlapping (optr,96) (word_add kptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add cptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add cptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 48),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 96),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 112),16) /\
      nonoverlapping (cbptr,16) (iptr,16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 48),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (cbptr,16) (kptr,16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add cptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add cptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 48),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 96),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 112),16) /\
      nonoverlapping (word_add sptr (word 16),16) (iptr,16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 48),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (word_add sptr (word 16),16) (kptr,16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add cptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add cptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 48),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 96),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 112),16) /\
      nonoverlapping (optr,96) (cbptr,16) /\
      nonoverlapping (optr,96) (word_add sptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 16),16)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_6x_mc) /\
                read RIP s = word pc /\
                read RDI s = iptr /\
                read RSI s = optr /\
                read RCX s = kptr /\
                read R9  s = hptr /\
                read R8  s = cbptr /\
                read R11 s = cptr /\
                read RSP s = sptr /\
                read (memory :> bytes128 iptr) s = p0 /\
                read (memory :> bytes128 (word_add iptr (word 16))) s = p1 /\
                read (memory :> bytes128 (word_add iptr (word 32))) s = p2 /\
                read (memory :> bytes128 (word_add iptr (word 48))) s = p3 /\
                read (memory :> bytes128 (word_add iptr (word 64))) s = p4 /\
                read (memory :> bytes128 (word_add iptr (word 80))) s = p5 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551488))) s = k0 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551504))) s = k1 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551520))) s = k2 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551536))) s = k3 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551552))) s = k4 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551568))) s = k5 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551584))) s = k6 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551600))) s = k7 /\
                read (memory :> bytes128 kptr) s = k8 /\
                read (memory :> bytes128 (word_add kptr (word 16))) s = k9 /\
                read (memory :> bytes128 (word_add kptr (word 32))) s = k10 /\
                read (memory :> bytes128
                  (word_add hptr (word 18446744073709551584))) s = h0 /\
                read (memory :> bytes128
                  (word_add hptr (word 18446744073709551600))) s = h1 /\
                read (memory :> bytes128 (word_add hptr (word 16))) s = h3 /\
                read (memory :> bytes128 (word_add hptr (word 32))) s = h4 /\
                read (memory :> bytes128 (word_add hptr (word 64))) s = h6 /\
                read (memory :> bytes128 (word_add hptr (word 80))) s = h7 /\
                read (memory :> bytes128 (word_add cptr (word 16))) s = red /\
                read (memory :> bytes128 (word_add cptr (word 32))) s = plus /\
                read (memory :> bytes128 cbptr) s = cb0 /\
                read (memory :> bytes128 (word_add sptr (word 16))) s = sp16 /\
                read (memory :> bytes128 (word_add sptr (word 32))) s = sp32 /\
                read (memory :> bytes128 (word_add sptr (word 48))) s = sp48 /\
                read (memory :> bytes128 (word_add sptr (word 64))) s = sp64 /\
                read (memory :> bytes128 (word_add sptr (word 80))) s = sp80 /\
                read (memory :> bytes128 (word_add sptr (word 96))) s = sp96 /\
                read (memory :> bytes128 (word_add sptr (word 112))) s = sp112 /\
                read YMM2  s = word_zx (plus:int128) /\
                read YMM4  s = word_zx (xi4:int128) /\
                read YMM7  s = word_zx (xi7:int128) /\
                read YMM8  s = word_zx (xi8:int128) /\
                read YMM9  s = word_zx (word_xor cb0 k0 : int128) /\
                read YMM10 s = word_zx (cb1:int128) /\
                read YMM11 s = word_zx (cb2:int128) /\
                read YMM12 s = word_zx (cb3:int128) /\
                read YMM13 s = word_zx (cb4:int128) /\
                read YMM14 s = word_zx (cb5:int128) /\
                read YMM15 s = word_zx (k0:int128))
           (\s. read RIP s = word (pc + 0x351) /\
                read RDI s = word_add iptr (word 96) /\
                read RSI s = word_add optr (word 96) /\
                read (memory :> bytes128 optr) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb0 p0 /\
                read (memory :> bytes128 (word_add optr (word 16))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb1 p1 /\
                read (memory :> bytes128 (word_add optr (word 32))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb2 p2 /\
                read (memory :> bytes128 (word_add optr (word 48))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb3 p3 /\
                read (memory :> bytes128 (word_add optr (word 64))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb4 p4 /\
                read (memory :> bytes128 (word_add optr (word 80))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb5 p5)
           (MAYCHANGE [RIP; RDI; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes128 optr;
                       memory :> bytes128 (word_add optr (word 16));
                       memory :> bytes128 (word_add optr (word 32));
                       memory :> bytes128 (word_add optr (word 48));
                       memory :> bytes128 (word_add optr (word 64));
                       memory :> bytes128 (word_add optr (word 80));
                       memory :> bytes128 cbptr;
                       memory :> bytes128 (word_add sptr (word 16))])`,
  MAP_EVERY X_GEN_TAC
   [`optr:int64`; `iptr:int64`; `kptr:int64`; `hptr:int64`; `cbptr:int64`;
    `cptr:int64`; `sptr:int64`;
    `p0:int128`; `p1:int128`; `p2:int128`;
    `p3:int128`; `p4:int128`; `p5:int128`;
    `cb0:int128`; `cb1:int128`; `cb2:int128`;
    `cb3:int128`; `cb4:int128`; `cb5:int128`;
    `k0:int128`; `k1:int128`; `k2:int128`; `k3:int128`;
    `k4:int128`; `k5:int128`; `k6:int128`; `k7:int128`;
    `k8:int128`; `k9:int128`; `k10:int128`;
    `h0:int128`; `h1:int128`; `h3:int128`;
    `h4:int128`; `h6:int128`; `h7:int128`;
    `xi4:int128`; `xi7:int128`; `xi8:int128`;
    `sp16:int128`; `sp32:int128`; `sp48:int128`; `sp64:int128`;
    `sp80:int128`; `sp96:int128`; `sp112:int128`;
    `red:int128`; `plus:int128`;
    `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[(REWRITE_CONV[aesni_gcm_stitched_6x_mc] THENC LENGTH_CONV)
                `LENGTH aesni_gcm_stitched_6x_mc`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* Drive all 168 steps with the per-step refold pass from Milestone 6.     *)
  (* The rewrite pass runs BOTH before and after the step so the stepper's   *)
  (* ASSUMPTION_STATE_UPDATE_TAC sees simplified forms of each existing      *)
  (* `read YMM_ sN = <expr>` hypothesis; without the pre-step pass the       *)
  (* ortho-conv silently drops hypotheses whose RHS is a nested word_zx      *)
  (* tree.  After the step, the same rewrites fold the newly emitted         *)
  (* hypothesis so it's tractable for the next iteration.                    *)
  MAP_EVERY (fun n ->
    RULE_ASSUM_TAC(REWRITE_RULE
     [VPSHUFB_BYTEREV_128;
      VPALIGNR_8_SWAP_128_VIA_ZX_256;
      WORD_ZX_ZX_128]) THEN
    X86_STEPS_TAC AESNI_GCM_STITCHED_6X_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [VPSHUFB_BYTEREV_128;
      VPALIGNR_8_SWAP_128_VIA_ZX_256;
      WORD_ZX_ZX_128]) THEN
    GHASH_ABBREV_STEP_TAC)
   (1--168) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (* 6 residual equalities survive, one per lane: the store at              *)
  (* `bytes128 (optr + 16*j)` equals `stitched_6x_ct_block ks cb_j p_j`.    *)
  (* Unfold the spec wrappers, then apply the AESENC/AESENCLAST FIPS-197    *)
  (* bridge and the aes128_cipher unrolling to reduce to a pure word_xor    *)
  (* identity in the outer p_j and k10 (the inner AES chain is identical    *)
  (* on both sides).  Mirrors Milestone 5's closure template at             *)
  (* aesni_ctr32_6x_core.ml:321-336.                                        *)
  REWRITE_TAC[stitched_6x_ct_block; aes128_ctr_lane_m7] THEN
  REWRITE_TAC[AESENC_FIPS197_BRIDGE_ALT; AESENCLAST_FIPS197_BRIDGE_ALT] THEN
  REWRITE_TAC[aes128_cipher; MAP] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256;
           ARITH_LE; ARITH_LT; ARITH;
           WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_XOR_0;
           WORD_REVERSEFIELDS_XOR_128] THEN
  REWRITE_TAC[fips197_final_round; WORD_REVERSEFIELDS_XOR_128;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  (* Close the 6 lane equalities.  Each one has the shape                    *)
  (*   word_xor Z (word_xor k10 p_j) = word_xor p_j (word_xor Z k10)         *)
  (* where Z is the common inner chain.  WORD_BLAST cannot see through the   *)
  (* fips197_* constants, so abstract Z to a variable per-conjunct and let   *)
  (* WORD_BLAST close the residual 128-bit XOR identity.                     *)
  REPEAT CONJ_TAC THEN
  (fun (asl,w) ->
    let lhs,_ = dest_eq w in
    (SPEC_TAC(lhand lhs,`u:int128`) THEN GEN_TAC THEN
     CONV_TAC WORD_BLAST) (asl,w)));;

(* ------------------------------------------------------------------------- *)
(* Extended post: additionally pins YMM2 = word_zx plus and YMM15 = word_zx   *)
(* k0 at M7's exit.  Both registers are overwritten mid-body but the body's  *)
(* final xmm2/xmm15 loads (vmovdqu 32(%r11),%xmm2 and vmovdqu 0-128(%rcx),   *)
(* %xmm15) restore them from the invariant memory locations cptr+32 and     *)
(* kptr-128, respectively.  Used by M8's loop-inductive step to carry the   *)
(* loopinv's YMM2 / YMM15 pins across the body.                             *)
(* ------------------------------------------------------------------------- *)

let AESNI_GCM_STITCHED_6X_CORRECT_EXT = prove
 (`!optr iptr kptr hptr cbptr cptr sptr
      p0 p1 p2 p3 p4 p5
      cb0 cb1 cb2 cb3 cb4 cb5
      k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
      h0 h1 h3 h4 h6 h7
      xi4 xi7 xi8
      sp16 sp32 sp48 sp64 sp80 sp96 sp112
      red plus
      pc.
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (optr,96) /\
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (cbptr,16) /\
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (word_add sptr (word 16),16) /\
      nonoverlapping (optr,96) (iptr,16) /\
      nonoverlapping (optr,96) (word_add iptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 48),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (optr,96) (kptr,16) /\
      nonoverlapping (optr,96) (word_add kptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add cptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add cptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 48),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 96),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 112),16) /\
      nonoverlapping (cbptr,16) (iptr,16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 48),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (cbptr,16) (kptr,16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add cptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add cptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 48),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 96),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 112),16) /\
      nonoverlapping (word_add sptr (word 16),16) (iptr,16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 48),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (word_add sptr (word 16),16) (kptr,16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add cptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add cptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 48),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 96),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 112),16) /\
      nonoverlapping (optr,96) (cbptr,16) /\
      nonoverlapping (optr,96) (word_add sptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 16),16)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_6x_mc) /\
                read RIP s = word pc /\
                read RDI s = iptr /\
                read RSI s = optr /\
                read RCX s = kptr /\
                read R9  s = hptr /\
                read R8  s = cbptr /\
                read R11 s = cptr /\
                read RSP s = sptr /\
                read (memory :> bytes128 iptr) s = p0 /\
                read (memory :> bytes128 (word_add iptr (word 16))) s = p1 /\
                read (memory :> bytes128 (word_add iptr (word 32))) s = p2 /\
                read (memory :> bytes128 (word_add iptr (word 48))) s = p3 /\
                read (memory :> bytes128 (word_add iptr (word 64))) s = p4 /\
                read (memory :> bytes128 (word_add iptr (word 80))) s = p5 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551488))) s = k0 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551504))) s = k1 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551520))) s = k2 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551536))) s = k3 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551552))) s = k4 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551568))) s = k5 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551584))) s = k6 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551600))) s = k7 /\
                read (memory :> bytes128 kptr) s = k8 /\
                read (memory :> bytes128 (word_add kptr (word 16))) s = k9 /\
                read (memory :> bytes128 (word_add kptr (word 32))) s = k10 /\
                read (memory :> bytes128
                  (word_add hptr (word 18446744073709551584))) s = h0 /\
                read (memory :> bytes128
                  (word_add hptr (word 18446744073709551600))) s = h1 /\
                read (memory :> bytes128 (word_add hptr (word 16))) s = h3 /\
                read (memory :> bytes128 (word_add hptr (word 32))) s = h4 /\
                read (memory :> bytes128 (word_add hptr (word 64))) s = h6 /\
                read (memory :> bytes128 (word_add hptr (word 80))) s = h7 /\
                read (memory :> bytes128 (word_add cptr (word 16))) s = red /\
                read (memory :> bytes128 (word_add cptr (word 32))) s = plus /\
                read (memory :> bytes128 cbptr) s = cb0 /\
                read (memory :> bytes128 (word_add sptr (word 16))) s = sp16 /\
                read (memory :> bytes128 (word_add sptr (word 32))) s = sp32 /\
                read (memory :> bytes128 (word_add sptr (word 48))) s = sp48 /\
                read (memory :> bytes128 (word_add sptr (word 64))) s = sp64 /\
                read (memory :> bytes128 (word_add sptr (word 80))) s = sp80 /\
                read (memory :> bytes128 (word_add sptr (word 96))) s = sp96 /\
                read (memory :> bytes128 (word_add sptr (word 112))) s = sp112 /\
                read YMM2  s = word_zx (plus:int128) /\
                read YMM4  s = word_zx (xi4:int128) /\
                read YMM7  s = word_zx (xi7:int128) /\
                read YMM8  s = word_zx (xi8:int128) /\
                read YMM9  s = word_zx (word_xor cb0 k0 : int128) /\
                read YMM10 s = word_zx (cb1:int128) /\
                read YMM11 s = word_zx (cb2:int128) /\
                read YMM12 s = word_zx (cb3:int128) /\
                read YMM13 s = word_zx (cb4:int128) /\
                read YMM14 s = word_zx (cb5:int128) /\
                read YMM15 s = word_zx (k0:int128))
           (\s. read RIP s = word (pc + 0x351) /\
                read RDI s = word_add iptr (word 96) /\
                read RSI s = word_add optr (word 96) /\
                read YMM2  s = word_zx (plus:int128) /\
                read YMM15 s = word_zx (k0:int128) /\
                read (memory :> bytes128 optr) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb0 p0 /\
                read (memory :> bytes128 (word_add optr (word 16))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb1 p1 /\
                read (memory :> bytes128 (word_add optr (word 32))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb2 p2 /\
                read (memory :> bytes128 (word_add optr (word 48))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb3 p3 /\
                read (memory :> bytes128 (word_add optr (word 64))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb4 p4 /\
                read (memory :> bytes128 (word_add optr (word 80))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb5 p5)
           (MAYCHANGE [RIP; RDI; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes128 optr;
                       memory :> bytes128 (word_add optr (word 16));
                       memory :> bytes128 (word_add optr (word 32));
                       memory :> bytes128 (word_add optr (word 48));
                       memory :> bytes128 (word_add optr (word 64));
                       memory :> bytes128 (word_add optr (word 80));
                       memory :> bytes128 cbptr;
                       memory :> bytes128 (word_add sptr (word 16))])`,
  MAP_EVERY X_GEN_TAC
   [`optr:int64`; `iptr:int64`; `kptr:int64`; `hptr:int64`; `cbptr:int64`;
    `cptr:int64`; `sptr:int64`;
    `p0:int128`; `p1:int128`; `p2:int128`;
    `p3:int128`; `p4:int128`; `p5:int128`;
    `cb0:int128`; `cb1:int128`; `cb2:int128`;
    `cb3:int128`; `cb4:int128`; `cb5:int128`;
    `k0:int128`; `k1:int128`; `k2:int128`; `k3:int128`;
    `k4:int128`; `k5:int128`; `k6:int128`; `k7:int128`;
    `k8:int128`; `k9:int128`; `k10:int128`;
    `h0:int128`; `h1:int128`; `h3:int128`;
    `h4:int128`; `h6:int128`; `h7:int128`;
    `xi4:int128`; `xi7:int128`; `xi8:int128`;
    `sp16:int128`; `sp32:int128`; `sp48:int128`; `sp64:int128`;
    `sp80:int128`; `sp96:int128`; `sp112:int128`;
    `red:int128`; `plus:int128`;
    `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[(REWRITE_CONV[aesni_gcm_stitched_6x_mc] THENC LENGTH_CONV)
                `LENGTH aesni_gcm_stitched_6x_mc`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n ->
    RULE_ASSUM_TAC(REWRITE_RULE
     [VPSHUFB_BYTEREV_128;
      VPALIGNR_8_SWAP_128_VIA_ZX_256;
      WORD_ZX_ZX_128]) THEN
    X86_STEPS_TAC AESNI_GCM_STITCHED_6X_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [VPSHUFB_BYTEREV_128;
      VPALIGNR_8_SWAP_128_VIA_ZX_256;
      WORD_ZX_ZX_128]) THEN
    GHASH_ABBREV_STEP_TAC)
   (1--168) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[stitched_6x_ct_block; aes128_ctr_lane_m7] THEN
  REWRITE_TAC[AESENC_FIPS197_BRIDGE_ALT; AESENCLAST_FIPS197_BRIDGE_ALT] THEN
  REWRITE_TAC[aes128_cipher; MAP] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256;
           ARITH_LE; ARITH_LT; ARITH;
           WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_XOR_0;
           WORD_REVERSEFIELDS_XOR_128] THEN
  REWRITE_TAC[fips197_final_round; WORD_REVERSEFIELDS_XOR_128;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w) ->
    let lhs,_ = dest_eq w in
    (SPEC_TAC(lhand lhs,`u:int128`) THEN GEN_TAC THEN
     CONV_TAC WORD_BLAST) (asl,w)));;
(* ==================================================================
   M7 EXT3 — extends EXT with 8 more post-state existentials pinning
   YMM0, 1, 3, 4, 5, 6, 7, 8 and the new value at cbptr memory.
   Used by M8 loop inductive step's Case B to discharge the loopinv
   existential block after the 7-instruction tail rotation.
   ================================================================== *)

(* Auxiliary lemma: any int256 value in word_zx form equals word_zx
   of its low 128 bits.  Used to close residuals of shape
     `_metaX = word_zx (word_subword _metaX (0,128))`
   when asl contains `word_zx <inner> = _metaX`. *)

let WORD_SUBWORD_ZX_EQ = prove
 (`!(m:256 word).
      (?(x:128 word). word_zx x = m)
      ==> m = word_zx (word_subword m (0,128) :128 word)`,
  GEN_TAC THEN STRIP_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BLAST);;

let AESNI_GCM_STITCHED_6X_CORRECT_EXT3 = prove
 (`!optr iptr kptr hptr cbptr cptr sptr
      p0 p1 p2 p3 p4 p5
      cb0 cb1 cb2 cb3 cb4 cb5
      k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
      h0 h1 h3 h4 h6 h7
      xi4 xi7 xi8
      sp16 sp32 sp48 sp64 sp80 sp96 sp112
      red plus
      pc.
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (optr,96) /\
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (cbptr,16) /\
      nonoverlapping (word pc,LENGTH aesni_gcm_stitched_6x_mc) (word_add sptr (word 16),16) /\
      nonoverlapping (optr,96) (iptr,16) /\
      nonoverlapping (optr,96) (word_add iptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 48),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add iptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (optr,96) (kptr,16) /\
      nonoverlapping (optr,96) (word_add kptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add kptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add hptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add cptr (word 16),16) /\
      nonoverlapping (optr,96) (word_add cptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 32),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 48),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 64),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 80),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 96),16) /\
      nonoverlapping (optr,96) (word_add sptr (word 112),16) /\
      nonoverlapping (cbptr,16) (iptr,16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 48),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add iptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (cbptr,16) (kptr,16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add kptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add hptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add cptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add cptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 32),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 48),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 64),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 80),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 96),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 112),16) /\
      nonoverlapping (word_add sptr (word 16),16) (iptr,16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 48),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add iptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551488),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551504),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551520),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551536),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551552),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551568),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551584),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 18446744073709551600),16) /\
      nonoverlapping (word_add sptr (word 16),16) (kptr,16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add kptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 18446744073709551584),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 18446744073709551600),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add hptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add cptr (word 16),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add cptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 32),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 48),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 64),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 80),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 96),16) /\
      nonoverlapping (word_add sptr (word 16),16) (word_add sptr (word 112),16) /\
      nonoverlapping (optr,96) (cbptr,16) /\
      nonoverlapping (optr,96) (word_add sptr (word 16),16) /\
      nonoverlapping (cbptr,16) (word_add sptr (word 16),16)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_6x_mc) /\
                read RIP s = word pc /\
                read RDI s = iptr /\
                read RSI s = optr /\
                read RCX s = kptr /\
                read R9  s = hptr /\
                read R8  s = cbptr /\
                read R11 s = cptr /\
                read RSP s = sptr /\
                read (memory :> bytes128 iptr) s = p0 /\
                read (memory :> bytes128 (word_add iptr (word 16))) s = p1 /\
                read (memory :> bytes128 (word_add iptr (word 32))) s = p2 /\
                read (memory :> bytes128 (word_add iptr (word 48))) s = p3 /\
                read (memory :> bytes128 (word_add iptr (word 64))) s = p4 /\
                read (memory :> bytes128 (word_add iptr (word 80))) s = p5 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551488))) s = k0 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551504))) s = k1 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551520))) s = k2 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551536))) s = k3 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551552))) s = k4 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551568))) s = k5 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551584))) s = k6 /\
                read (memory :> bytes128
                  (word_add kptr (word 18446744073709551600))) s = k7 /\
                read (memory :> bytes128 kptr) s = k8 /\
                read (memory :> bytes128 (word_add kptr (word 16))) s = k9 /\
                read (memory :> bytes128 (word_add kptr (word 32))) s = k10 /\
                read (memory :> bytes128
                  (word_add hptr (word 18446744073709551584))) s = h0 /\
                read (memory :> bytes128
                  (word_add hptr (word 18446744073709551600))) s = h1 /\
                read (memory :> bytes128 (word_add hptr (word 16))) s = h3 /\
                read (memory :> bytes128 (word_add hptr (word 32))) s = h4 /\
                read (memory :> bytes128 (word_add hptr (word 64))) s = h6 /\
                read (memory :> bytes128 (word_add hptr (word 80))) s = h7 /\
                read (memory :> bytes128 (word_add cptr (word 16))) s = red /\
                read (memory :> bytes128 (word_add cptr (word 32))) s = plus /\
                read (memory :> bytes128 cbptr) s = cb0 /\
                read (memory :> bytes128 (word_add sptr (word 16))) s = sp16 /\
                read (memory :> bytes128 (word_add sptr (word 32))) s = sp32 /\
                read (memory :> bytes128 (word_add sptr (word 48))) s = sp48 /\
                read (memory :> bytes128 (word_add sptr (word 64))) s = sp64 /\
                read (memory :> bytes128 (word_add sptr (word 80))) s = sp80 /\
                read (memory :> bytes128 (word_add sptr (word 96))) s = sp96 /\
                read (memory :> bytes128 (word_add sptr (word 112))) s = sp112 /\
                read YMM2  s = word_zx (plus:int128) /\
                read YMM4  s = word_zx (xi4:int128) /\
                read YMM7  s = word_zx (xi7:int128) /\
                read YMM8  s = word_zx (xi8:int128) /\
                read YMM9  s = word_zx (word_xor cb0 k0 : int128) /\
                read YMM10 s = word_zx (cb1:int128) /\
                read YMM11 s = word_zx (cb2:int128) /\
                read YMM12 s = word_zx (cb3:int128) /\
                read YMM13 s = word_zx (cb4:int128) /\
                read YMM14 s = word_zx (cb5:int128) /\
                read YMM15 s = word_zx (k0:int128))
           (\s. read RIP s = word (pc + 0x351) /\
                read RDI s = word_add iptr (word 96) /\
                read RSI s = word_add optr (word 96) /\
                read YMM2  s = word_zx (plus:int128) /\
                read YMM15 s = word_zx (k0:int128) /\
                (?(new_cb0:int128) (c0_out:int128) (c5_out:int128)
                  (c6_out:int128) (c7_out:int128) (c3_out:int128)
                  (xi4_out:int128) (xi8_out:int128).
                   read (memory :> bytes128 cbptr) s = new_cb0 /\
                   read YMM1 s = word_zx new_cb0 /\
                   read YMM0 s = word_zx c0_out /\
                   read YMM5 s = word_zx c5_out /\
                   read YMM6 s = word_zx c6_out /\
                   read YMM7 s = word_zx c7_out /\
                   read YMM3 s = word_zx c3_out /\
                   read YMM4 s = word_zx xi4_out /\
                   read YMM8 s = word_zx xi8_out) /\
                read (memory :> bytes128 optr) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb0 p0 /\
                read (memory :> bytes128 (word_add optr (word 16))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb1 p1 /\
                read (memory :> bytes128 (word_add optr (word 32))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb2 p2 /\
                read (memory :> bytes128 (word_add optr (word 48))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb3 p3 /\
                read (memory :> bytes128 (word_add optr (word 64))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb4 p4 /\
                read (memory :> bytes128 (word_add optr (word 80))) s =
                  stitched_6x_ct_block
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] cb5 p5)
           (MAYCHANGE [RIP; RDI; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes128 optr;
                       memory :> bytes128 (word_add optr (word 16));
                       memory :> bytes128 (word_add optr (word 32));
                       memory :> bytes128 (word_add optr (word 48));
                       memory :> bytes128 (word_add optr (word 64));
                       memory :> bytes128 (word_add optr (word 80));
                       memory :> bytes128 cbptr;
                       memory :> bytes128 (word_add sptr (word 16))])`,
  MAP_EVERY X_GEN_TAC
   [`optr:int64`; `iptr:int64`; `kptr:int64`; `hptr:int64`; `cbptr:int64`;
    `cptr:int64`; `sptr:int64`;
    `p0:int128`; `p1:int128`; `p2:int128`;
    `p3:int128`; `p4:int128`; `p5:int128`;
    `cb0:int128`; `cb1:int128`; `cb2:int128`;
    `cb3:int128`; `cb4:int128`; `cb5:int128`;
    `k0:int128`; `k1:int128`; `k2:int128`; `k3:int128`;
    `k4:int128`; `k5:int128`; `k6:int128`; `k7:int128`;
    `k8:int128`; `k9:int128`; `k10:int128`;
    `h0:int128`; `h1:int128`; `h3:int128`;
    `h4:int128`; `h6:int128`; `h7:int128`;
    `xi4:int128`; `xi7:int128`; `xi8:int128`;
    `sp16:int128`; `sp32:int128`; `sp48:int128`; `sp64:int128`;
    `sp80:int128`; `sp96:int128`; `sp112:int128`;
    `red:int128`; `plus:int128`;
    `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[(REWRITE_CONV[aesni_gcm_stitched_6x_mc] THENC LENGTH_CONV)
                `LENGTH aesni_gcm_stitched_6x_mc`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n ->
    RULE_ASSUM_TAC(REWRITE_RULE
     [VPSHUFB_BYTEREV_128;
      VPALIGNR_8_SWAP_128_VIA_ZX_256;
      WORD_ZX_ZX_128]) THEN
    X86_STEPS_TAC AESNI_GCM_STITCHED_6X_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [VPSHUFB_BYTEREV_128;
      VPALIGNR_8_SWAP_128_VIA_ZX_256;
      WORD_ZX_ZX_128]) THEN
    GHASH_ABBREV_STEP_TAC)
   (1--168) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (* Existential block — 8 witnesses.  For cbptr-mem and YMM1, pick the
       value at s168 directly.  For bare-metavar YMM_X, pick
       `word_subword (read YMM_X s168) (0,128)` — the low 128 bits.  After
       ASM_REWRITE folds read-YMM hypotheses, residuals have shape
         `_metaX = word_zx (word_subword _metaX (0,128))`
       which closes via WORD_SUBWORD_ZX_EQ + the asl hyp
       `word_zx <inner> = _metaX`. *)
    EXISTS_TAC `read (memory :> bytes128 cbptr) s168 :int128` THEN
    EXISTS_TAC `word_subword (read YMM0 s168 :int256) (0,128) :int128` THEN
    EXISTS_TAC `word_subword (read YMM5 s168 :int256) (0,128) :int128` THEN
    EXISTS_TAC `word_subword (read YMM6 s168 :int256) (0,128) :int128` THEN
    EXISTS_TAC `word_subword (read YMM7 s168 :int256) (0,128) :int128` THEN
    EXISTS_TAC `word_subword (read YMM3 s168 :int256) (0,128) :int128` THEN
    EXISTS_TAC `word_subword (read YMM4 s168 :int256) (0,128) :int128` THEN
    EXISTS_TAC `word_subword (read YMM8 s168 :int256) (0,128) :int128` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC WORD_SUBWORD_ZX_EQ THEN
    ASM_MESON_TAC[];
    ALL_TAC
  ] THEN
  REWRITE_TAC[stitched_6x_ct_block; aes128_ctr_lane_m7] THEN
  REWRITE_TAC[AESENC_FIPS197_BRIDGE_ALT; AESENCLAST_FIPS197_BRIDGE_ALT] THEN
  REWRITE_TAC[aes128_cipher; MAP] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256;
           ARITH_LE; ARITH_LT; ARITH;
           WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_XOR_0;
           WORD_REVERSEFIELDS_XOR_128] THEN
  REWRITE_TAC[fips197_final_round; WORD_REVERSEFIELDS_XOR_128;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w) ->
    let lhs,_ = dest_eq w in
    (SPEC_TAC(lhand lhs,`u:int128`) THEN GEN_TAC THEN
     CONV_TAC WORD_BLAST) (asl,w)));;
