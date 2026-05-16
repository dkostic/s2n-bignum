(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bulk-loop wrapper for the stitched 6-way AES-128-CTR + GHASH body —       *)
(* recursive-spec edition (Milestone 8, v2).                                 *)
(*                                                                           *)
(* Replaces the M7-EXTN-composed `AESNI_GCM_STITCHED_6X_LOOP_CORRECT`         *)
(* (in `aesni_gcm_stitched_6x_loop.ml`) with an inline simulation of M7's    *)
(* 168-instruction body against the recursive closed-form spec               *)
(* (`x86/proofs/utils/aesni_gcm_stitched_spec.ml`).  See the                 *)
(* recursive-spec-pivot memo (2026-05-16) for the design walkthrough.         *)
(*                                                                           *)
(* The M7 body file is still loaded for                                       *)
(*   - `aesni_gcm_stitched_6x_mc`               (used to share the .Loop6x   *)
(*                                              first-840-byte body via      *)
(*                                              APPEND prefix relations)     *)
(*   - `AESNI_GCM_STITCHED_6X_EXEC`             (stepper exec rule)          *)
(*   - `aes128_ctr_lane_m7`, `stitched_6x_ct_block`                          *)
(*                                              (asm-side per-block CT)      *)
(* but we do NOT compose `AESNI_GCM_STITCHED_6X_CORRECT` (or any of the      *)
(* EXT-N variants) into the inductive step.  Instead the body is simulated   *)
(* via `X86_BIGSTEP_TAC` in this file, with the closed-form spec advancing   *)
(* the loop invariant via `GHASH_COMBINE_STEP` + `BODY_GHASH_STEP_COMPONENTS`.*)
(*                                                                           *)
(* M8-v2 status: the byte list, EXEC rule, helper lemmas, and loop           *)
(* invariant are committed.  The correctness theorem                          *)
(* `AESNI_GCM_STITCHED_LOOP_CORRECT_V2` is currently CHEAT-stubbed; the       *)
(* per-iter inductive step (~2k lines) lands incrementally.  See the         *)
(* matching memo `next-step-m8-rewrite-2026-05-16`.                           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/aesni_gcm_stitched_spec.ml";;
needs "x86/proofs/aesni_gcm_stitched_6x.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code for the bulk loop.                                           *)
(*                                                                           *)
(* This is M7's 198-instruction body (840 bytes [0, 0x3e9)) followed by 10  *)
(* bytes of loop plumbing (subq+jc + 7 SIMD register copies + jmp + ret).   *)
(* Identical to the legacy `aesni_gcm_stitched_6x_loop_mc` byte-for-byte,    *)
(* renamed here so the v2 file stands alone.  Layout:                        *)
(*                                                                           *)
(*     pc + 0x000  .Loop6x body (M7's mc, 198 instructions, 840 bytes)       *)
(*     pc + 0x3e9  subq $6, %rdx                                             *)
(*     pc + 0x3ed  jc .Ldone_exit       (forward to pc + 0x413)              *)
(*     pc + 0x3ef  vpxor %xmm15,%xmm1,%xmm9      (next-iter xmm9)            *)
(*     pc + 0x3f4  vmovdqa %xmm0,%xmm10                                      *)
(*     pc + 0x3f8  vmovdqa %xmm5,%xmm11                                      *)
(*     pc + 0x3fc  vmovdqa %xmm6,%xmm12                                      *)
(*     pc + 0x400  vmovdqa %xmm7,%xmm13                                      *)
(*     pc + 0x404  vmovdqa %xmm3,%xmm14                                      *)
(*     pc + 0x408  vmovdqu 0x20(%rsp),%xmm7                                  *)
(*     pc + 0x40e  jmp pc+0                                                  *)
(*     pc + 0x413  ret                                                       *)
(*                                                                           *)
(* Total 1044 bytes (=0x414).                                                *)
(* ------------------------------------------------------------------------- *)

let aesni_gcm_stitched_loop_mc = define_assert_word_list
  "aesni_gcm_stitched_loop_mc"
  `[
   word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x59; word 0xe0;
   word 0xc5; word 0x89; word 0xfc; word 0xca; word 0xc4; word 0x41;
   word 0x29; word 0xef; word 0xd7; word 0xc4; word 0x41; word 0x21;
   word 0xef; word 0xdf; word 0xc4; word 0xc1; word 0x7a; word 0x7f;
   word 0x08; word 0xc4; word 0xe3; word 0x41; word 0x44; word 0xeb;
   word 0x10; word 0xc4; word 0x41; word 0x19; word 0xef; word 0xe7;
   word 0xc5; word 0xfa; word 0x6f; word 0x51; word 0x90; word 0xc4;
   word 0xe3; word 0x41; word 0x44; word 0xf3; word 0x01; word 0x4d;
   word 0x31; word 0xe4; word 0x4d; word 0x39; word 0xf7; word 0xc4;
   word 0x62; word 0x31; word 0xdc; word 0xca; word 0xc5; word 0xfa;
   word 0x6f; word 0x44; word 0x24; word 0x30; word 0xc4; word 0x41;
   word 0x11; word 0xef; word 0xef; word 0xc4; word 0xe3; word 0x41;
   word 0x44; word 0xcb; word 0x00; word 0xc4; word 0x62; word 0x29;
   word 0xdc; word 0xd2; word 0xc4; word 0x41; word 0x09; word 0xef;
   word 0xf7; word 0x41; word 0x0f; word 0x93; word 0xc4; word 0xc4;
   word 0xe3; word 0x41; word 0x44; word 0xfb; word 0x11; word 0xc4;
   word 0x62; word 0x21; word 0xdc; word 0xda; word 0xc4; word 0xc1;
   word 0x7a; word 0x6f; word 0x59; word 0xf0; word 0x49; word 0xf7;
   word 0xdc; word 0xc4; word 0x62; word 0x19; word 0xdc; word 0xe2;
   word 0xc5; word 0xc9; word 0xef; word 0xf5; word 0xc4; word 0xe3;
   word 0x79; word 0x44; word 0xeb; word 0x00; word 0xc5; word 0x39;
   word 0xef; word 0xc4; word 0xc4; word 0x62; word 0x11; word 0xdc;
   word 0xea; word 0xc5; word 0xf1; word 0xef; word 0xe5; word 0x49;
   word 0x83; word 0xe4; word 0x60; word 0xc5; word 0x7a; word 0x6f;
   word 0x79; word 0xa0; word 0xc4; word 0xe3; word 0x79; word 0x44;
   word 0xcb; word 0x10; word 0xc4; word 0x62; word 0x09; word 0xdc;
   word 0xf2; word 0xc4; word 0xe3; word 0x79; word 0x44; word 0xd3;
   word 0x01; word 0x4f; word 0x8d; word 0x34; word 0x26; word 0xc4;
   word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc5; word 0x39;
   word 0xef; word 0x44; word 0x24; word 0x10; word 0xc4; word 0xe3;
   word 0x79; word 0x44; word 0xdb; word 0x11; word 0xc5; word 0xfa;
   word 0x6f; word 0x44; word 0x24; word 0x40; word 0xc4; word 0x42;
   word 0x29; word 0xdc; word 0xd7; word 0x4d; word 0x0f; word 0x38;
   word 0xf0; word 0x6e; word 0x58; word 0xc4; word 0x42; word 0x21;
   word 0xdc; word 0xdf; word 0x4d; word 0x0f; word 0x38; word 0xf0;
   word 0x66; word 0x50; word 0xc4; word 0x42; word 0x19; word 0xdc;
   word 0xe7; word 0x4c; word 0x89; word 0x6c; word 0x24; word 0x20;
   word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0x4c;
   word 0x89; word 0x64; word 0x24; word 0x28; word 0xc4; word 0xc1;
   word 0x7a; word 0x6f; word 0x69; word 0x10; word 0xc4; word 0x42;
   word 0x09; word 0xdc; word 0xf7; word 0xc5; word 0x7a; word 0x6f;
   word 0x79; word 0xb0; word 0xc5; word 0xc9; word 0xef; word 0xf1;
   word 0xc4; word 0xe3; word 0x79; word 0x44; word 0xcd; word 0x00;
   word 0xc4; word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc5;
   word 0xc9; word 0xef; word 0xf2; word 0xc4; word 0xe3; word 0x79;
   word 0x44; word 0xd5; word 0x10; word 0xc4; word 0x42; word 0x29;
   word 0xdc; word 0xd7; word 0xc5; word 0xc1; word 0xef; word 0xfb;
   word 0xc4; word 0xe3; word 0x79; word 0x44; word 0xdd; word 0x01;
   word 0xc4; word 0x42; word 0x21; word 0xdc; word 0xdf; word 0xc4;
   word 0xe3; word 0x79; word 0x44; word 0xed; word 0x11; word 0xc5;
   word 0xfa; word 0x6f; word 0x44; word 0x24; word 0x50; word 0xc4;
   word 0x42; word 0x19; word 0xdc; word 0xe7; word 0xc4; word 0x42;
   word 0x11; word 0xdc; word 0xef; word 0xc5; word 0xd9; word 0xef;
   word 0xe1; word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x49;
   word 0x20; word 0xc4; word 0x42; word 0x09; word 0xdc; word 0xf7;
   word 0xc5; word 0x7a; word 0x6f; word 0x79; word 0xc0; word 0xc5;
   word 0xc9; word 0xef; word 0xf2; word 0xc4; word 0xe3; word 0x79;
   word 0x44; word 0xd1; word 0x00; word 0xc4; word 0x42; word 0x31;
   word 0xdc; word 0xcf; word 0xc5; word 0xc9; word 0xef; word 0xf3;
   word 0xc4; word 0xe3; word 0x79; word 0x44; word 0xd9; word 0x10;
   word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7; word 0x4d;
   word 0x0f; word 0x38; word 0xf0; word 0x6e; word 0x48; word 0xc5;
   word 0xc1; word 0xef; word 0xfd; word 0xc4; word 0xe3; word 0x79;
   word 0x44; word 0xe9; word 0x01; word 0xc4; word 0x42; word 0x21;
   word 0xdc; word 0xdf; word 0x4d; word 0x0f; word 0x38; word 0xf0;
   word 0x66; word 0x40; word 0xc4; word 0xe3; word 0x79; word 0x44;
   word 0xc9; word 0x11; word 0xc5; word 0xfa; word 0x6f; word 0x44;
   word 0x24; word 0x60; word 0xc4; word 0x42; word 0x19; word 0xdc;
   word 0xe7; word 0x4c; word 0x89; word 0x6c; word 0x24; word 0x30;
   word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0x4c;
   word 0x89; word 0x64; word 0x24; word 0x38; word 0xc5; word 0xd9;
   word 0xef; word 0xe2; word 0xc4; word 0xc1; word 0x7a; word 0x6f;
   word 0x51; word 0x40; word 0xc4; word 0x42; word 0x09; word 0xdc;
   word 0xf7; word 0xc5; word 0x7a; word 0x6f; word 0x79; word 0xd0;
   word 0xc5; word 0xc9; word 0xef; word 0xf3; word 0xc4; word 0xe3;
   word 0x79; word 0x44; word 0xda; word 0x00; word 0xc4; word 0x42;
   word 0x31; word 0xdc; word 0xcf; word 0xc5; word 0xc9; word 0xef;
   word 0xf5; word 0xc4; word 0xe3; word 0x79; word 0x44; word 0xea;
   word 0x10; word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7;
   word 0x4d; word 0x0f; word 0x38; word 0xf0; word 0x6e; word 0x38;
   word 0xc5; word 0xc1; word 0xef; word 0xf9; word 0xc4; word 0xe3;
   word 0x79; word 0x44; word 0xca; word 0x01; word 0xc5; word 0x39;
   word 0xef; word 0x44; word 0x24; word 0x70; word 0xc4; word 0x42;
   word 0x21; word 0xdc; word 0xdf; word 0x4d; word 0x0f; word 0x38;
   word 0xf0; word 0x66; word 0x30; word 0xc4; word 0xe3; word 0x79;
   word 0x44; word 0xd2; word 0x11; word 0xc4; word 0x42; word 0x19;
   word 0xdc; word 0xe7; word 0x4c; word 0x89; word 0x6c; word 0x24;
   word 0x40; word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef;
   word 0x4c; word 0x89; word 0x64; word 0x24; word 0x48; word 0xc5;
   word 0xd9; word 0xef; word 0xe3; word 0xc4; word 0xc1; word 0x7a;
   word 0x6f; word 0x59; word 0x50; word 0xc4; word 0x42; word 0x09;
   word 0xdc; word 0xf7; word 0xc5; word 0x7a; word 0x6f; word 0x79;
   word 0xe0; word 0xc5; word 0xc9; word 0xef; word 0xf5; word 0xc4;
   word 0xe3; word 0x39; word 0x44; word 0xeb; word 0x10; word 0xc4;
   word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc5; word 0xc9;
   word 0xef; word 0xf1; word 0xc4; word 0xe3; word 0x39; word 0x44;
   word 0xcb; word 0x01; word 0xc4; word 0x42; word 0x29; word 0xdc;
   word 0xd7; word 0x4d; word 0x0f; word 0x38; word 0xf0; word 0x6e;
   word 0x28; word 0xc5; word 0xc1; word 0xef; word 0xfa; word 0xc4;
   word 0xe3; word 0x39; word 0x44; word 0xd3; word 0x00; word 0xc4;
   word 0x42; word 0x21; word 0xdc; word 0xdf; word 0x4d; word 0x0f;
   word 0x38; word 0xf0; word 0x66; word 0x20; word 0xc4; word 0x63;
   word 0x39; word 0x44; word 0xc3; word 0x11; word 0xc4; word 0x42;
   word 0x19; word 0xdc; word 0xe7; word 0x4c; word 0x89; word 0x6c;
   word 0x24; word 0x50; word 0xc4; word 0x42; word 0x11; word 0xdc;
   word 0xef; word 0x4c; word 0x89; word 0x64; word 0x24; word 0x58;
   word 0xc5; word 0xc9; word 0xef; word 0xf5; word 0xc4; word 0x42;
   word 0x09; word 0xdc; word 0xf7; word 0xc5; word 0xc9; word 0xef;
   word 0xf1; word 0xc5; word 0x7a; word 0x6f; word 0x79; word 0xf0;
   word 0xc5; word 0xd1; word 0x73; word 0xfe; word 0x08; word 0xc5;
   word 0xd9; word 0xef; word 0xe2; word 0xc4; word 0xc1; word 0x7a;
   word 0x6f; word 0x5b; word 0x10; word 0xc4; word 0x42; word 0x31;
   word 0xdc; word 0xcf; word 0xc4; word 0xc1; word 0x41; word 0xef;
   word 0xf8; word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7;
   word 0xc5; word 0xd9; word 0xef; word 0xe5; word 0x4d; word 0x0f;
   word 0x38; word 0xf0; word 0x6e; word 0x18; word 0xc4; word 0x42;
   word 0x21; word 0xdc; word 0xdf; word 0x4d; word 0x0f; word 0x38;
   word 0xf0; word 0x66; word 0x10; word 0xc4; word 0xe3; word 0x59;
   word 0x0f; word 0xc4; word 0x08; word 0xc4; word 0xe3; word 0x59;
   word 0x44; word 0xe3; word 0x10; word 0x4c; word 0x89; word 0x6c;
   word 0x24; word 0x60; word 0xc4; word 0x42; word 0x19; word 0xdc;
   word 0xe7; word 0x4c; word 0x89; word 0x64; word 0x24; word 0x68;
   word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0xc5;
   word 0xfa; word 0x6f; word 0x09; word 0xc4; word 0x42; word 0x09;
   word 0xdc; word 0xf7; word 0xc4; word 0x62; word 0x31; word 0xdc;
   word 0xc9; word 0xc5; word 0x7a; word 0x6f; word 0x79; word 0x10;
   word 0xc4; word 0x62; word 0x29; word 0xdc; word 0xd1; word 0xc5;
   word 0xc9; word 0x73; word 0xde; word 0x08; word 0xc4; word 0x62;
   word 0x21; word 0xdc; word 0xd9; word 0xc5; word 0xc1; word 0xef;
   word 0xfe; word 0xc4; word 0x62; word 0x19; word 0xdc; word 0xe1;
   word 0xc5; word 0xd9; word 0xef; word 0xe0; word 0x4d; word 0x0f;
   word 0x38; word 0xf0; word 0x6e; word 0x08; word 0xc4; word 0x62;
   word 0x11; word 0xdc; word 0xe9; word 0x4d; word 0x0f; word 0x38;
   word 0xf0; word 0x26; word 0xc4; word 0x62; word 0x09; word 0xdc;
   word 0xf1; word 0xc5; word 0xfa; word 0x6f; word 0x49; word 0x20;
   word 0xc4; word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc5;
   word 0xfa; word 0x7f; word 0x7c; word 0x24; word 0x10; word 0xc4;
   word 0x63; word 0x59; word 0x0f; word 0xc4; word 0x08; word 0xc4;
   word 0x42; word 0x29; word 0xdc; word 0xd7; word 0xc4; word 0xe3;
   word 0x59; word 0x44; word 0xe3; word 0x10; word 0xc5; word 0xf1;
   word 0xef; word 0x17; word 0xc4; word 0x42; word 0x21; word 0xdc;
   word 0xdf; word 0xc5; word 0xf1; word 0xef; word 0x47; word 0x10;
   word 0xc4; word 0x42; word 0x19; word 0xdc; word 0xe7; word 0xc5;
   word 0xf1; word 0xef; word 0x6f; word 0x20; word 0xc4; word 0x42;
   word 0x11; word 0xdc; word 0xef; word 0xc5; word 0xf1; word 0xef;
   word 0x77; word 0x30; word 0xc4; word 0x42; word 0x09; word 0xdc;
   word 0xf7; word 0xc5; word 0xf1; word 0xef; word 0x7f; word 0x40;
   word 0xc5; word 0xf1; word 0xef; word 0x5f; word 0x50; word 0xc4;
   word 0xc1; word 0x7a; word 0x6f; word 0x08; word 0xc4; word 0x62;
   word 0x31; word 0xdd; word 0xca; word 0xc4; word 0xc1; word 0x7a;
   word 0x6f; word 0x53; word 0x20; word 0xc4; word 0x62; word 0x29;
   word 0xdd; word 0xd0; word 0xc5; word 0xf1; word 0xfc; word 0xc2;
   word 0x4c; word 0x89; word 0x6c; word 0x24; word 0x70; word 0x48;
   word 0x8d; word 0x7f; word 0x60; word 0xc4; word 0x62; word 0x21;
   word 0xdd; word 0xdd; word 0xc5; word 0xf9; word 0xfc; word 0xea;
   word 0x4c; word 0x89; word 0x64; word 0x24; word 0x78; word 0x48;
   word 0x8d; word 0x76; word 0x60; word 0xc5; word 0x7a; word 0x6f;
   word 0x79; word 0x80; word 0xc4; word 0x62; word 0x19; word 0xdd;
   word 0xe6; word 0xc5; word 0xd1; word 0xfc; word 0xf2; word 0xc4;
   word 0x62; word 0x11; word 0xdd; word 0xef; word 0xc5; word 0xc9;
   word 0xfc; word 0xfa; word 0xc4; word 0x62; word 0x09; word 0xdd;
   word 0xf3; word 0xc5; word 0xc1; word 0xfc; word 0xda; word 0xc5;
   word 0x7a; word 0x7f; word 0x4e; word 0xa0; word 0xc5; word 0x7a;
   word 0x7f; word 0x56; word 0xb0; word 0xc5; word 0x7a; word 0x7f;
   word 0x5e; word 0xc0; word 0xc5; word 0x7a; word 0x7f; word 0x66;
   word 0xd0; word 0xc5; word 0x7a; word 0x7f; word 0x6e; word 0xe0;
   word 0xc5; word 0x7a; word 0x7f; word 0x76; word 0xf0; word 0x48;
   word 0x83; word 0xea; word 0x06; word 0x72; word 0x24; word 0xc4;
   word 0x41; word 0x71; word 0xef; word 0xcf; word 0xc5; word 0x79;
   word 0x6f; word 0xd0; word 0xc5; word 0x79; word 0x6f; word 0xdd;
   word 0xc5; word 0x79; word 0x6f; word 0xe6; word 0xc5; word 0x79;
   word 0x6f; word 0xef; word 0xc5; word 0x79; word 0x6f; word 0xf3;
   word 0xc5; word 0xfa; word 0x6f; word 0x7c; word 0x24; word 0x20;
   word 0xe9; word 0xed; word 0xfb; word 0xff; word 0xff; word 0xc3]:byte list`
  [
   0xc4; 0xc1; 0x7a; 0x6f; 0x59; 0xe0; 0xc5; 0x89; 0xfc; 0xca; 0xc4; 0x41;
   0x29; 0xef; 0xd7; 0xc4; 0x41; 0x21; 0xef; 0xdf; 0xc4; 0xc1; 0x7a; 0x7f;
   0x08; 0xc4; 0xe3; 0x41; 0x44; 0xeb; 0x10; 0xc4; 0x41; 0x19; 0xef; 0xe7;
   0xc5; 0xfa; 0x6f; 0x51; 0x90; 0xc4; 0xe3; 0x41; 0x44; 0xf3; 0x01; 0x4d;
   0x31; 0xe4; 0x4d; 0x39; 0xf7; 0xc4; 0x62; 0x31; 0xdc; 0xca; 0xc5; 0xfa;
   0x6f; 0x44; 0x24; 0x30; 0xc4; 0x41; 0x11; 0xef; 0xef; 0xc4; 0xe3; 0x41;
   0x44; 0xcb; 0x00; 0xc4; 0x62; 0x29; 0xdc; 0xd2; 0xc4; 0x41; 0x09; 0xef;
   0xf7; 0x41; 0x0f; 0x93; 0xc4; 0xc4; 0xe3; 0x41; 0x44; 0xfb; 0x11; 0xc4;
   0x62; 0x21; 0xdc; 0xda; 0xc4; 0xc1; 0x7a; 0x6f; 0x59; 0xf0; 0x49; 0xf7;
   0xdc; 0xc4; 0x62; 0x19; 0xdc; 0xe2; 0xc5; 0xc9; 0xef; 0xf5; 0xc4; 0xe3;
   0x79; 0x44; 0xeb; 0x00; 0xc5; 0x39; 0xef; 0xc4; 0xc4; 0x62; 0x11; 0xdc;
   0xea; 0xc5; 0xf1; 0xef; 0xe5; 0x49; 0x83; 0xe4; 0x60; 0xc5; 0x7a; 0x6f;
   0x79; 0xa0; 0xc4; 0xe3; 0x79; 0x44; 0xcb; 0x10; 0xc4; 0x62; 0x09; 0xdc;
   0xf2; 0xc4; 0xe3; 0x79; 0x44; 0xd3; 0x01; 0x4f; 0x8d; 0x34; 0x26; 0xc4;
   0x42; 0x31; 0xdc; 0xcf; 0xc5; 0x39; 0xef; 0x44; 0x24; 0x10; 0xc4; 0xe3;
   0x79; 0x44; 0xdb; 0x11; 0xc5; 0xfa; 0x6f; 0x44; 0x24; 0x40; 0xc4; 0x42;
   0x29; 0xdc; 0xd7; 0x4d; 0x0f; 0x38; 0xf0; 0x6e; 0x58; 0xc4; 0x42; 0x21;
   0xdc; 0xdf; 0x4d; 0x0f; 0x38; 0xf0; 0x66; 0x50; 0xc4; 0x42; 0x19; 0xdc;
   0xe7; 0x4c; 0x89; 0x6c; 0x24; 0x20; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0x4c;
   0x89; 0x64; 0x24; 0x28; 0xc4; 0xc1; 0x7a; 0x6f; 0x69; 0x10; 0xc4; 0x42;
   0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x79; 0xb0; 0xc5; 0xc9; 0xef; 0xf1;
   0xc4; 0xe3; 0x79; 0x44; 0xcd; 0x00; 0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc5;
   0xc9; 0xef; 0xf2; 0xc4; 0xe3; 0x79; 0x44; 0xd5; 0x10; 0xc4; 0x42; 0x29;
   0xdc; 0xd7; 0xc5; 0xc1; 0xef; 0xfb; 0xc4; 0xe3; 0x79; 0x44; 0xdd; 0x01;
   0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4; 0xe3; 0x79; 0x44; 0xed; 0x11; 0xc5;
   0xfa; 0x6f; 0x44; 0x24; 0x50; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42;
   0x11; 0xdc; 0xef; 0xc5; 0xd9; 0xef; 0xe1; 0xc4; 0xc1; 0x7a; 0x6f; 0x49;
   0x20; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x79; 0xc0; 0xc5;
   0xc9; 0xef; 0xf2; 0xc4; 0xe3; 0x79; 0x44; 0xd1; 0x00; 0xc4; 0x42; 0x31;
   0xdc; 0xcf; 0xc5; 0xc9; 0xef; 0xf3; 0xc4; 0xe3; 0x79; 0x44; 0xd9; 0x10;
   0xc4; 0x42; 0x29; 0xdc; 0xd7; 0x4d; 0x0f; 0x38; 0xf0; 0x6e; 0x48; 0xc5;
   0xc1; 0xef; 0xfd; 0xc4; 0xe3; 0x79; 0x44; 0xe9; 0x01; 0xc4; 0x42; 0x21;
   0xdc; 0xdf; 0x4d; 0x0f; 0x38; 0xf0; 0x66; 0x40; 0xc4; 0xe3; 0x79; 0x44;
   0xc9; 0x11; 0xc5; 0xfa; 0x6f; 0x44; 0x24; 0x60; 0xc4; 0x42; 0x19; 0xdc;
   0xe7; 0x4c; 0x89; 0x6c; 0x24; 0x30; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0x4c;
   0x89; 0x64; 0x24; 0x38; 0xc5; 0xd9; 0xef; 0xe2; 0xc4; 0xc1; 0x7a; 0x6f;
   0x51; 0x40; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x79; 0xd0;
   0xc5; 0xc9; 0xef; 0xf3; 0xc4; 0xe3; 0x79; 0x44; 0xda; 0x00; 0xc4; 0x42;
   0x31; 0xdc; 0xcf; 0xc5; 0xc9; 0xef; 0xf5; 0xc4; 0xe3; 0x79; 0x44; 0xea;
   0x10; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0x4d; 0x0f; 0x38; 0xf0; 0x6e; 0x38;
   0xc5; 0xc1; 0xef; 0xf9; 0xc4; 0xe3; 0x79; 0x44; 0xca; 0x01; 0xc5; 0x39;
   0xef; 0x44; 0x24; 0x70; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0x4d; 0x0f; 0x38;
   0xf0; 0x66; 0x30; 0xc4; 0xe3; 0x79; 0x44; 0xd2; 0x11; 0xc4; 0x42; 0x19;
   0xdc; 0xe7; 0x4c; 0x89; 0x6c; 0x24; 0x40; 0xc4; 0x42; 0x11; 0xdc; 0xef;
   0x4c; 0x89; 0x64; 0x24; 0x48; 0xc5; 0xd9; 0xef; 0xe3; 0xc4; 0xc1; 0x7a;
   0x6f; 0x59; 0x50; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x79;
   0xe0; 0xc5; 0xc9; 0xef; 0xf5; 0xc4; 0xe3; 0x39; 0x44; 0xeb; 0x10; 0xc4;
   0x42; 0x31; 0xdc; 0xcf; 0xc5; 0xc9; 0xef; 0xf1; 0xc4; 0xe3; 0x39; 0x44;
   0xcb; 0x01; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0x4d; 0x0f; 0x38; 0xf0; 0x6e;
   0x28; 0xc5; 0xc1; 0xef; 0xfa; 0xc4; 0xe3; 0x39; 0x44; 0xd3; 0x00; 0xc4;
   0x42; 0x21; 0xdc; 0xdf; 0x4d; 0x0f; 0x38; 0xf0; 0x66; 0x20; 0xc4; 0x63;
   0x39; 0x44; 0xc3; 0x11; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0x4c; 0x89; 0x6c;
   0x24; 0x50; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0x4c; 0x89; 0x64; 0x24; 0x58;
   0xc5; 0xc9; 0xef; 0xf5; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0xc9; 0xef;
   0xf1; 0xc5; 0x7a; 0x6f; 0x79; 0xf0; 0xc5; 0xd1; 0x73; 0xfe; 0x08; 0xc5;
   0xd9; 0xef; 0xe2; 0xc4; 0xc1; 0x7a; 0x6f; 0x5b; 0x10; 0xc4; 0x42; 0x31;
   0xdc; 0xcf; 0xc4; 0xc1; 0x41; 0xef; 0xf8; 0xc4; 0x42; 0x29; 0xdc; 0xd7;
   0xc5; 0xd9; 0xef; 0xe5; 0x4d; 0x0f; 0x38; 0xf0; 0x6e; 0x18; 0xc4; 0x42;
   0x21; 0xdc; 0xdf; 0x4d; 0x0f; 0x38; 0xf0; 0x66; 0x10; 0xc4; 0xe3; 0x59;
   0x0f; 0xc4; 0x08; 0xc4; 0xe3; 0x59; 0x44; 0xe3; 0x10; 0x4c; 0x89; 0x6c;
   0x24; 0x60; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0x4c; 0x89; 0x64; 0x24; 0x68;
   0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc5; 0xfa; 0x6f; 0x09; 0xc4; 0x42; 0x09;
   0xdc; 0xf7; 0xc4; 0x62; 0x31; 0xdc; 0xc9; 0xc5; 0x7a; 0x6f; 0x79; 0x10;
   0xc4; 0x62; 0x29; 0xdc; 0xd1; 0xc5; 0xc9; 0x73; 0xde; 0x08; 0xc4; 0x62;
   0x21; 0xdc; 0xd9; 0xc5; 0xc1; 0xef; 0xfe; 0xc4; 0x62; 0x19; 0xdc; 0xe1;
   0xc5; 0xd9; 0xef; 0xe0; 0x4d; 0x0f; 0x38; 0xf0; 0x6e; 0x08; 0xc4; 0x62;
   0x11; 0xdc; 0xe9; 0x4d; 0x0f; 0x38; 0xf0; 0x26; 0xc4; 0x62; 0x09; 0xdc;
   0xf1; 0xc5; 0xfa; 0x6f; 0x49; 0x20; 0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc5;
   0xfa; 0x7f; 0x7c; 0x24; 0x10; 0xc4; 0x63; 0x59; 0x0f; 0xc4; 0x08; 0xc4;
   0x42; 0x29; 0xdc; 0xd7; 0xc4; 0xe3; 0x59; 0x44; 0xe3; 0x10; 0xc5; 0xf1;
   0xef; 0x17; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc5; 0xf1; 0xef; 0x47; 0x10;
   0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc5; 0xf1; 0xef; 0x6f; 0x20; 0xc4; 0x42;
   0x11; 0xdc; 0xef; 0xc5; 0xf1; 0xef; 0x77; 0x30; 0xc4; 0x42; 0x09; 0xdc;
   0xf7; 0xc5; 0xf1; 0xef; 0x7f; 0x40; 0xc5; 0xf1; 0xef; 0x5f; 0x50; 0xc4;
   0xc1; 0x7a; 0x6f; 0x08; 0xc4; 0x62; 0x31; 0xdd; 0xca; 0xc4; 0xc1; 0x7a;
   0x6f; 0x53; 0x20; 0xc4; 0x62; 0x29; 0xdd; 0xd0; 0xc5; 0xf1; 0xfc; 0xc2;
   0x4c; 0x89; 0x6c; 0x24; 0x70; 0x48; 0x8d; 0x7f; 0x60; 0xc4; 0x62; 0x21;
   0xdd; 0xdd; 0xc5; 0xf9; 0xfc; 0xea; 0x4c; 0x89; 0x64; 0x24; 0x78; 0x48;
   0x8d; 0x76; 0x60; 0xc5; 0x7a; 0x6f; 0x79; 0x80; 0xc4; 0x62; 0x19; 0xdd;
   0xe6; 0xc5; 0xd1; 0xfc; 0xf2; 0xc4; 0x62; 0x11; 0xdd; 0xef; 0xc5; 0xc9;
   0xfc; 0xfa; 0xc4; 0x62; 0x09; 0xdd; 0xf3; 0xc5; 0xc1; 0xfc; 0xda; 0xc5;
   0x7a; 0x7f; 0x4e; 0xa0; 0xc5; 0x7a; 0x7f; 0x56; 0xb0; 0xc5; 0x7a; 0x7f;
   0x5e; 0xc0; 0xc5; 0x7a; 0x7f; 0x66; 0xd0; 0xc5; 0x7a; 0x7f; 0x6e; 0xe0;
   0xc5; 0x7a; 0x7f; 0x76; 0xf0; 0x48; 0x83; 0xea; 0x06; 0x72; 0x24; 0xc4;
   0x41; 0x71; 0xef; 0xcf; 0xc5; 0x79; 0x6f; 0xd0; 0xc5; 0x79; 0x6f; 0xdd;
   0xc5; 0x79; 0x6f; 0xe6; 0xc5; 0x79; 0x6f; 0xef; 0xc5; 0x79; 0x6f; 0xf3;
   0xc5; 0xfa; 0x6f; 0x7c; 0x24; 0x20; 0xe9; 0xed; 0xfb; 0xff; 0xff; 0xc3];;

let AESNI_GCM_STITCHED_LOOP_EXEC =
  X86_MK_CORE_EXEC_RULE aesni_gcm_stitched_loop_mc;;

(* ------------------------------------------------------------------------- *)
(* Sanity: byte length matches the expected 1044-byte loop layout.           *)
(* ------------------------------------------------------------------------- *)

let LENGTH_AESNI_GCM_STITCHED_LOOP_MC = prove
 (`LENGTH aesni_gcm_stitched_loop_mc = 1044`,
  REWRITE_TAC[(REWRITE_CONV[aesni_gcm_stitched_loop_mc] THENC LENGTH_CONV)
                `LENGTH aesni_gcm_stitched_loop_mc`]);;

(* ------------------------------------------------------------------------- *)
(* Prefix relation between M7's body bytes and the v2 loop bytes.            *)
(*                                                                           *)
(* The first 840 bytes of `aesni_gcm_stitched_loop_mc` are byte-for-byte     *)
(* identical to `BUTLAST aesni_gcm_stitched_6x_mc` (M7's body minus its     *)
(* trailing `ret`).  Exhibiting the decomposition as an APPEND equality      *)
(* lets the inductive step's stepper machinery discharge the                 *)
(* `bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_6x_mc)`            *)
(* side-condition the M7 EXEC rule needs.                                    *)
(* ------------------------------------------------------------------------- *)

let AESNI_GCM_STITCHED_LOOP_MC_APPEND = prove
 (`aesni_gcm_stitched_loop_mc =
   APPEND (BUTLAST aesni_gcm_stitched_6x_mc)
          [word 0x48; word 0x83; word 0xea; word 0x06;
           word 0x72; word 0x24; word 0xc4; word 0x41;
           word 0x71; word 0xef; word 0xcf; word 0xc5;
           word 0x79; word 0x6f; word 0xd0; word 0xc5;
           word 0x79; word 0x6f; word 0xdd; word 0xc5;
           word 0x79; word 0x6f; word 0xe6; word 0xc5;
           word 0x79; word 0x6f; word 0xef; word 0xc5;
           word 0x79; word 0x6f; word 0xf3; word 0xc5;
           word 0xfa; word 0x6f; word 0x7c; word 0x24;
           word 0x20; word 0xe9; word 0xed; word 0xfb;
           word 0xff; word 0xff; word 0xc3]`,
  REWRITE_TAC[aesni_gcm_stitched_loop_mc; aesni_gcm_stitched_6x_mc;
              BUTLAST_CLAUSES; APPEND; NOT_CONS_NIL]);;

let BYTES_LOADED_LOOP_IMPLIES_M7_BUTLAST = prove
 (`!s pc.
     bytes_loaded s (word pc) aesni_gcm_stitched_loop_mc
     ==> bytes_loaded s (word pc)
           (BUTLAST aesni_gcm_stitched_6x_mc)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[AESNI_GCM_STITCHED_LOOP_MC_APPEND]) THEN
  SIMP_TAC[bytes_loaded_append]);;

(* Companion: `BUTLAST loop_mc` also extends over M7's body.  This is the    *)
(* form X86_BIGSTEP_TAC needs inside the inductive-step proof, since the     *)
(* outer CORRECT statement uses BUTLAST-of-loop-mc (X86_MK_CORE_EXEC_RULE    *)
(* strips the trailing ret).                                                 *)

let BUTLAST_LOOP_MC_APPEND = prove
 (`BUTLAST aesni_gcm_stitched_loop_mc =
   APPEND (BUTLAST aesni_gcm_stitched_6x_mc)
          [word 0x48; word 0x83; word 0xea; word 0x06;
           word 0x72; word 0x24; word 0xc4; word 0x41;
           word 0x71; word 0xef; word 0xcf; word 0xc5;
           word 0x79; word 0x6f; word 0xd0; word 0xc5;
           word 0x79; word 0x6f; word 0xdd; word 0xc5;
           word 0x79; word 0x6f; word 0xe6; word 0xc5;
           word 0x79; word 0x6f; word 0xef; word 0xc5;
           word 0x79; word 0x6f; word 0xf3; word 0xc5;
           word 0xfa; word 0x6f; word 0x7c; word 0x24;
           word 0x20; word 0xe9; word 0xed; word 0xfb;
           word 0xff; word 0xff]`,
  REWRITE_TAC[aesni_gcm_stitched_loop_mc; aesni_gcm_stitched_6x_mc;
              BUTLAST_CLAUSES; APPEND; NOT_CONS_NIL]);;

let BYTES_LOADED_LOOP_BUTLAST_IMPLIES_M7_BUTLAST = prove
 (`!s pc.
     bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_loop_mc)
     ==> bytes_loaded s (word pc)
           (BUTLAST aesni_gcm_stitched_6x_mc)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BUTLAST_LOOP_MC_APPEND]) THEN
  SIMP_TAC[bytes_loaded_append]);;

(* ------------------------------------------------------------------------- *)
(* Loop-control arithmetic.                                                  *)
(*                                                                           *)
(* At loop-top iteration i, RDX holds                                         *)
(*   word_sub (word (6 * iter_count)) (word (6 + 6 * i))                     *)
(* and the body's tail does `subq $6, %rdx; jc .Ldone_exit`.  These three    *)
(* lemmas — RDX advance for mid/last iter, and the CF-vs-iter-count          *)
(* equivalence — are the arithmetic backbone of the                          *)
(* ENSURES_WHILE_UP2-generated case split on `i + 1 = iter_count`.           *)
(* ------------------------------------------------------------------------- *)

let LOOP_RDX_STEP_MID = prove
 (`!(i:num) (iter_count:num).
     word_sub (word_sub (word (6 * iter_count)) (word (6 + 6 * i))) (word 6)
       = (word_sub (word (6 * iter_count)) (word (6 + 6 * (i + 1))):int64)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE
    `!a b c:int64. word_sub (word_sub a b) c = word_sub a (word_add b c)`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let LOOP_RDX_STEP_LAST = prove
 (`!(i:num) (iter_count:num).
     i + 1 = iter_count
     ==> word_sub (word_sub (word (6 * iter_count)) (word (6 + 6 * i))) (word 6)
       = (word_sub (word (6 * iter_count)) (word (6 + 6 * iter_count)):int64)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LOOP_RDX_STEP_MID]);;

let LOOP_CF_EQUIV = prove
 (`!(i:num) (iter_count:num).
     i < iter_count /\ 6 * iter_count < 2 EXP 64
     ==> (val (word_sub (word (6 * iter_count)) (word (6 + 6 * i)):int64) < 6
          <=> i + 1 = iter_count)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(6 * iter_count) MOD 2 EXP 64 = 6 * iter_count`
   SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(6 + 6 * i) MOD 2 EXP 64 = 6 + 6 * i`
   SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `6 * iter_count + 2 EXP 64 - (6 + 6 * i) =
                (6 * iter_count - (6 + 6 * i)) + 2 EXP 64`
   SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_REFL; ADD_CLAUSES; MOD_MOD_REFL] THEN
  SUBGOAL_THEN `(6 * iter_count - (6 + 6 * i)) MOD 2 EXP 64 =
                6 * iter_count - (6 + 6 * i)`
   SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Per-iter sub-region nonoverlap.  The outer precondition gives             *)
(*   `nonoverlapping (optr, 16*6*iter_count) X`                              *)
(* for each readable X; the inductive step needs                              *)
(*   `nonoverlapping (word_add optr (word (96*i)), 96) X`                    *)
(* for `i < iter_count`.  These five helpers cover the standard cases.       *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_SUBREGION_LEFT = prove
 (`!(base:int64) (n:num) (off:num) (len:num) (x:int64) (lx:num).
      off + len <= n
      ==> nonoverlapping (base, n) (x, lx)
      ==> nonoverlapping (word_add base (word off), len) (x, lx)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
  EXISTS_TAC `val (base:int64):num` THEN EXISTS_TAC `n:num` THEN
  EXISTS_TAC `val (x:int64):num` THEN EXISTS_TAC `lx:num` THEN
  REPEAT CONJ_TAC THENL [
    MP_TAC(ASSUME `nonoverlapping (base:int64, n) (x, lx)`) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN SIMP_TAC[];
    REWRITE_TAC[contained_modulo] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `off + i:num` THEN CONJ_TAC THENL [
      ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_ASSOC]];
    REWRITE_TAC[contained_modulo] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[CONG_REFL]
  ]);;

let NONOVERLAPPING_SUBREGION_RIGHT = prove
 (`!(base:int64) (n:num) (off:num) (len:num) (x:int64) (lx:num).
      off + len <= n
      ==> nonoverlapping (x, lx) (base, n)
      ==> nonoverlapping (x, lx) (word_add base (word off), len)`,
  MESON_TAC[NONOVERLAPPING_SUBREGION_LEFT; NONOVERLAPPING_SYM]);;

let NONOVERLAPPING_SUBREGION_BOTH = prove
 (`!(base1:int64) (n1:num) (off1:num) (len1:num)
     (base2:int64) (n2:num) (off2:num) (len2:num).
      off1 + len1 <= n1 /\ off2 + len2 <= n2 /\
      nonoverlapping (base1, n1) (base2, n2)
      ==> nonoverlapping (word_add base1 (word off1), len1)
                         (word_add base2 (word off2), len2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`base2:int64`; `n2:num`; `off2:num`; `len2:num`;
                  `word_add (base1:int64) (word off1)`; `len1:num`]
                 NONOVERLAPPING_SUBREGION_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC (ISPECL [`base1:int64`; `n1:num`; `off1:num`; `len1:num`;
                  `base2:int64`; `n2:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
  ASM_REWRITE_TAC[]);;

let NONOVERLAPPING_SUBREGION_SAME_BASE = prove
 (`!(base:int64) (n:num) (off1:num) (len1:num) (off2:num) (len2:num).
      off1 + len1 <= off2 /\ off2 + len2 <= n /\ n <= 2 EXP 64
      ==> nonoverlapping (word_add base (word off1):int64, len1)
                         (word_add base (word off2):int64, len2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo;
              NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[GSYM ADD_ASSOC; CONG_ADD_LCANCEL_EQ]) THEN
  SUBGOAL_THEN `off1 + i = off2 + j` MP_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let NONOVERLAPPING_SUBREGION_SAME_BASE_SYM = prove
 (`!(base:int64) (n:num) (off1:num) (len1:num) (off2:num) (len2:num).
      off2 + len2 <= off1 /\ off1 + len1 <= n /\ n <= 2 EXP 64
      ==> nonoverlapping (word_add base (word off1):int64, len1)
                         (word_add base (word off2):int64, len2)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
  MATCH_MP_TAC NONOVERLAPPING_SUBREGION_SAME_BASE THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pointer-equality identities used for loopinv_v2 closure in Case A/B of    *)
(* the inductive step.  Both reduce `word_add (iter_ptr) (word 96)` (where  *)
(* iter_ptr = word_add x (word (96*i))) to the target form.                  *)
(* ------------------------------------------------------------------------- *)

let CASEA_PTR_EQ = prove
 (`!(x:int64) (i:num) (iter_count:num).
     i + 1 = iter_count
     ==> word_add (word_add x (word (96 * i))) (word 96) =
         word_add x (word (96 * iter_count))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let CASEB_PTR_EQ = prove
 (`!(x:int64) (i:num).
     word_add (word_add x (word (96 * i))) (word 96) =
     word_add x (word (96 * (i + 1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Loop invariant — recursive-spec edition.                                   *)
(*                                                                           *)
(* At iteration i (0..iter_count), the invariant pins register/memory state  *)
(* at the loop-top label `pc + 0`, with the GHASH carry expressed as a       *)
(* closed-form `ghash_at` of the input plaintext.  The 4-tuple ghash         *)
(* residue (xi4, xi7, xi8, sp16) is held by an existential whose             *)
(* `ghash_combine = ghash_at i` invariant ties it back to the spec-side      *)
(* recursive function.                                                        *)
(*                                                                           *)
(* Differences from the legacy `loopinv` (in aesni_gcm_stitched_6x_loop.ml): *)
(*                                                                           *)
(*   - Counter pinning uses `cb_at icb (6*i+k)` directly — no                *)
(*     `counter_fn` ghost.  The simd16 tail rotations between iterations    *)
(*     advance the YMM9..14 registers, and the spec's `cb_at` recurrence    *)
(*     evaluates them by induction.                                          *)
(*                                                                           *)
(*   - Plaintext / ciphertext-prefix pinning uses `pt_at` / `ct_at` — no    *)
(*     `p_fn` / `counter_fn` ghosts; they're functions of (pt_in, ks, icb).  *)
(*                                                                           *)
(*   - Stash-region (sp+32..sp+112) holds `bswap_ct_at` of CT blocks         *)
(*     6*(i-2)..6*(i-2)+5 when 2 <= i (off-by-TWO mapping), vacuous else.   *)
(*                                                                           *)
(*   - Ghash carry is a 4-existential `?xi4 xi7 xi8 sp16` whose              *)
(*     `ghash_combine xi4 xi8 sp16 = ghash_at h tag0 ks icb pt_in i`        *)
(*     ties the asm registers back to the closed-form running ghash.         *)
(*     M9's tail's first two vpxors collapse this 4-tuple to ghash_at        *)
(*     so the M9 contract sees no existentials.                              *)
(* ------------------------------------------------------------------------- *)

let pt_preserved_v2 = new_definition
 `pt_preserved_v2 (iter_count:num) (iptr_base:int64) (s:x86state)
                  (pt_in:byte list) <=>
    !j. j < 6 * iter_count
        ==> read (memory :> bytes128
                    (word_add iptr_base (word (16 * j)))) s = pt_at pt_in j`;;

let ct_preserved_v2 = new_definition
 `ct_preserved_v2 (i:num) (optr_base:int64) (s:x86state)
                  (ks:int128 list) (icb:int128) (pt_in:byte list) <=>
    !j. j < 6 * i
        ==> read (memory :> bytes128
                    (word_add optr_base (word (16 * j)))) s =
            ct_at ks icb pt_in j`;;

let stashed_ct_preserved_v2 = new_definition
 `stashed_ct_preserved_v2 (i:num) (sptr:int64) (s:x86state)
                          (ks:int128 list) (icb:int128) (pt_in:byte list) <=>
    2 <= i
    ==> !k. k < 6
            ==> read (memory :> bytes128
                        (word_add sptr (word (32 + 16 * k)))) s =
                bswap_ct_at ks icb pt_in (6 * (i - 2) + (5 - k))`;;

let loopinv_common_v2 = new_definition
 `loopinv_common_v2
    (iptr_base:int64) (optr_base:int64) (kptr:int64) (hptr:int64)
    (cbptr:int64) (cptr:int64) (sptr:int64)
    (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
    (k5:int128) (k6:int128) (k7:int128) (k8:int128) (k9:int128) (k10:int128)
    (h0:int128) (h1:int128) (h3:int128) (h4:int128) (h6:int128) (h7:int128)
    (red:int128) (plus:int128)
    (icb:int128) (pt_in:byte list)
    (r14_orig:int64) (r15_orig:int64)
    (iter_count:num) (i:num) (s:x86state) <=>
      pt_preserved_v2 iter_count iptr_base s pt_in /\
      ct_preserved_v2 i optr_base s
        [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] icb pt_in /\
      stashed_ct_preserved_v2 i sptr s
        [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] icb pt_in /\
      read RDI s = word_add iptr_base (word (96 * i)) /\
      read RSI s = word_add optr_base (word (96 * i)) /\
      read RDX s = word_sub (word (6 * iter_count)) (word (6 + 6 * i)) /\
      read RCX s = kptr /\
      read R9  s = hptr /\
      read R8  s = cbptr /\
      read R11 s = cptr /\
      read R15 s = r15_orig /\
      read RSP s = sptr /\
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
      read YMM2  s = (word_zx (plus:int128) : int256) /\
      read YMM15 s = (word_zx (k0:int128) : int256)`;;

let loopinv_v2 = new_definition
 `loopinv_v2
    (iptr_base:int64) (optr_base:int64) (kptr:int64) (hptr:int64)
    (cbptr:int64) (cptr:int64) (sptr:int64)
    (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
    (k5:int128) (k6:int128) (k7:int128) (k8:int128) (k9:int128) (k10:int128)
    (h0:int128) (h1:int128) (h3:int128) (h4:int128) (h6:int128) (h7:int128)
    (red:int128) (plus:int128)
    (h:int128) (tag0:int128)
    (icb:int128) (pt_in:byte list)
    (r14_orig:int64) (r15_orig:int64)
    (iter_count:num) (i:num) (s:x86state) <=>
      loopinv_common_v2 iptr_base optr_base kptr hptr cbptr cptr sptr
                        k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
                        h0 h1 h3 h4 h6 h7
                        red plus
                        icb pt_in
                        r14_orig r15_orig
                        iter_count i s /\
      (i < iter_count
       ==> (?(xi4:int128) (xi7:int128) (xi8:int128) (sp16:int128).
              read YMM4  s = (word_zx xi4 : int256) /\
              read YMM7  s = (word_zx xi7 : int256) /\
              read YMM8  s = (word_zx xi8 : int256) /\
              read YMM9  s = (word_zx
                (word_xor (cb_at icb (6 * i)) k0 : int128) : int256) /\
              read YMM10 s = (word_zx (cb_at icb (6 * i + 1)) : int256) /\
              read YMM11 s = (word_zx (cb_at icb (6 * i + 2)) : int256) /\
              read YMM12 s = (word_zx (cb_at icb (6 * i + 3)) : int256) /\
              read YMM13 s = (word_zx (cb_at icb (6 * i + 4)) : int256) /\
              read YMM14 s = (word_zx (cb_at icb (6 * i + 5)) : int256) /\
              read (memory :> bytes128 cbptr) s = cb_at icb (6 * i) /\
              read (memory :> bytes128 (word_add sptr (word 16))) s = sp16 /\
              ghash_combine xi4 xi8 sp16 =
                ghash_at h tag0
                  [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] icb pt_in i))`;;

(* ========================================================================= *)
(* Correctness of the bulk loop (Milestone 8, v2).                            *)
(*                                                                           *)
(* Given                                                                      *)
(*   - iter_count >= 1 iterations of the .Loop6x body,                       *)
(*   - the recursive-spec preconditions on h / tag0 / icb / pt_in,           *)
(*   - the geometric tie `r14_orig + 192 = optr` and global bound            *)
(*     `val r14_orig + 96*iter_count <= val r15_orig`,                       *)
(*   - the usual AES/GHASH register / memory disjointness antecedent,        *)
(*   - the entry-time `loopinv_v2 iter_count 0`,                              *)
(* the loop runs iter_count iterations and exits through `ret` with          *)
(* `loopinv_v2 iter_count iter_count` holding.                                *)
(*                                                                           *)
(* The MAYCHANGE frame matches the legacy v1 wrapper (RIP/RDI/RSI/RDX +      *)
(* R12-R14 + ZMM0..15 + flags + events + bytes(optr,16*6*iter_count) +       *)
(* bytes(cbptr,16) + bytes(sp+16,16) + bytes(sp+32,96)).                      *)
(*                                                                           *)
(* Currently CHEAT-stubbed; the per-iter inductive step (~2k lines) lands    *)
(* incrementally.                                                             *)
(* ========================================================================= *)

let AESNI_GCM_STITCHED_LOOP_CORRECT_V2 = prove
 (`!(optr:int64) (iptr:int64) (kptr:int64) (hptr:int64)
      (cbptr:int64) (cptr:int64) (sptr:int64)
      (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
      (k5:int128) (k6:int128) (k7:int128) (k8:int128)
      (k9:int128) (k10:int128)
      (h0:int128) (h1:int128) (h3:int128) (h4:int128) (h6:int128) (h7:int128)
      (red:int128) (plus:int128)
      (h:int128) (tag0:int128)
      (icb:int128) (pt_in:byte list)
      (r14_orig:int64) (r15_orig:int64)
      (iter_count:num) (pc:num).
      1 <= iter_count /\
      16 * 6 * iter_count < 2 EXP 64 /\
      val r14_orig + 96 * iter_count <= val r15_orig /\
      word_add r14_orig (word 192) = optr /\
      LENGTH pt_in = 16 * 6 * iter_count /\
      nonoverlapping (word pc:int64,LENGTH aesni_gcm_stitched_loop_mc) (optr, 16 * 6 * iter_count) /\
      nonoverlapping (word pc:int64,LENGTH aesni_gcm_stitched_loop_mc) ((cbptr:int64), 16) /\
      nonoverlapping (word pc:int64,LENGTH aesni_gcm_stitched_loop_mc) (word_add sptr (word 16), 16) /\
      nonoverlapping (word pc:int64,LENGTH aesni_gcm_stitched_loop_mc) (word_add sptr (word 32), 96) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (iptr, 16 * 6 * iter_count) /\
      nonoverlapping ((cbptr:int64), 16) (iptr, 16 * 6 * iter_count) /\
      nonoverlapping (word_add sptr (word 16), 16) (iptr, 16 * 6 * iter_count) /\
      nonoverlapping (iptr, 16 * 6 * iter_count) (word_add sptr (word 32), 96) /\
      nonoverlapping (optr, 16 * 6 * iter_count) ((cbptr:int64), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 16), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 32), 96) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 16), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551488), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551504), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551520), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551536), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551552), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551568), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551584), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 18446744073709551600), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (kptr, 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 16), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add kptr (word 32), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add hptr (word 18446744073709551584), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add hptr (word 18446744073709551600), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add hptr (word 16), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add hptr (word 32), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add hptr (word 64), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add hptr (word 80), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add cptr (word 16), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add cptr (word 32), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551488), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551504), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551520), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551536), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551552), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551568), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551584), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 18446744073709551600), 16) /\
      nonoverlapping ((cbptr:int64), 16) (kptr, 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 16), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add kptr (word 32), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add hptr (word 18446744073709551584), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add hptr (word 18446744073709551600), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add hptr (word 16), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add hptr (word 32), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add hptr (word 64), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add hptr (word 80), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add cptr (word 16), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add cptr (word 32), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551488), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551504), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551520), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551536), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551552), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551568), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551584), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 18446744073709551600), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (kptr, 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 16), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add kptr (word 32), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add hptr (word 18446744073709551584), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add hptr (word 18446744073709551600), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add hptr (word 16), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add hptr (word 32), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add hptr (word 64), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add hptr (word 80), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add cptr (word 16), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add cptr (word 32), 16) /\
      nonoverlapping (word_add kptr (word 18446744073709551488), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 18446744073709551504), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 18446744073709551520), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 18446744073709551536), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 18446744073709551552), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 18446744073709551568), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 18446744073709551584), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 18446744073709551600), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (kptr, 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 16), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add kptr (word 32), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add hptr (word 18446744073709551584), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add hptr (word 18446744073709551600), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add hptr (word 16), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add hptr (word 32), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add hptr (word 64), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add hptr (word 80), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add cptr (word 16), 16) (word_add sptr (word 32), 96) /\
      nonoverlapping (word_add cptr (word 32), 16) (word_add sptr (word 32), 96)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_loop_mc) /\
                read RIP s = word pc /\
                loopinv_v2 iptr optr kptr hptr cbptr cptr sptr
                           k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
                           h0 h1 h3 h4 h6 h7
                           red plus
                           h tag0
                           icb pt_in
                           r14_orig r15_orig
                           iter_count 0 s)
           (\s. read RIP s = word (pc + 0x413) /\
                loopinv_v2 iptr optr kptr hptr cbptr cptr sptr
                           k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
                           h0 h1 h3 h4 h6 h7
                           red plus
                           h tag0
                           icb pt_in
                           r14_orig r15_orig
                           iter_count iter_count s)
           (MAYCHANGE [RIP; RDI; RSI; RDX; R12; R13; R14] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (optr,16 * 6 * iter_count);
                       memory :> bytes ((cbptr:int64),16);
                       memory :> bytes (word_add sptr (word 16),16);
                       memory :> bytes (word_add sptr (word 32),96)])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_UP2_TAC `iter_count:num` `pc + 0x0` `pc + 0x413`
   `\(i:num) (s:x86state).
       loopinv_v2 iptr optr kptr hptr cbptr cptr sptr
                  k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
                  h0 h1 h3 h4 h6 h7
                  red plus
                  h tag0
                  icb pt_in
                  r14_orig r15_orig
                  iter_count i s /\
       bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_loop_mc)` THEN
  REPEAT CONJ_TAC THENL
   [(* iter_count is non-zero *)
    ASM_ARITH_TAC;

    (* Base case — entry state IS loopinv_v2 ... 0; postcond at pc+0 also
       requires the BUTLAST bytes_loaded fact (already in asl).  After
       reducing `word (96 * 0) = word 0`, the entry-time `loopinv_v2 ... 0`
       discharges directly. *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0];

    (* Inductive step — preamble for body simulation.

       Strategy: simulate the 168-instruction body inline against the
       recursive spec.  The legacy M8 wrapper composes M7's EXT4 theorem;
       this v2 wrapper does the simulation locally so the loopinv carries
       closed-form GHASH state via `ghash_combine xi4 xi8 sp16 = ghash_at
       h tag0 ks icb pt_in i` rather than per-iter existential ghosts.

       The preamble below stages the per-iter scaffolding: a 96*i+96 <=
       16*6*iter_count bound, ABBREV's for `iter_iptr` and `iter_optr`,
       ABBREV's for the 6 plaintext blocks `p0..p5` (= `pt_at pt_in
       (6*i+k)` via pt_preserved_v2), 6 cb_at counters renamed `cb0..cb5`,
       and the standard ~50 per-iter nonoverlapping clauses derived from
       the outer bulk via NONOVERLAPPING_SUBREGION_{LEFT,RIGHT,BOTH}.

       Body simulation follows the M7-EXT4 recipe (lines 1793--1810 of
       aesni_gcm_stitched_6x.ml): per-step
         RULE_ASSUM_TAC(REWRITE_RULE[VPSHUFB_BYTEREV_128;
                                     VPALIGNR_8_SWAP_128_VIA_ZX_256;
                                     WORD_ZX_ZX_128]) THEN
         X86_STEPS_TAC AESNI_GCM_STITCHED_LOOP_EXEC [n] THEN
         SIMD_SIMPLIFY_TAC[] THEN ... THEN GHASH_ABBREV_STEP_TAC
       for n = 1..168, with abbrev-then-step for the YMM7 stash propagation
       per [[m8-caseB-ymm7-drop]].  Use BYTES_LOADED_LOOP_BUTLAST_IMPLIES_
       M7_BUTLAST to bridge the M7 stepper exec rule's bytes_loaded
       precondition to the v2 loop mc.

       After body simulation, step subq+jc (steps 169--170 against the v2
       loop mc), apply LOOP_CF_EQUIV, ASM_CASES_TAC `i + 1 = iter_count`
       and split into Case A (jc taken, exit) and Case B (jc not taken,
       middle-iter tail).  In Case B reconstruct `loopinv_v2 (i + 1)` by
       picking 4-tuple existential witnesses (xi4_asm, xi7_asm, xi8_asm,
       sp16_asm) directly from the asm post-state and discharging the
       `ghash_combine xi4_asm xi8_asm sp16_asm = ghash_at ... (i+1)`
       conjunct via GHASH_COMBINE_STEP + the asm-side ring-algebra
       equation `xi4_asm XOR xi8_asm XOR sp16_asm = polyval_reduce_prop3
       (karatsuba_batch_6x ...)` (proved locally from the asm reduction
       shape — the load-bearing fragment that the prior 5 EXT-N
       enrichments each re-proved). *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[loopinv_v2; loopinv_common_v2] THEN
    ENSURES_INIT_TAC "s0" THEN
    (* Pull the 4-tuple existential block (gated by i < iter_count) into
       scope as named variables xi4 / xi7 / xi8 / sp16. *)
    FIRST_X_ASSUM (fun th ->
      let c = concl th in
      if is_imp c && is_exists (snd (dest_imp c))
      then STRIP_ASSUME_TAC (MATCH_MP th (ASSUME `i < iter_count`))
      else NO_TAC) THEN
    (* Per-iter pointer abbreviations.  Match the legacy v1 names so the
       NONOVERLAPPING_SUBREGION_* helpers can fire by EXPAND. *)
    ABBREV_TAC `iter_iptr:int64 = word_add iptr (word (96 * i))` THEN
    ABBREV_TAC `iter_optr:int64 = word_add optr (word (96 * i))` THEN
    (* Per-iter geometric bound — drives every NONOVERLAPPING_SUBREGION
       discharge below. *)
    SUBGOAL_THEN `96 * i + 96 <= 16 * 6 * iter_count` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    (* Reduce LENGTH aesni_gcm_stitched_loop_mc to 1044 in asl so that
       NONOVERLAPPING_TAC and NONOVERLAPPING_SUBREGION* see a numeric
       bound. *)
    RULE_ASSUM_TAC(REWRITE_RULE
       [(REWRITE_CONV[aesni_gcm_stitched_loop_mc] THENC LENGTH_CONV)
          `LENGTH aesni_gcm_stitched_loop_mc`]) THEN
    (* ---------------------------------------------------------------- *)
    (* Per-iter nonoverlapping clauses.  Standard set lifted from legacy *)
    (* v1 M8 wrapper (aesni_gcm_stitched_6x_loop.ml ~lines 1466-1834).   *)
    (* Drives X86_STEPS_TAC's NONOVERLAPPING_DRIVERS during body         *)
    (* simulation, plus MAYCHANGE subsumption at Case A/B closure.       *)
    (* Each clause discharges via the corresponding outer-bulk hyp +     *)
    (* NONOVERLAPPING_SUBREGION_{LEFT,RIGHT,BOTH} + the per-iter         *)
    (* `96 * i + 96 <= 16 * 6 * iter_count` bound established just       *)
    (* above.                                                            *)
    (* ---------------------------------------------------------------- *)
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551488):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551488):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551504):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551504):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551520):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551520):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551536):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551536):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551552):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551552):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551568):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551568):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551584):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551584):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 18446744073709551600):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 18446744073709551600):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (kptr:int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `kptr:int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 16):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 16):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add kptr (word 32):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add kptr (word 32):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add hptr (word 18446744073709551584):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add hptr (word 18446744073709551584):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add hptr (word 18446744073709551600):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add hptr (word 18446744073709551600):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add hptr (word 16):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add hptr (word 16):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add hptr (word 32):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add hptr (word 32):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add hptr (word 64):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add hptr (word 64):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add hptr (word 80):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add hptr (word 80):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add cptr (word 16):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add cptr (word 16):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add cptr (word 32):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add cptr (word 32):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (cbptr:int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `cbptr:int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 16):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 16):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (cbptr:int64, 16) (iter_iptr:int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `cbptr:int64`; `16:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add sptr (word 16):int64, 16) (iter_iptr:int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 16):int64`; `16:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (iter_iptr:int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN EXPAND_TAC "iter_iptr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `iptr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`]
                    NONOVERLAPPING_SUBREGION_BOTH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (iter_optr:int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word pc:int64`; `1044:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (word_add iter_optr (word 16):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 16:num`; `16:num`;
                     `word pc:int64`; `1044:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (word_add iter_optr (word 32):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 32:num`; `16:num`;
                     `word pc:int64`; `1044:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (word_add iter_optr (word 48):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 48:num`; `16:num`;
                     `word pc:int64`; `1044:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (word_add iter_optr (word 64):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 64:num`; `16:num`;
                     `word pc:int64`; `1044:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (word_add iter_optr (word 80):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 80:num`; `16:num`;
                     `word pc:int64`; `1044:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (iter_optr:int64, 16)` ASSUME_TAC THENL [
      MP_TAC(ISPECL [`iter_optr:int64`; `96:num`; `0:num`; `16:num`;
                     `word pc:int64`; `1044:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 1044) (word_add iter_optr (word 0):int64, 16)` ASSUME_TAC THENL [
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 32):int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 32):int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_iptr:int64, 96) (word_add sptr (word 32):int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 32):int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add iter_iptr (word 16):int64, 16) (word_add sptr (word 32):int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i + 16:num`; `16:num`;
                     `word_add sptr (word 32):int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add iter_iptr (word 32):int64, 16) (word_add sptr (word 32):int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i + 32:num`; `16:num`;
                     `word_add sptr (word 32):int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add iter_iptr (word 48):int64, 16) (word_add sptr (word 32):int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i + 48:num`; `16:num`;
                     `word_add sptr (word 32):int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add iter_iptr (word 64):int64, 16) (word_add sptr (word 32):int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i + 64:num`; `16:num`;
                     `word_add sptr (word 32):int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add iter_iptr (word 80):int64, 16) (word_add sptr (word 32):int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_iptr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`iptr:int64`; `16 * 6 * iter_count:num`; `96 * i + 80:num`; `16:num`;
                     `word_add sptr (word 32):int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    (* ---------------------------------------------------------------- *)
    (* Stash ABBREVs.  Bind cstash0..cstash5 = read sp+(32+16k) s0 for   *)
    (* k=0..5 — 6 ghost int128 values for the body's pre-MOVBE-write     *)
    (* read of the previous-iter's stash slots.  These are absolute       *)
    (* (no spec link required during simulation): the stepper propagates *)
    (* them through register-only steps via ASSUMPTION_STATE_UPDATE so   *)
    (* the early-body VPSHUFB / VMOVDQU stash reads see named values.    *)
    (* The spec-side bridge to stashed_ct_preserved_v2 (gated by 2 <= i) *)
    (* is derived locally at iter close where ct_preserved_v2 (i+1)      *)
    (* closure consumes the bswap_ct_at form.                            *)
    (* ---------------------------------------------------------------- *)
    ABBREV_TAC `cstash0:int128 = read (memory :> bytes128 (word_add sptr (word 32))) s0` THEN
    ABBREV_TAC `cstash1:int128 = read (memory :> bytes128 (word_add sptr (word 48))) s0` THEN
    ABBREV_TAC `cstash2:int128 = read (memory :> bytes128 (word_add sptr (word 64))) s0` THEN
    ABBREV_TAC `cstash3:int128 = read (memory :> bytes128 (word_add sptr (word 80))) s0` THEN
    ABBREV_TAC `cstash4:int128 = read (memory :> bytes128 (word_add sptr (word 96))) s0` THEN
    ABBREV_TAC `cstash5:int128 = read (memory :> bytes128 (word_add sptr (word 112))) s0` THEN
    (* ---------------------------------------------------------------- *)
    (* Plaintext ABBREVs.  Bind p0..p5 = pt_at pt_in (6*i+k) for k=0..5  *)
    (* and pre-derive the corresponding bytes128 reads at iter_iptr+16k  *)
    (* via pt_preserved_v2.  This gives ASSUMPTION_STATE_UPDATE named    *)
    (* values to fold during body simulation, and supplies the spec-side *)
    (* link `pt_at pt_in (6*i+k) = p_k` that the body's ct_preserved_v2  *)
    (* discharge needs at iter close.                                    *)
    (* ---------------------------------------------------------------- *)
    ABBREV_TAC `p0:int128 = pt_at pt_in (6 * i + 0)` THEN
    ABBREV_TAC `p1:int128 = pt_at pt_in (6 * i + 1)` THEN
    ABBREV_TAC `p2:int128 = pt_at pt_in (6 * i + 2)` THEN
    ABBREV_TAC `p3:int128 = pt_at pt_in (6 * i + 3)` THEN
    ABBREV_TAC `p4:int128 = pt_at pt_in (6 * i + 4)` THEN
    ABBREV_TAC `p5:int128 = pt_at pt_in (6 * i + 5)` THEN
    SUBGOAL_THEN
      `read (memory :> bytes128 (word_add iter_iptr (word 0))) s0 = (p0:int128) /\
       read (memory :> bytes128 (word_add iter_iptr (word 16))) s0 = (p1:int128) /\
       read (memory :> bytes128 (word_add iter_iptr (word 32))) s0 = (p2:int128) /\
       read (memory :> bytes128 (word_add iter_iptr (word 48))) s0 = (p3:int128) /\
       read (memory :> bytes128 (word_add iter_iptr (word 64))) s0 = (p4:int128) /\
       read (memory :> bytes128 (word_add iter_iptr (word 80))) s0 = (p5:int128)`
      STRIP_ASSUME_TAC THENL [
      SUBGOAL_THEN
        `6 * i + 0 < 6 * iter_count /\ 6 * i + 1 < 6 * iter_count /\
         6 * i + 2 < 6 * iter_count /\ 6 * i + 3 < 6 * iter_count /\
         6 * i + 4 < 6 * iter_count /\ 6 * i + 5 < 6 * iter_count`
        STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC (REWRITE_RULE[pt_preserved_v2]
                (ASSUME `pt_preserved_v2 iter_count iptr s0 pt_in`)) THEN
      DISCH_THEN (fun th ->
        let s0 = SPEC `6 * i + 0` th in
        let s1 = SPEC `6 * i + 1` th in
        let s2 = SPEC `6 * i + 2` th in
        let s3 = SPEC `6 * i + 3` th in
        let s4 = SPEC `6 * i + 4` th in
        let s5 = SPEC `6 * i + 5` th in
        MP_TAC s5 THEN MP_TAC s4 THEN MP_TAC s3 THEN
        MP_TAC s2 THEN MP_TAC s1 THEN MP_TAC s0) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `16 * (6 * i + 0) = 96 * i + 0`;
                  ARITH_RULE `16 * (6 * i + 1) = 96 * i + 16`;
                  ARITH_RULE `16 * (6 * i + 2) = 96 * i + 32`;
                  ARITH_RULE `16 * (6 * i + 3) = 96 * i + 48`;
                  ARITH_RULE `16 * (6 * i + 4) = 96 * i + 64`;
                  ARITH_RULE `16 * (6 * i + 5) = 96 * i + 80`] THEN
      EXPAND_TAC "iter_iptr" THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    (* ---------------------------------------------------------------- *)
    (* Pre-step PC normalisation.  ENSURES_WHILE_UP2_TAC stamps          *)
    (* `read RIP s0 = word (pc + 0)` into asl; the stepper's X86_CONV    *)
    (* needs the reduced form `read RIP s0 = word pc` to match the EXEC *)
    (* rule's `pc + i` antecedent at i = 0.  ADD_CLAUSES collapses       *)
    (* `pc + 0` to `pc` in asl so step 1 fires.  Subsequent steps emit  *)
    (* clean PC arithmetic and need no further normalisation.            *)
    (* ---------------------------------------------------------------- *)
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    (* ---------------------------------------------------------------- *)
    (* Body simulation 1..168.  Same per-step recipe as M7 EXT4 (lines  *)
    (* 1793-1804 of aesni_gcm_stitched_6x.ml): RULE_ASSUM_TAC the SIMD  *)
    (* fold lemmas, X86_STEPS_TAC the single instruction n,             *)
    (* SIMD_SIMPLIFY_TAC, fold again, then GHASH_ABBREV_STEP_TAC names  *)
    (* the ghash-state register's new value.  The same machine code as  *)
    (* M7 EXT4 (these are bytes 0..839 of aesni_gcm_stitched_loop_mc =  *)
    (* BUTLAST aesni_gcm_stitched_6x_mc), so the per-step pattern        *)
    (* transfers verbatim.  168 steps complete in ~80s wall-clock.       *)
    (* ---------------------------------------------------------------- *)
    MAP_EVERY (fun n ->
      RULE_ASSUM_TAC(REWRITE_RULE
       [VPSHUFB_BYTEREV_128;
        VPALIGNR_8_SWAP_128_VIA_ZX_256;
        WORD_ZX_ZX_128]) THEN
      X86_STEPS_TAC AESNI_GCM_STITCHED_LOOP_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [VPSHUFB_BYTEREV_128;
        VPALIGNR_8_SWAP_128_VIA_ZX_256;
        WORD_ZX_ZX_128]) THEN
      GHASH_ABBREV_STEP_TAC)
     (1--198) THEN
    (* ---------------------------------------------------------------- *)
    (* Subq + jc.  The body's tail does `subq $6, %rdx; jc .Ldone_exit`. *)
    (* Without the SIMD recipe (these are GPR ops), we step them         *)
    (* directly.  After step 200 RIP is symbolically                     *)
    (*   read RIP s200 =                                                 *)
    (*     if val(rdx) < 6 then pc+0x413 else pc+0x3ef.                  *)
    (* LOOP_CF_EQUIV folds val(rdx) < 6 into i+1 = iter_count.            *)
    (* ---------------------------------------------------------------- *)
    X86_STEPS_TAC AESNI_GCM_STITCHED_LOOP_EXEC [199; 200] THEN
    MP_TAC(SPECL [`i:num`; `iter_count:num`] LOOP_CF_EQUIV) THEN
    ANTS_TAC THENL [
      CONJ_TAC THENL [
        FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `16 * 6 * iter_count < 2 EXP 64` THEN ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
      `val (word_sub (word (6 * iter_count)) (word (6 + 6 * i)):int64) < 6 <=>
       i + 1 = iter_count`]) THEN
    ASM_CASES_TAC `i + 1 = iter_count` THENL [
      (* Case A: last iter (jc taken, exit at pc+0x413).  Close
         loopinv_v2 iter_count; only loopinv_common_v2 conjuncts apply
         since i+1 = iter_count makes the `i + 1 < iter_count` guard
         false, dropping the 4-tuple existential. *)
      ASM_REWRITE_TAC[LT_REFL] THEN
      (* Substitute iter_iptr/iter_optr back to word_add iptr/optr (word
         (96*i)) form so MONOTONE_MAYCHANGE matches its automated
         pattern. *)
      FIRST_X_ASSUM (fun th ->
        if string_of_term (concl th) =
             "word_add optr (word (96 * i)) = iter_optr"
        then SUBST_ALL_TAC (SYM th) else NO_TAC) THEN
      FIRST_X_ASSUM (fun th ->
        if string_of_term (concl th) =
             "word_add iptr (word (96 * i)) = iter_iptr"
        then SUBST_ALL_TAC (SYM th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
        (* pt_preserved_v2 iter_count — frame from s0 via memory orthogonality
           (the asm body writes to (optr,16*6*iter_count), cbptr, sp+16,
           sp+32..120 — none overlap iptr's region).  Same recipe as v1's
           PT_FRAME_TAC (line 625 of aesni_gcm_stitched_6x_loop.ml). *)
        REWRITE_TAC[pt_preserved_v2] THEN
        REPEAT STRIP_TAC THEN
        MP_TAC (REWRITE_RULE[pt_preserved_v2]
                  (ASSUME `pt_preserved_v2 iter_count iptr s0 pt_in`)) THEN
        DISCH_THEN (MP_TAC o SPEC `j:num`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN
        FIRST_X_ASSUM (fun th ->
          let c = concl th in
          try
            let _, args = strip_comb c in
            let n = List.length args in
            if n >= 2 &&
               is_var (List.nth args (n-2)) &&
               fst(dest_var (List.nth args (n-2))) = "s0" &&
               is_var (List.nth args (n-1)) &&
               fst(dest_var (List.nth args (n-1))) = "s200"
            then MP_TAC th else NO_TAC
          with _ -> NO_TAC) THEN
        REWRITE_TAC[MAYCHANGE; SEQ_ID; seq; ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
        REPEAT STRIP_TAC THEN
        REPEAT (FIRST_X_ASSUM (fun th ->
          try
            let c = concl th in
            if not (is_eq c) then NO_TAC else
            let lhs, rhs = dest_eq c in
            let is_write_term t =
              try name_of (fst (strip_comb t)) = "write" with _ -> false in
            let is_fresh_state t =
              is_var t &&
              (let n = fst (dest_var t) in
               String.length n >= 2 &&
               String.get n 0 = 's' &&
               String.get n 1 <> '0') in
            if (is_write_term lhs && is_fresh_state rhs) ||
               (is_fresh_state lhs && is_fresh_state rhs) ||
               (is_fresh_state lhs && is_write_term rhs)
            then SUBST_ALL_TAC (SYM th) else NO_TAC
          with _ -> NO_TAC)) THEN
        READ_OVER_WRITE_ORTHOGONAL_TAC;
        (* ct_preserved_v2 iter_count — combine ct_preserved_v2 i optr s0
           framing for j<6*i (memory orthogonality) with the asm body's 6
           per-block writes for j ∈ {6*i..6*i+5} (decoded via the FIPS-197
           bridge to ct_at).  Same recipe as M7 EXT4's per-iter ct closure
           (lines 1873-1888 of aesni_gcm_stitched_6x.ml), specialised to
           the v2 spec form. *)
        REWRITE_TAC[ct_preserved_v2] THEN
        REPEAT STRIP_TAC THEN
        ASM_CASES_TAC `j < 6 * i` THENL [
          (* j < 6*i: preserve from ct_preserved_v2 i s0 via memory
             orthogonality.  optr+16j is in (optr,16*6*iter_count) but is
             not in any of the 6 per-slot writes (optr+96*i+16k) for
             k=0..5 (which are the asm body's actual MAYCHANGE region). *)
          MP_TAC (REWRITE_RULE[ct_preserved_v2]
                    (ASSUME `ct_preserved_v2 i optr s0
                               [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10]
                               icb pt_in`)) THEN
          DISCH_THEN (MP_TAC o SPEC `j:num`) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN (SUBST1_TAC o SYM) THEN
          FIRST_X_ASSUM (fun th ->
            let c = concl th in
            try
              let _, args = strip_comb c in
              let n = List.length args in
              if n >= 2 &&
                 is_var (List.nth args (n-2)) &&
                 fst(dest_var (List.nth args (n-2))) = "s0" &&
                 is_var (List.nth args (n-1)) &&
                 fst(dest_var (List.nth args (n-1))) = "s200"
              then MP_TAC th else NO_TAC
            with _ -> NO_TAC) THEN
          REWRITE_TAC[MAYCHANGE; SEQ_ID; seq; ASSIGNS_THM;
                      LEFT_IMP_EXISTS_THM] THEN
          REPEAT STRIP_TAC THEN
          REPEAT (FIRST_X_ASSUM (fun th ->
            try
              let c = concl th in
              if not (is_eq c) then NO_TAC else
              let lhs, rhs = dest_eq c in
              let is_write_term t =
                try name_of (fst (strip_comb t)) = "write" with _ -> false in
              let is_fresh_state t =
                is_var t &&
                (let n = fst (dest_var t) in
                 String.length n >= 2 &&
                 String.get n 0 = 's' &&
                 String.get n 1 <> '0') in
              if (is_write_term lhs && is_fresh_state rhs) ||
                 (is_fresh_state lhs && is_fresh_state rhs) ||
                 (is_fresh_state lhs && is_write_term rhs)
              then SUBST_ALL_TAC (SYM th) else NO_TAC
            with _ -> NO_TAC)) THEN
          READ_OVER_WRITE_ORTHOGONAL_TAC;

          (* j ∈ {6*i..6*i+5}: 6-way split, then per-k discharge via the
             body's asm-side write at optr+(96*i+16*k) folded against ct_at
             via the FIPS-197 bridge. *)
          SUBGOAL_THEN
            `j = 6 * i \/ j = 6 * i + 1 \/ j = 6 * i + 2 \/
             j = 6 * i + 3 \/ j = 6 * i + 4 \/ j = 6 * i + 5`
            STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `~(j < 6 * i)` THEN
            UNDISCH_TAC `j < 6 * iter_count` THEN
            UNDISCH_TAC `(i:num) + 1 = iter_count` THEN
            ARITH_TAC;
            ALL_TAC] THENL
          [(* k = 0: the SUBST_ALL produces `j = 6 * i`, so
              `16 * j` becomes `16 * 6 * i` (no `+ 0` after HOL reduction).
              Match ABBREV `pt_at pt_in (6 * i) = p0` similarly. *)
            POP_ASSUM (fun th -> ASSUME_TAC th THEN SUBST_ALL_TAC th) THEN
            REWRITE_TAC[ARITH_RULE `16 * 6 * i = 96 * i`] THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[ct_at] THEN
            REWRITE_TAC[AESENC_FIPS197_BRIDGE_ALT;
                        AESENCLAST_FIPS197_BRIDGE_ALT] THEN
            REWRITE_TAC[aes128_cipher; MAP] THEN
            CONV_TAC(DEPTH_CONV let_CONV) THEN
            CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
            SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256;
                     ARITH_LE; ARITH_LT; ARITH;
                     WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_XOR_0;
                     WORD_REVERSEFIELDS_XOR_128] THEN
            REWRITE_TAC[fips197_final_round; WORD_REVERSEFIELDS_XOR_128;
                        WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
            FIRST_X_ASSUM (fun th ->
              if string_of_term (concl th) = "pt_at pt_in (6 * i) = p0"
              then SUBST1_TAC (SYM th) else NO_TAC) THEN
            (fun (asl, w) ->
              let lhs, _ = dest_eq w in
              SPEC_TAC(lhand lhs, `u:int128`) (asl, w)) THEN
            GEN_TAC THEN
            CONV_TAC WORD_BLAST] @
          (map (fun k ->
            let off = 16 * k in
            POP_ASSUM (fun th -> ASSUME_TAC th THEN SUBST_ALL_TAC th) THEN
            REWRITE_TAC[ARITH_RULE
              (mk_eq
                (mk_binop `(*):num->num->num`
                          (mk_small_numeral 16)
                          (mk_binop `(+):num->num->num`
                                    (mk_binop `(*):num->num->num`
                                              (mk_small_numeral 6)
                                              `i:num`)
                                    (mk_small_numeral k)),
                 mk_binop `(+):num->num->num`
                          (mk_binop `(*):num->num->num`
                                    (mk_small_numeral 96)
                                    `i:num`)
                          (mk_small_numeral off)))] THEN
            ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC_CONSTS] THEN
            REWRITE_TAC[ct_at] THEN
            REWRITE_TAC[AESENC_FIPS197_BRIDGE_ALT;
                        AESENCLAST_FIPS197_BRIDGE_ALT] THEN
            REWRITE_TAC[aes128_cipher; MAP] THEN
            CONV_TAC(DEPTH_CONV let_CONV) THEN
            CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
            SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256;
                     ARITH_LE; ARITH_LT; ARITH;
                     WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_XOR_0;
                     WORD_REVERSEFIELDS_XOR_128] THEN
            REWRITE_TAC[fips197_final_round; WORD_REVERSEFIELDS_XOR_128;
                        WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
            (let pk_eq =
               "pt_at pt_in (6 * i + " ^ string_of_int k ^ ") = p" ^
               string_of_int k in
             FIRST_X_ASSUM (fun th ->
               if string_of_term (concl th) = pk_eq
               then SUBST1_TAC (SYM th) else NO_TAC)) THEN
            (fun (asl, w) ->
              let lhs, _ = dest_eq w in
              SPEC_TAC(lhand lhs, `u:int128`) (asl, w)) THEN
            GEN_TAC THEN
            CONV_TAC WORD_BLAST)
           [1; 2; 3; 4; 5])
        ];
        (* stashed_ct_preserved_v2 iter_count — hold for next pass *)
        CHEAT_TAC;
        (* RDI advance: word_add iter_iptr (word 96) =
                        word_add iptr (word (96 * iter_count)) *)
        MATCH_MP_TAC CASEA_PTR_EQ THEN ASM_REWRITE_TAC[];
        (* RSI advance: same pattern for optr *)
        MATCH_MP_TAC CASEA_PTR_EQ THEN ASM_REWRITE_TAC[];
        (* RDX update via LOOP_RDX_STEP_LAST *)
        MATCH_MP_TAC LOOP_RDX_STEP_LAST THEN ASM_REWRITE_TAC[]
      ];

      (* Case B: middle iter (jc not taken, fall through to
         register-copy tail at pc+0x3ef + jmp back to pc+0).  Step the
         remaining 7 SIMD register copies + jmp, then reconstitute
         loopinv_v2 (i+1) by picking 4-tuple existential witnesses
         (xi4_asm, xi7_asm, xi8_asm, sp16_asm) directly from asm
         post-state.  The ghash_combine = ghash_at (i+1) conjunct
         closes via GHASH_COMBINE_STEP + the asm-side ring-algebra
         equation. *)
      CHEAT_TAC];

    (* Exit case — at pc+0x413 we have loopinv_v2 iter_count; simply
       discharge since the postcondition asserts loopinv_v2 iter_count at
       pc+0x413. *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[]]);;
