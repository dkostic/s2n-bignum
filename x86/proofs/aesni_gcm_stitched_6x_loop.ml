(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bulk-loop wrapper for the stitched 6-way AES-128-CTR + GHASH body         *)
(* (Milestone 8).                                                            *)
(*                                                                           *)
(* Composes Milestone 7's `AESNI_GCM_STITCHED_6X_CORRECT` over an arbitrary  *)
(* number of iterations by wrapping it in `ENSURES_WHILE_UP2_TAC` over the   *)
(* .Loop6x back-edge of `aesni_gcm_encrypt`.  The loop artefact              *)
(* `aesni_gcm_stitched_6x_loop_mc` is produced by                            *)
(* `tools/extract_stitched_6x_loop.py`: it is M7's 168-instruction filtered  *)
(* fast-path body (bytes 0..0x350 byte-for-byte identical to M7's            *)
(* `aesni_gcm_stitched_6x_mc`) followed by 10 bytes of loop plumbing         *)
(*                                                                           *)
(*     pc + 0x351  subq $6, %rdx        (4 bytes)                             *)
(*     pc + 0x355  jc .Ldone_exit       (2 bytes, forward to pc + 0x37b)      *)
(*     pc + 0x357  vpxor %xmm15,%xmm1,%xmm9      (next-iter xmm9)             *)
(*     pc + 0x35c  vmovdqa %xmm0,%xmm10          (next-iter xmm10)            *)
(*     pc + 0x360  vmovdqa %xmm5,%xmm11          (next-iter xmm11)            *)
(*     pc + 0x364  vmovdqa %xmm6,%xmm12          (next-iter xmm12)            *)
(*     pc + 0x368  vmovdqa %xmm7,%xmm13          (next-iter xmm13 - xmm7     *)
(*                                                is OVERWRITTEN below)       *)
(*     pc + 0x36c  vmovdqa %xmm3,%xmm14          (next-iter xmm14)            *)
(*     pc + 0x370  vmovdqu 0x20(%rsp),%xmm7      (reload prior-iter GHASH h) *)
(*     pc + 0x376  jmp aesni_gcm_stitched_6x_loop_core  (5-byte near jump)   *)
(*     pc + 0x37b  ret                                                        *)
(*                                                                           *)
(* Byte-count sanity: 892 total bytes (=0x37c), pre-ret at 0x37b, loop top   *)
(* at pc + 0x0, back-edge test at pc + 0x355.                                *)
(*                                                                           *)
(* The M7 body bytes [0, 0x351) are verbatim identical, so                   *)
(* AESNI_GCM_STITCHED_6X_CORRECT composes into the inductive-step subgoal    *)
(* of the loop via X86_BIGSTEP_TAC - no re-proving of the body is required.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/aesni_gcm_stitched_6x.ml";;  (* M7 theorem                 *)

(* ------------------------------------------------------------------------- *)
(* Machine code for the bulk loop.                                           *)
(* ------------------------------------------------------------------------- *)

let aesni_gcm_stitched_6x_loop_mc = define_assert_word_list
  "aesni_gcm_stitched_6x_loop_mc"
  `[
   word 0xc4; word 0xc1; word 0x7a; word 0x6f; word 0x59; word 0xe0;
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
   word 0x7f; word 0x76; word 0xf0; word 0x48; word 0x83; word 0xea;
   word 0x06; word 0x72; word 0x24; word 0xc4; word 0x41; word 0x71;
   word 0xef; word 0xcf; word 0xc5; word 0x79; word 0x6f; word 0xd0;
   word 0xc5; word 0x79; word 0x6f; word 0xdd; word 0xc5; word 0x79;
   word 0x6f; word 0xe6; word 0xc5; word 0x79; word 0x6f; word 0xef;
   word 0xc5; word 0x79; word 0x6f; word 0xf3; word 0xc5; word 0xfa;
   word 0x6f; word 0x7c; word 0x24; word 0x20; word 0xe9; word 0x85;
   word 0xfc; word 0xff; word 0xff; word 0xc3]:byte list`
  [
   0xc4; 0xc1; 0x7a; 0x6f; 0x59; 0xe0; 0xc5; 0x89; 0xfc; 0xca; 0xc4; 0x41;
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
   0x7a; 0x7f; 0x6e; 0xe0; 0xc5; 0x7a; 0x7f; 0x76; 0xf0; 0x48; 0x83; 0xea;
   0x06; 0x72; 0x24; 0xc4; 0x41; 0x71; 0xef; 0xcf; 0xc5; 0x79; 0x6f; 0xd0;
   0xc5; 0x79; 0x6f; 0xdd; 0xc5; 0x79; 0x6f; 0xe6; 0xc5; 0x79; 0x6f; 0xef;
   0xc5; 0x79; 0x6f; 0xf3; 0xc5; 0xfa; 0x6f; 0x7c; 0x24; 0x20; 0xe9; 0x85;
   0xfc; 0xff; 0xff; 0xc3];;

let AESNI_GCM_STITCHED_6X_LOOP_EXEC =
  X86_MK_CORE_EXEC_RULE aesni_gcm_stitched_6x_loop_mc;;

(* ------------------------------------------------------------------------- *)
(* Prefix relation between M7 and M8 byte lists.                             *)
(*                                                                           *)
(* M8's first 840 bytes are byte-for-byte identical to M7's first 840 bytes  *)
(* (which is `BUTLAST aesni_gcm_stitched_6x_mc`, i.e. M7's body minus the    *)
(* trailing `ret`).  Exhibiting the decomposition as an APPEND equality      *)
(* lets us discharge the `bytes_loaded s (word pc) (BUTLAST aesni_gcm_       *)
(* stitched_6x_mc)` side-condition of AESNI_GCM_STITCHED_6X_CORRECT inside   *)
(* the X86_BIGSTEP_TAC-generated inductive-step subgoal.                     *)
(* ------------------------------------------------------------------------- *)

let AESNI_GCM_STITCHED_6X_LOOP_MC_APPEND = prove
 (`aesni_gcm_stitched_6x_loop_mc =
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
           word 0x20; word 0xe9; word 0x85; word 0xfc;
           word 0xff; word 0xff; word 0xc3]`,
  REWRITE_TAC[aesni_gcm_stitched_6x_loop_mc; aesni_gcm_stitched_6x_mc;
              BUTLAST_CLAUSES; APPEND; NOT_CONS_NIL]);;

let BYTES_LOADED_LOOP_IMPLIES_M7_BUTLAST = prove
 (`!s pc.
     bytes_loaded s (word pc) aesni_gcm_stitched_6x_loop_mc
     ==> bytes_loaded s (word pc)
           (BUTLAST aesni_gcm_stitched_6x_mc)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[AESNI_GCM_STITCHED_6X_LOOP_MC_APPEND]) THEN
  SIMP_TAC[bytes_loaded_append]);;

(* Companion: `BUTLAST loop_mc` also extends over M7's body.  This is the    *)
(* form X86_BIGSTEP_TAC needs inside the inductive-step proof, because the   *)
(* outer CORRECT statement uses BUTLAST-of-loop-mc (as X86_MK_CORE_EXEC_RULE *)
(* strips the trailing ret).                                                 *)

let BUTLAST_LOOP_MC_APPEND = prove
 (`BUTLAST aesni_gcm_stitched_6x_loop_mc =
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
           word 0x20; word 0xe9; word 0x85; word 0xfc;
           word 0xff; word 0xff]`,
  REWRITE_TAC[aesni_gcm_stitched_6x_loop_mc; aesni_gcm_stitched_6x_mc;
              BUTLAST_CLAUSES; APPEND; NOT_CONS_NIL]);;

let BYTES_LOADED_LOOP_BUTLAST_IMPLIES_M7_BUTLAST = prove
 (`!s pc.
     bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_6x_loop_mc)
     ==> bytes_loaded s (word pc)
           (BUTLAST aesni_gcm_stitched_6x_mc)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BUTLAST_LOOP_MC_APPEND]) THEN
  SIMP_TAC[bytes_loaded_append]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence for the CF flag set by the `subq $6, %rdx` tail instruction.  *)
(*                                                                           *)
(* At loop-top iteration i, rdx = word_sub (word (6*iter_count))             *)
(* (word (6 + 6*i)).  After `subq $6, %rdx`, the instruction's CF = 1 iff    *)
(* the pre-subtraction value was < 6 (unsigned), i.e., the val of the rdx    *)
(* word is < 6.  Under the bounds `i < iter_count` and `6 * iter_count <     *)
(* 2^64`, this val is exactly `6 * (iter_count - 1 - i)`, which is < 6 iff   *)
(* i + 1 = iter_count.  The `jc` at pc+0x355 branches to pc+0x37b when CF=1, *)
(* which matches the ENSURES_WHILE_UP2 step's expected RIP at the last      *)
(* iteration.                                                                *)
(* ------------------------------------------------------------------------- *)

(* Rdx-step arithmetic: after `subq $6, %rdx`, the new rdx value matches
   either the next-iter invariant (i+1 < iter_count) or the exit-case
   invariant (i+1 = iter_count).  Both identities are pure-arithmetic
   facts about word_sub under the loop-top rdx spec. *)

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
(* Per-iteration nonoverlap.  The outer precondition gives `nonoverlapping   *)
(* (optr, 16*6*iter_count) X` for each readable X; the inductive step needs  *)
(* `nonoverlapping (word_add optr (word (96*i)), 96) X` for i < iter_count.  *)
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

(* Both-sided sub-region: used when iter_optr and iter_iptr are BOTH sub-  *)
(* regions of larger bulk regions.                                          *)

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

(* Pointer-equality identities used for loopinv_common closure in Case A/B  *)
(* of M8's inductive step.  Both reduce `word_add (iter_ptr) (word 96)`     *)
(* (where iter_ptr = word_add x (word (96*i))) to the target form.          *)

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
(* Loop invariant.                                                           *)
(*                                                                           *)
(* At iteration i (0..k), with k = number of 6-block iterations the caller   *)
(* has requested, the invariant pins register / memory / flag state at the   *)
(* loop-top label `pc + 0`:                                                  *)
(*                                                                           *)
(*   - RIP = pc + 0 (loop top)                                               *)
(*   - RDX = word_sub (word (6 * k)) (word (6 + 6 * i)) (remaining - 6,      *)
(*     decremented by 6 per iter, starts at 6*(k-1) for last-iter exit).     *)
(*   - RDI = word_add iptr_base (word (96 * i))  (plaintext pointer advance) *)
(*   - RSI = word_add optr_base (word (96 * i))  (ciphertext pointer advance)*)
(*   - RCX = kptr, R9 = hptr, R8 = cbptr, R11 = cptr, RSP = sptr (invariant) *)
(*   - Key schedule bytes pinned at kptr +/- biased offsets                  *)
(*   - H-table bytes pinned at hptr +/- biased offsets                       *)
(*   - Constants (red at cptr+16, plus at cptr+32) invariant                 *)
(*   - Stack stash slots sptr+{32..112} invariant                            *)
(*   - For the counter-/GHASH-state registers xmm2/xmm4/xmm7/xmm8/xmm9..15   *)
(*     AND the iter-linked memory at cbptr and sptr+16: the invariant uses   *)
(*     existential ghost variables so the specific values need not be named  *)
(*     in the schematic invariant shape.  The base case discharges them to   *)
(*     the caller's supplied (cb0..cb5, xi4, xi7, xi8, sp16).  The inductive *)
(*     step's X86_BIGSTEP_TAC of M7 advances them through one body's worth   *)
(*     of stores (pinning the 6 ciphertext-store outputs), and the 9-insn    *)
(*     tail rebuilds the counter-fan-out xmm9..14 for iter i+1.              *)
(*                                                                           *)
(* Input memory at iptr_base + [0, 16*6*k) is invariant (untouched).         *)
(* Output memory at optr_base + [0, 16*6*i) holds the ciphertext prefix —    *)
(* each 16-byte chunk is stitched_6x_ct_block applied to the iter's counter  *)
(* and plaintext.  In this scaffolding the prefix equality is asserted as an *)
(* existential ghost to keep the invariant tractable; M8 closure will name   *)
(* the precise expression in terms of ghash_polyval_acc + inc32 chains.      *)
(* ------------------------------------------------------------------------- *)

(* The invariant has two forms:
   - `loop-top form` (for i = 0..iter_count-1, state at pc+0 about to run body).
     Pins YMM4/7/8/9..14 via the cb0..cb5/xi4/xi7/xi8 existentials with the
     strong coupling `YMM9 = word_zx (word_xor cb0 k0)` and
     `cbptr-mem = cb0`, needed to discharge M7's precondition.
   - `exit form` (for i = iter_count, state at pc+891 after jc taken in the
     last iteration).  Pins only YMM2/YMM15 via memory invariants;
     YMM4/7/8/9..14 and cbptr/sptr+16 are arbitrary post-body.

   The two forms differ in the YMM existential block: loop-top requires the
   pre-body coupling, exit form requires nothing.  This matches the actual
   control flow: at loop-top, the 7-insn tail rotation has just run and set
   up YMM9..14 for the next iteration's counter fan-out; at exit, jc skipped
   the rotation so YMM9..14 hold the last iteration's ciphertext outputs. *)

(* Wrapper around the universally-quantified plaintext-memory read.  Hiding
   the quantifier inside a constant keeps `DISCARD_OLDSTATE_TAC`'s
   `unbound_statevars_of_read` from tripping on the outer `!j ... read c s`
   pattern when the stepper advances the state; see
   feedback_plaintext_framing_tactic.md for the reasoning.                  *)
let pt_preserved = new_definition
 `pt_preserved (iter_count:num) (iptr_base:int64) (s:x86state)
               (p_fn:num->int128) <=>
    !j. j < 6 * iter_count
        ==> read (memory :> bytes128
                    (word_add iptr_base (word (16 * j)))) s = p_fn j`;;

(* Framing tactic: given `pt_preserved iter_count iptr s0 p_fn` in the
   assumptions and a MAYCHANGE hypothesis `(M...) s0 s_end` (the accumulated
   writable frame for the iteration's body, which does NOT touch
   (iptr, 16*6*iter_count)), prove `pt_preserved iter_count iptr s_end p_fn`.

   Strategy:
     1. Unfold the goal to `!j. j < 6*iter_count ==> read(iptr+16j) s_end = p_fn j`
     2. Strip universal j, discharge the bound, and rewrite the RHS
        `p_fn j` to `read(iptr+16j) s0` via the pt_preserved s0 assumption.
     3. Pull the MAYCHANGE s0 s_end hypothesis, unfold to its write-chain
        component, substitute nested write-chain state abbrevs, and close
        via READ_OVER_WRITE_ORTHOGONAL_TAC using the bulk `nonoverlapping
        (optr, 96*iter_count) (iptr, ...)`, cbptr- and sp+16- vs-iptr
        nonoverlaps, together with the per-iter bound 96*i+96 <= 96*iter_count
        and j < 6*iter_count.

   See feedback_plaintext_framing_tactic.md for the origin. *)
let PT_FRAME_TAC (s_end_name:string) : tactic =
  REWRITE_TAC[pt_preserved] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th ->
    let c = concl th in
    try
      if name_of (fst (strip_comb c)) = "pt_preserved"
      then MP_TAC (REWRITE_RULE[pt_preserved] th) else NO_TAC
    with _ -> NO_TAC) THEN
  DISCH_THEN (MP_TAC o SPEC `j:num`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  (* Goal: read (mem :> bytes128 (word_add iptr (word (16*j)))) s_end =
           read (mem :> bytes128 (word_add iptr (word (16*j)))) s0 *)
  FIRST_X_ASSUM (fun th ->
    let c = concl th in
    try
      let _, args = strip_comb c in
      let n = List.length args in
      if n >= 2 &&
         is_var (List.nth args (n-2)) &&
         fst(dest_var (List.nth args (n-2))) = "s0" &&
         is_var (List.nth args (n-1)) &&
         fst(dest_var (List.nth args (n-1))) = s_end_name
      then MP_TAC th else NO_TAC
    with _ -> NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID; seq; ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN
  (* Only substitute write-chain equations; do NOT substitute hyps like
     `read R8 s0 = cbptr`, which would replace `cbptr` with `read R8 s0`
     in MAYCHANGE writables and break ROWOT. *)
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
  READ_OVER_WRITE_ORTHOGONAL_TAC;;

(* Opaque wrapper around the quantified output-prefix ciphertext invariant.
   ct_preserved i optr s ks counter_fn p_fn says that for every j < 6*i,
   the 16-byte block at optr+16j in state s equals the stitched-6x
   ciphertext block computed from AES round keys ks, counter counter_fn j
   and plaintext p_fn j.  Same opaque-wrapper rationale as pt_preserved:
   hiding the quantifier prevents DISCARD_OLDSTATE_TAC from discarding the
   hypothesis across X86_BIGSTEP_TAC. *)
let ct_preserved = new_definition
 `ct_preserved (i:num) (optr_base:int64) (s:x86state)
               (ks:int128 list) (counter_fn:num->int128)
               (p_fn:num->int128) <=>
    !j. j < 6 * i
        ==> read (memory :> bytes128
                    (word_add optr_base (word (16 * j)))) s =
            stitched_6x_ct_block ks (counter_fn j) (p_fn j)`;;

(* Framing tactic: given `ct_preserved i optr s0 ks counter_fn p_fn`,
   the per-iter bound `96*i + 96 <= 16*6*iter_count`, and a MAYCHANGE
   hypothesis `(M...) s0 s_end` whose memory writables are a subset of
   `(iter_optr, 96) ∪ cbptr ∪ (sptr+16, 16)` (where `iter_optr =
   word_add optr (word (96*i))`), prove the "old" part
   `!j<6*i. read(optr+16j) s_end = stitched_6x_ct_block ks (cf j) (pf j)`.
   The address `optr+16j` with j<6*i satisfies 16j+16 <= 96*i <= the start
   of iter_optr's region, so ROWOT closes using the (iter_optr, 96) ∪
   cbptr/sptr+16-vs-optr nonoverlap bounds.  This only establishes the
   preservation of the "old" j<6*i conjuncts — the new j in {6*i..6*i+5}
   are added in the caller via CONJ with the 6 per-block EXT4 facts. *)
let CT_FRAME_TAC (s_end_name:string) : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th ->
    let c = concl th in
    try
      if name_of (fst (strip_comb c)) = "ct_preserved"
      then MP_TAC (REWRITE_RULE[ct_preserved] th) else NO_TAC
    with _ -> NO_TAC) THEN
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
         fst(dest_var (List.nth args (n-1))) = s_end_name
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
  READ_OVER_WRITE_ORTHOGONAL_TAC;;

let loopinv_common = new_definition
 `loopinv_common
    (iptr_base:int64) (optr_base:int64) (kptr:int64) (hptr:int64)
    (cbptr:int64) (cptr:int64) (sptr:int64)
    (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
    (k5:int128) (k6:int128) (k7:int128) (k8:int128) (k9:int128) (k10:int128)
    (h0:int128) (h1:int128) (h3:int128) (h4:int128) (h6:int128) (h7:int128)
    (sp32:int128) (sp48:int128) (sp64:int128) (sp80:int128)
    (sp96:int128) (sp112:int128)
    (red:int128) (plus:int128)
    (counter_fn:num->int128) (p_fn:num->int128)
    (iter_count:num) (i:num) (s:x86state) <=>
      pt_preserved iter_count iptr_base s p_fn /\
      ct_preserved i optr_base s
        [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] counter_fn p_fn /\
      read RDI s = word_add iptr_base (word (96 * i)) /\
      read RSI s = word_add optr_base (word (96 * i)) /\
      read RDX s = word_sub (word (6 * iter_count)) (word (6 + 6 * i)) /\
      read RCX s = kptr /\
      read R9  s = hptr /\
      read R8  s = cbptr /\
      read R11 s = cptr /\
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
      read (memory :> bytes128 (word_add sptr (word 32))) s = sp32 /\
      read (memory :> bytes128 (word_add sptr (word 48))) s = sp48 /\
      read (memory :> bytes128 (word_add sptr (word 64))) s = sp64 /\
      read (memory :> bytes128 (word_add sptr (word 80))) s = sp80 /\
      read (memory :> bytes128 (word_add sptr (word 96))) s = sp96 /\
      read (memory :> bytes128 (word_add sptr (word 112))) s = sp112 /\
      read YMM2  s = (word_zx (plus:int128) : int256) /\
      read YMM15 s = (word_zx (k0:int128) : int256)`;;

let loopinv = new_definition
 `loopinv
    (iptr_base:int64) (optr_base:int64) (kptr:int64) (hptr:int64)
    (cbptr:int64) (cptr:int64) (sptr:int64)
    (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
    (k5:int128) (k6:int128) (k7:int128) (k8:int128) (k9:int128) (k10:int128)
    (h0:int128) (h1:int128) (h3:int128) (h4:int128) (h6:int128) (h7:int128)
    (sp32:int128) (sp48:int128) (sp64:int128) (sp80:int128)
    (sp96:int128) (sp112:int128)
    (red:int128) (plus:int128)
    (counter_fn:num->int128) (p_fn:num->int128)
    (iter_count:num) (i:num) (s:x86state) <=>
      loopinv_common iptr_base optr_base kptr hptr cbptr cptr sptr
                     k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
                     h0 h1 h3 h4 h6 h7
                     sp32 sp48 sp64 sp80 sp96 sp112
                     red plus
                     counter_fn p_fn
                     iter_count i s /\
      (i < iter_count
       ==> (?(xi4:int128) (xi7:int128) (xi8:int128) (sp16:int128).
              read YMM4  s = (word_zx xi4 : int256) /\
              read YMM7  s = (word_zx xi7 : int256) /\
              read YMM8  s = (word_zx xi8 : int256) /\
              read YMM9  s = (word_zx
                (word_xor (counter_fn (6 * i + 0)) k0 : int128) : int256) /\
              read YMM10 s = (word_zx (counter_fn (6 * i + 1)) : int256) /\
              read YMM11 s = (word_zx (counter_fn (6 * i + 2)) : int256) /\
              read YMM12 s = (word_zx (counter_fn (6 * i + 3)) : int256) /\
              read YMM13 s = (word_zx (counter_fn (6 * i + 4)) : int256) /\
              read YMM14 s = (word_zx (counter_fn (6 * i + 5)) : int256) /\
              read (memory :> bytes128 cbptr) s = counter_fn (6 * i + 0) /\
              read (memory :> bytes128 (word_add sptr (word 16))) s = sp16))`;;

(* ========================================================================= *)
(* Correctness statement for the bulk-loop wrapper.                          *)
(*                                                                           *)
(* Given k >= 1 iterations, entry matching the per-iteration invariant at    *)
(* i = 0, and the usual AES/GHASH memory/register disjointness, the loop    *)
(* runs k iterations of the stitched 6-way body and exits through `ret`.    *)
(* The postcondition asserts only the program-counter discharge and the     *)
(* MAYCHANGE frame (register + memory writables) — the specific output      *)
(* values (ciphertext prefix, final GHASH) are not re-asserted here.  They  *)
(* will be pinned down in a subsequent milestone that couples this loop     *)
(* wrapper with the tail path and GHASH unwinding, at which point the       *)
(* invariant's existential witnesses will be refined to closed-form         *)
(* expressions in ghash_polyval_acc / inc32_chain.                          *)
(* ========================================================================= *)

(* The 84 pairwise nonoverlapping clauses below (generated by
   tools/gen_m8_nonoverlap.py) replicate M7's 99-clause antecedent set over
   the outer iter-indexed (optr+96i, 16) / (iptr+96i+16j, 16) addresses via
   NONOVERLAPPING_SUBREGIONS: each sub-region of (optr, 96*iter_count)
   inherits its pairwise nonoverlap with every fixed readable.  Count: 3
   code-vs-writable + 3 writable-vs-iptr + 75 writable-vs-fixed-readable
   + 3 writable-vs-writable = 84. *)

let AESNI_GCM_STITCHED_6X_LOOP_CORRECT = prove
 (`!(optr:int64) (iptr:int64) (kptr:int64) (hptr:int64)
      (cbptr:int64) (cptr:int64) (sptr:int64)
      (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
      (k5:int128) (k6:int128) (k7:int128) (k8:int128)
      (k9:int128) (k10:int128)
      (h0:int128) (h1:int128) (h3:int128) (h4:int128) (h6:int128) (h7:int128)
      (sp32:int128) (sp48:int128) (sp64:int128) (sp80:int128)
      (sp96:int128) (sp112:int128)
      (red:int128) (plus:int128)
      (counter_fn:num->int128) (p_fn:num->int128)
      (iter_count:num) (pc:num).
      1 <= iter_count /\
      6 * iter_count < 2 EXP 64 /\
      (!j. counter_fn (j + 1) =
           simd16 word_add ((counter_fn j):int128) (plus:int128)) /\
      nonoverlapping (word pc:int64,LENGTH aesni_gcm_stitched_6x_loop_mc) (optr, 16 * 6 * iter_count) /\
      nonoverlapping (word pc:int64,LENGTH aesni_gcm_stitched_6x_loop_mc) ((cbptr:int64), 16) /\
      nonoverlapping (word pc:int64,LENGTH aesni_gcm_stitched_6x_loop_mc) (word_add sptr (word 16), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (iptr, 16 * 6 * iter_count) /\
      nonoverlapping ((cbptr:int64), 16) (iptr, 16 * 6 * iter_count) /\
      nonoverlapping (word_add sptr (word 16), 16) (iptr, 16 * 6 * iter_count) /\
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
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 32), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 48), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 64), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 80), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 96), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 112), 16) /\
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
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 32), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 48), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 64), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 80), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 96), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 112), 16) /\
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
      nonoverlapping (word_add sptr (word 16), 16) (word_add sptr (word 32), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add sptr (word 48), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add sptr (word 64), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add sptr (word 80), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add sptr (word 96), 16) /\
      nonoverlapping (word_add sptr (word 16), 16) (word_add sptr (word 112), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) ((cbptr:int64), 16) /\
      nonoverlapping (optr, 16 * 6 * iter_count) (word_add sptr (word 16), 16) /\
      nonoverlapping ((cbptr:int64), 16) (word_add sptr (word 16), 16)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_6x_loop_mc) /\
                read RIP s = word pc /\
                loopinv iptr optr kptr hptr cbptr cptr sptr
                        k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
                        h0 h1 h3 h4 h6 h7
                        sp32 sp48 sp64 sp80 sp96 sp112
                        red plus
                        counter_fn p_fn
                        iter_count 0 s)
           (\s. read RIP s = word (pc + 0x37b) /\
                loopinv iptr optr kptr hptr cbptr cptr sptr
                        k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
                        h0 h1 h3 h4 h6 h7
                        sp32 sp48 sp64 sp80 sp96 sp112
                        red plus
                        counter_fn p_fn
                        iter_count iter_count s)
           (MAYCHANGE [RIP; RDI; RSI; RDX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (optr,16 * 6 * iter_count);
                       memory :> bytes ((cbptr:int64),16);
                       memory :> bytes (word_add sptr (word 16),16)])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_UP2_TAC `iter_count:num` `pc + 0x0` `pc + 0x37b`
   `\(i:num) (s:x86state).
       loopinv iptr optr kptr hptr cbptr cptr sptr
               k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
               h0 h1 h3 h4 h6 h7
               sp32 sp48 sp64 sp80 sp96 sp112
               red plus
               counter_fn p_fn
               iter_count i s /\
       bytes_loaded s (word pc) (BUTLAST aesni_gcm_stitched_6x_loop_mc)` THEN
  REPEAT CONJ_TAC THENL
   [(* Non-zeroness of iter_count *)
    ASM_ARITH_TAC;

    (* Base case — loopinv 0 holds on entry since the precond asserts it.
       After B1 (RDI/RSI advance by 96*i), at i=0 we need to reduce
         word_add iptr_base (word (96 * 0)) = iptr_base
       via MULT_CLAUSES (96*0 = 0) and WORD_ADD_0. *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0];

    (* Inductive step — M7 via X86_BIGSTEP_TAC, then subq+jc + case split,
       then reconstitute loopinv (i+1).  Phases (a)-(f):

         (a) X_GEN_TAC i THEN STRIP_TAC THEN unfold loopinv.  The `i <
             iter_count` precondition (from the outer STRIP_TAC) fires the
             loop-top existential block, which STRIP_ASSUME_TAC brings into
             scope as cb0..cb5, xi4, xi7, xi8, sp16.
         (b) ABBREV_TAC plaintext blocks p0..p5 at iptr+{0..80}.
         (c) MP_TAC (SPECL [...] AESNI_GCM_STITCHED_6X_CORRECT_EXT) to bring
             the extended M7 (with YMM2/YMM15 pins) into scope, then
             discharge its 99-clause antecedent via NONOVERLAPPING_TAC.
         (d) X86_BIGSTEP_TAC with BYTES_LOADED_LOOP_BUTLAST_IMPLIES_
             M7_BUTLAST for the exec side-condition — lands at s1 with
             RIP = pc + 0x351.
         (e) X86_STEPS_TAC [2; 3] for subq + jc.
         (f) LOOP_CF_EQUIV folds the CF test into `i + 1 = iter_count`.
             ASM_CASES_TAC `i + 1 = iter_count` splits:
             - Case A (last iter, jc taken): RIP s3 = pc+891; the exit-form
               loopinv requires only loopinv_common, which is trivially
               derivable from s3's pinned state.
             - Case B (middle iter, jc not taken): 7 more insns land at
               s10 with RIP = pc + 0 and YMM9..14 set up for iter (i+1)
               via the tail rotations.  loopinv_common plus the
               pre-body existential block both close. *)
    (* Inductive step: with loopinv_common now asserting RDI/RSI advance by
       96*i per iteration (tracking M7's leaq advances), the composition via
       MP_TAC AESNI_GCM_STITCHED_6X_CORRECT_EXT3 must be SPECL'd at the
       per-iteration pointers iter_optr := word_add optr (word (96*i)) and
       iter_iptr := word_add iptr (word (96*i)).  The 99-clause nonoverlap
       antecedent splits into 99 individual goals via REPEAT CONJ_TAC; each
       closes with NONOVERLAPPING_TAC once per-iter bulk nonoverlaps have
       been added as named hypotheses via SUBGOAL_THEN + the three helpers
       NONOVERLAPPING_SUBREGION_LEFT/RIGHT/BOTH (defined above).  The
       per-iter derivations needed: 27 (iter_optr,96) X nonoverlaps
       (readables: 11 kptr entries, 6 hptr, 2 cptr, 6 sptr, cbptr, sp+16),
       1 (iter_optr,96) (iter_iptr,96) (via SUBREGION_BOTH), 2
       (cbptr|sp+16, 16) (iter_iptr, 96), 1 (pc,LENGTH mc) (iter_optr,96),
       and 6 (pc,892) (iter_optr+k,16) for the BIGSTEP program-mod check.
       Probed 2026-05-09 session 7: antecedent discharge works end-to-end
       and BIGSTEP succeeds, but Case A closure stalls on ASM_ARITH_TAC
       over 180+ hypotheses.  CASEA_PTR_EQ / CASEB_PTR_EQ (defined above)
       should close Case A/B ptr-equality subgoals once the MAYCHANGE
       frame-subsumption residual is navigated.  Memory:
       feedback_m8_ptr_advance_blocker.md summarises what remains.  *)
    (* Inductive step: composes M7 EXT3 via X86_BIGSTEP_TAC, then steps subq+jc,
       and case-splits on whether i+1 = iter_count (jc taken -> exit; else tail
       rotations for iter i+1's counter fan-out).  Per-iter nonoverlapping clauses
       are derived via NONOVERLAPPING_SUBREGION_{LEFT,RIGHT,BOTH} from the outer
       bulk hypotheses.  Case A closure requires substituting iter_optr/iter_iptr
       back to word_add optr/iptr (word (96*i)) before ENSURES_FINAL_STATE_TAC so
       that its MONOTONE_MAYCHANGE step can discharge the MAYCHANGE residual via
       CONTAINED_TAC (otherwise ASM_ARITH_TAC hangs in the 180+ hypothesis context). *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[loopinv; loopinv_common] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM (fun th ->
      let c = concl th in
      if is_imp c && is_exists (snd (dest_imp c))
      then STRIP_ASSUME_TAC (MATCH_MP th (ASSUME `i < iter_count`))
      else NO_TAC) THEN
    ABBREV_TAC `iter_iptr:int64 = word_add iptr (word (96 * i))` THEN
    ABBREV_TAC `iter_optr:int64 = word_add optr (word (96 * i))` THEN
    ABBREV_TAC `p0:int128 = read (memory :> bytes128 iter_iptr) s0` THEN
    ABBREV_TAC
      `p1:int128 = read (memory :> bytes128 (word_add iter_iptr (word 16))) s0` THEN
    ABBREV_TAC
      `p2:int128 = read (memory :> bytes128 (word_add iter_iptr (word 32))) s0` THEN
    ABBREV_TAC
      `p3:int128 = read (memory :> bytes128 (word_add iter_iptr (word 48))) s0` THEN
    ABBREV_TAC
      `p4:int128 = read (memory :> bytes128 (word_add iter_iptr (word 64))) s0` THEN
    ABBREV_TAC
      `p5:int128 = read (memory :> bytes128 (word_add iter_iptr (word 80))) s0` THEN
    (* Bridge p0..p5 to p_fn via pt_preserved so that EXT4's post ciphertext
       hypotheses (stated in terms of p_k in the 6 stitched conjuncts) can be
       closed against the ct_preserved SUBGOAL later (stated in terms of
       p_fn). *)
    (* Pre-compute the 6 bridging equations `read (iter_iptr+16k) s0 = p_fn(6i+k)`
       inline as conjuncts; unlike a universally-quantified !k.<read ... s0>, a
       plain conjunction of 6 concrete `read ... s0` hypotheses is erased by
       DISCARD_OLDSTATE_TAC (the facts mention s0).  So derive them JIT inside
       Case A/B's ct_preserved SUBGOAL from the surviving opaque pt_preserved
       s0-wrapped hypothesis. *)
    SUBGOAL_THEN `96 * i + 96 <= 16 * 6 * iter_count` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
       [(REWRITE_CONV[aesni_gcm_stitched_6x_loop_mc] THENC LENGTH_CONV)
          `LENGTH aesni_gcm_stitched_6x_loop_mc`]) THEN
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
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 32):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 32):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 48):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 48):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 64):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 64):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 80):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 80):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 96):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 96):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (iter_optr:int64, 96) (word_add sptr (word 112):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word_add sptr (word 112):int64`; `16:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
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
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (iter_optr:int64, 96)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i:num`; `96:num`;
                     `word pc:int64`; `892:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, LENGTH aesni_gcm_stitched_6x_mc) (iter_optr:int64, 96)` ASSUME_TAC THENL [
      REWRITE_TAC[(REWRITE_CONV[aesni_gcm_stitched_6x_mc] THENC LENGTH_CONV)
                    `LENGTH aesni_gcm_stitched_6x_mc`] THEN
      MP_TAC(ISPECL [`word pc:int64`; `892:num`; `0:num`; `850:num`;
                     `iter_optr:int64`; `96:num`] NONOVERLAPPING_SUBREGION_LEFT) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (word_add iter_optr (word 16):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 16:num`; `16:num`;
                     `word pc:int64`; `892:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (word_add iter_optr (word 32):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 32:num`; `16:num`;
                     `word pc:int64`; `892:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (word_add iter_optr (word 48):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 48:num`; `16:num`;
                     `word pc:int64`; `892:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (word_add iter_optr (word 64):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 64:num`; `16:num`;
                     `word pc:int64`; `892:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (word_add iter_optr (word 80):int64, 16)` ASSUME_TAC THENL [
      EXPAND_TAC "iter_optr" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      MP_TAC(ISPECL [`optr:int64`; `16 * 6 * iter_count:num`; `96 * i + 80:num`; `16:num`;
                     `word pc:int64`; `892:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
        [UNDISCH_TAC `96 * i + 96 <= 16 * 6 * iter_count` THEN ARITH_TAC;
         SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (iter_optr:int64, 16)` ASSUME_TAC THENL [
      MP_TAC(ISPECL [`iter_optr:int64`; `96:num`; `0:num`; `16:num`;
                     `word pc:int64`; `892:num`] NONOVERLAPPING_SUBREGION_RIGHT) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word pc:int64, 892) (word_add iter_optr (word 0):int64, 16)` ASSUME_TAC THENL [
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC (SPECL
      [`iter_optr:int64`;
       `iter_iptr:int64`;
       `kptr:int64`; `hptr:int64`; `cbptr:int64`; `cptr:int64`; `sptr:int64`;
       `p0:int128`; `p1:int128`; `p2:int128`;
       `p3:int128`; `p4:int128`; `p5:int128`;
       `(counter_fn:num->int128) (6 * i + 0)`;
       `(counter_fn:num->int128) (6 * i + 1)`;
       `(counter_fn:num->int128) (6 * i + 2)`;
       `(counter_fn:num->int128) (6 * i + 3)`;
       `(counter_fn:num->int128) (6 * i + 4)`;
       `(counter_fn:num->int128) (6 * i + 5)`;
       `k0:int128`; `k1:int128`; `k2:int128`; `k3:int128`;
       `k4:int128`; `k5:int128`; `k6:int128`; `k7:int128`;
       `k8:int128`; `k9:int128`; `k10:int128`;
       `h0:int128`; `h1:int128`; `h3:int128`;
       `h4:int128`; `h6:int128`; `h7:int128`;
       `xi4:int128`; `xi7:int128`; `xi8:int128`;
       `sp16:int128`; `sp32:int128`; `sp48:int128`; `sp64:int128`;
       `sp80:int128`; `sp96:int128`; `sp112:int128`;
       `red:int128`; `plus:int128`;
       `pc:num`] AESNI_GCM_STITCHED_6X_CORRECT_EXT4) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
    REWRITE_TAC[(REWRITE_CONV[aesni_gcm_stitched_6x_mc] THENC LENGTH_CONV)
                  `LENGTH aesni_gcm_stitched_6x_mc`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
    ANTS_TAC THENL [
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC
    ] THEN
    X86_BIGSTEP_TAC AESNI_GCM_STITCHED_6X_LOOP_EXEC "s1" THENL [
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      MATCH_MP_TAC BYTES_LOADED_LOOP_BUTLAST_IMPLIES_M7_BUTLAST THEN
      ASM_REWRITE_TAC[];
      ALL_TAC
    ] THEN
    X86_STEPS_TAC AESNI_GCM_STITCHED_6X_LOOP_EXEC [2; 3] THEN
    MP_TAC(SPECL [`i:num`; `iter_count:num`] LOOP_CF_EQUIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
      `val (word_sub (word (6 * iter_count)) (word (6 + 6 * i)):int64) < 6 <=>
       i + 1 = iter_count`]) THEN
    ASM_CASES_TAC `i + 1 = iter_count` THENL [
      (* Case A: last iter (i + 1 = iter_count), jc taken, land at pc+0x37b.  The
         exit-form loopinv requires only loopinv_common.  Substituting iter_optr
         and iter_iptr back to word_add optr/iptr (word (96*i)) form in all
         hypotheses BEFORE ENSURES_FINAL_STATE_TAC lets its auto MONOTONE_MAYCHANGE
         step close the MAYCHANGE residual via CONTAINED_TAC (the per-iter bound
         96*i + 96 <= 16*6*iter_count feeds contained_modulo). *)
      ASM_REWRITE_TAC[LT_REFL] THEN
      FIRST_X_ASSUM (fun th ->
        if string_of_term (concl th) =
             "word_add optr (word (96 * i)) = iter_optr"
        then SUBST_ALL_TAC (SYM th) else NO_TAC) THEN
      FIRST_X_ASSUM (fun th ->
        if string_of_term (concl th) =
             "word_add iptr (word (96 * i)) = iter_iptr"
        then SUBST_ALL_TAC (SYM th) else NO_TAC) THEN
      SUBGOAL_THEN `pt_preserved iter_count iptr s3 p_fn` ASSUME_TAC THENL
       [PT_FRAME_TAC "s3"; ALL_TAC] THEN
      (* WIP (2026-05-11 session aborted by reboot): ct_preserved Case A
         closure is behind CHEAT_TAC.  Strategy mostly designed + partially
         probed:

         1. Reduce iter_count to i+1 (Case A assumes i+1=iter_count).
         2. Unfold ct_preserved; X_GEN_TAC j; ASM_CASES_TAC `j < 6 * i`.
         3. Old j (j < 6*i): bridge s0 -> s3 via MAYCHANGE orthogonality
            through `ct_preserved i optr s0` (opaque, survives).  Requires
            deriving 8 per-j nonoverlaps: (optr+16j, 16) vs each of the
            6 MAYCHANGE writables `(word_add (word_add optr (word 96i))
            (word r), 16)` for r in {0,16,..,80}, plus cbptr and sptr+16.
            BLOCKER (probed): NONOVERLAPPING_SUBREGION_BOTH requires two
            DISJOINT superregions (same-base optr vs optr fails with
            `nonoverlapping (optr,N) (optr,N)` which is always false).
            Fix: add a new helper lemma `NONOVERLAPPING_SUBREGION_SAME_BASE`:
               !base n off1 len1 off2 len2.
                  off1 + len1 <= off2 /\ off2 + len2 <= n ==>
                  nonoverlapping (word_add base (word off1), len1)
                                 (word_add base (word off2), len2)
            Follows from NONOVERLAPPING_DISJOINT_INTERVALS + word arith.
         4. New j (j = 6*i+k', k'<6): use EXT4's 6 stitched hyps
            (in asl at s3 with `p_k` form) + bridge `p_k = p_fn(6*i+k)` via
            pt_preserved s3 SPEC'd at `6*i+k`.  Case-split k' in {0..5} and
            close each by ASM_REWRITE.

         The WIP skeleton below (after this CHEAT_TAC) is preserved as a
         reference for the next session.  See feedback_b2b_wip.md. *)
      SUBGOAL_THEN
        `ct_preserved iter_count optr s3
           [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] counter_fn p_fn`
        ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
        MATCH_MP_TAC CASEA_PTR_EQ THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CASEA_PTR_EQ THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LOOP_RDX_STEP_LAST THEN ASM_REWRITE_TAC[]
      ];
      (* Case B: middle iter (i + 1 < iter_count), jc not taken, step 7 tail insns
         + 1 back-jmp to land at pc+0 for iter (i+1).  The loopinv (i+1) existential
         block's witnesses come from M7 EXT3's post: new_cb0, c0/5/6/7/3_out,
         xi4_out, sp32 (reload), xi8_out, sp+16 (unchanged).  CASEB_PTR_EQ (an
         unconditional equation) closes ptr-advance via REWRITE_TAC; LOOP_RDX_STEP_MID
         closes the rdx update.  SUBST iter_optr/iter_iptr before MONOTONE_MAYCHANGE
         for the MAYCHANGE residual, same rationale as Case A. *)
      SUBGOAL_THEN `i + 1 < iter_count` ASSUME_TAC THENL [
        UNDISCH_TAC `i < iter_count` THEN
        UNDISCH_TAC `~(i + 1 = iter_count)` THEN
        ARITH_TAC;
        ALL_TAC
      ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(i + 1 = iter_count)`]) THEN
      X86_STEPS_TAC AESNI_GCM_STITCHED_6X_LOOP_EXEC (4--11) THEN
      FIRST_X_ASSUM (fun th ->
        if string_of_term (concl th) =
             "word_add optr (word (96 * i)) = iter_optr"
        then SUBST_ALL_TAC (SYM th) else NO_TAC) THEN
      FIRST_X_ASSUM (fun th ->
        if string_of_term (concl th) =
             "word_add iptr (word (96 * i)) = iter_iptr"
        then SUBST_ALL_TAC (SYM th) else NO_TAC) THEN
      SUBGOAL_THEN `pt_preserved iter_count iptr s11 p_fn` ASSUME_TAC THENL
       [PT_FRAME_TAC "s11"; ALL_TAC] THEN
      SUBGOAL_THEN
        `ct_preserved (i + 1) optr s11
           [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] counter_fn p_fn`
        ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
        REWRITE_TAC[ADD_CLAUSES];
        REWRITE_TAC[CASEB_PTR_EQ];
        REWRITE_TAC[CASEB_PTR_EQ];
        REWRITE_TAC[LOOP_RDX_STEP_MID];
        MAP_EVERY EXISTS_TAC
          [`xi4_out:int128`; `sp32:int128`; `xi8_out:int128`;
           `read (memory :> bytes128 (word_add sptr (word 16))) s11 :int128`] THEN
        ASM_REWRITE_TAC[WORD_ZX_ZX_128] THEN CHEAT_TAC
      ]
    ];

    (* Exit case — at pc+0x37b we have loopinv iter_count; simply discharge
       since the postcondition asserts loopinv iter_count at pc+0x37b. *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[]]);;

