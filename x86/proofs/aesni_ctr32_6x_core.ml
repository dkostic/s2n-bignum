(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 6-way AES-128 CTR body, standalone-artefact form (Milestone 5).           *)
(*                                                                           *)
(* Proves correctness of `aesni_ctr32_6x_core.S`, the unrolled fast path of  *)
(* aws-lc's `_aesni_ctr32_6x` helper repackaged as a single-entry function   *)
(* with a System V ABI:                                                      *)
(*                                                                           *)
(*     rdi = input   (96 bytes = 6 plaintext blocks)                         *)
(*     rsi = output  (96 bytes = 6 ciphertext blocks)                        *)
(*     rdx = key     (176 bytes = 11 round keys k0..k10)                     *)
(*     rcx = counter (96 bytes = 6 pre-shuffled counter blocks c0..c5)       *)
(*                                                                           *)
(* The counter lanes are assumed already in XMM byte order (the form that   *)
(* `.Loop_ctr32` would observe after the leading `vpshufb .Lbswap_mask`     *)
(* chain in aws-lc) with per-lane 32-bit counter increment pre-applied.     *)
(* The `.Lhandle_ctr32_2` carry branch is elided: the caller guarantees    *)
(* that the CTR32 field does not wrap across the 6 blocks, so all 6 lanes   *)
(* are processed in the fast path.                                          *)
(*                                                                           *)
(* Correctness: for each lane j in {0,...,5},                                *)
(*                                                                           *)
(*   output[j] = input[j] XOR word_reversefields 8                           *)
(*     (aes128_cipher (word_reversefields 8 c_j)                             *)
(*                    [word_reversefields 8 k0; ...;                         *)
(*                     word_reversefields 8 k10])                            *)
(*                                                                           *)
(* The byte-reversal lifts the hardware XMM little-endian layout into the   *)
(* NIST big-endian orientation expected by `fips197_round`/`aes128_cipher`  *)
(* (AESENC_FIPS197_BRIDGE; project memory "AES hardware vs FIPS 197").      *)
(*                                                                           *)
(* This proof is not composed into the eventual `aesni_gcm_encrypt`         *)
(* theorem (s2n-bignum does not permit `ensures`-composition across files); *)
(* its role is threefold, per plan §5 Milestone 5:                           *)
(*                                                                           *)
(*   1. A standalone-verified reference for the same instruction sequence   *)
(*      that later has to be re-proven as a prefix of the inlined encrypt   *)
(*      function, giving a concrete cost budget signal.                     *)
(*   2. A self-contained artefact reusable by future AES-CTR mode proofs.   *)
(*   3. A template whose invariant shape and bridging-tactic spine transfer *)
(*      to the stitched Milestone 7/8 loop.                                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/aes_fips197_bridge.ml";;

(* 475 bytes (0x1db) of machine code; 91 instructions.                       *)
(* Structure:                                                                *)
(*   - 12 loads + 6 vpxor  :  counter-lane initial AddRoundKey  (18)         *)
(*   - 9 x (1 load + 6 vaesenc) :  middle rounds k1..k9         (63)         *)
(*   - 1 load + 6 vpxor   :  final-round key XOR'd with input   (7)          *)
(*   - 6 vaesenclast      :  closing AES round                  (6)          *)
(*   - 6 vmovdqu stores   :  ciphertext writes                  (6)          *)
(*   - 1 ret                                                    (1)          *)
(* = 18 + 63 + 7 + 6 + 6 + 1 = 91 instructions, 475 bytes total.             *)

let aesni_ctr32_6x_core_mc = define_assert_word_list "aesni_ctr32_6x_core_mc"
  `[word 0xc5; word 0xfa; word 0x6f; word 0x22; word 0xc5; word 0x7a;
    word 0x6f; word 0x09; word 0xc5; word 0x31; word 0xef; word 0xcc;
    word 0xc5; word 0x7a; word 0x6f; word 0x51; word 0x10; word 0xc5;
    word 0x29; word 0xef; word 0xd4; word 0xc5; word 0x7a; word 0x6f;
    word 0x59; word 0x20; word 0xc5; word 0x21; word 0xef; word 0xdc;
    word 0xc5; word 0x7a; word 0x6f; word 0x61; word 0x30; word 0xc5;
    word 0x19; word 0xef; word 0xe4; word 0xc5; word 0x7a; word 0x6f;
    word 0x69; word 0x40; word 0xc5; word 0x11; word 0xef; word 0xec;
    word 0xc5; word 0x7a; word 0x6f; word 0x71; word 0x50; word 0xc5;
    word 0x09; word 0xef; word 0xf4; word 0xc5; word 0x7a; word 0x6f;
    word 0x7a; word 0x10; word 0xc4; word 0x42; word 0x31; word 0xdc;
    word 0xcf; word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7;
    word 0xc4; word 0x42; word 0x21; word 0xdc; word 0xdf; word 0xc4;
    word 0x42; word 0x19; word 0xdc; word 0xe7; word 0xc4; word 0x42;
    word 0x11; word 0xdc; word 0xef; word 0xc4; word 0x42; word 0x09;
    word 0xdc; word 0xf7; word 0xc5; word 0x7a; word 0x6f; word 0x7a;
    word 0x20; word 0xc4; word 0x42; word 0x31; word 0xdc; word 0xcf;
    word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7; word 0xc4;
    word 0x42; word 0x21; word 0xdc; word 0xdf; word 0xc4; word 0x42;
    word 0x19; word 0xdc; word 0xe7; word 0xc4; word 0x42; word 0x11;
    word 0xdc; word 0xef; word 0xc4; word 0x42; word 0x09; word 0xdc;
    word 0xf7; word 0xc5; word 0x7a; word 0x6f; word 0x7a; word 0x30;
    word 0xc4; word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc4;
    word 0x42; word 0x29; word 0xdc; word 0xd7; word 0xc4; word 0x42;
    word 0x21; word 0xdc; word 0xdf; word 0xc4; word 0x42; word 0x19;
    word 0xdc; word 0xe7; word 0xc4; word 0x42; word 0x11; word 0xdc;
    word 0xef; word 0xc4; word 0x42; word 0x09; word 0xdc; word 0xf7;
    word 0xc5; word 0x7a; word 0x6f; word 0x7a; word 0x40; word 0xc4;
    word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc4; word 0x42;
    word 0x29; word 0xdc; word 0xd7; word 0xc4; word 0x42; word 0x21;
    word 0xdc; word 0xdf; word 0xc4; word 0x42; word 0x19; word 0xdc;
    word 0xe7; word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef;
    word 0xc4; word 0x42; word 0x09; word 0xdc; word 0xf7; word 0xc5;
    word 0x7a; word 0x6f; word 0x7a; word 0x50; word 0xc4; word 0x42;
    word 0x31; word 0xdc; word 0xcf; word 0xc4; word 0x42; word 0x29;
    word 0xdc; word 0xd7; word 0xc4; word 0x42; word 0x21; word 0xdc;
    word 0xdf; word 0xc4; word 0x42; word 0x19; word 0xdc; word 0xe7;
    word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0xc4;
    word 0x42; word 0x09; word 0xdc; word 0xf7; word 0xc5; word 0x7a;
    word 0x6f; word 0x7a; word 0x60; word 0xc4; word 0x42; word 0x31;
    word 0xdc; word 0xcf; word 0xc4; word 0x42; word 0x29; word 0xdc;
    word 0xd7; word 0xc4; word 0x42; word 0x21; word 0xdc; word 0xdf;
    word 0xc4; word 0x42; word 0x19; word 0xdc; word 0xe7; word 0xc4;
    word 0x42; word 0x11; word 0xdc; word 0xef; word 0xc4; word 0x42;
    word 0x09; word 0xdc; word 0xf7; word 0xc5; word 0x7a; word 0x6f;
    word 0x7a; word 0x70; word 0xc4; word 0x42; word 0x31; word 0xdc;
    word 0xcf; word 0xc4; word 0x42; word 0x29; word 0xdc; word 0xd7;
    word 0xc4; word 0x42; word 0x21; word 0xdc; word 0xdf; word 0xc4;
    word 0x42; word 0x19; word 0xdc; word 0xe7; word 0xc4; word 0x42;
    word 0x11; word 0xdc; word 0xef; word 0xc4; word 0x42; word 0x09;
    word 0xdc; word 0xf7; word 0xc5; word 0x7a; word 0x6f; word 0xba;
    word 0x80; word 0x00; word 0x00; word 0x00; word 0xc4; word 0x42;
    word 0x31; word 0xdc; word 0xcf; word 0xc4; word 0x42; word 0x29;
    word 0xdc; word 0xd7; word 0xc4; word 0x42; word 0x21; word 0xdc;
    word 0xdf; word 0xc4; word 0x42; word 0x19; word 0xdc; word 0xe7;
    word 0xc4; word 0x42; word 0x11; word 0xdc; word 0xef; word 0xc4;
    word 0x42; word 0x09; word 0xdc; word 0xf7; word 0xc5; word 0x7a;
    word 0x6f; word 0xba; word 0x90; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0x42; word 0x31; word 0xdc; word 0xcf; word 0xc4;
    word 0x42; word 0x29; word 0xdc; word 0xd7; word 0xc4; word 0x42;
    word 0x21; word 0xdc; word 0xdf; word 0xc4; word 0x42; word 0x19;
    word 0xdc; word 0xe7; word 0xc4; word 0x42; word 0x11; word 0xdc;
    word 0xef; word 0xc4; word 0x42; word 0x09; word 0xdc; word 0xf7;
    word 0xc5; word 0xfa; word 0x6f; word 0x9a; word 0xa0; word 0x00;
    word 0x00; word 0x00; word 0xc5; word 0xe1; word 0xef; word 0x27;
    word 0xc5; word 0xe1; word 0xef; word 0x6f; word 0x10; word 0xc5;
    word 0xe1; word 0xef; word 0x77; word 0x20; word 0xc5; word 0x61;
    word 0xef; word 0x47; word 0x30; word 0xc5; word 0xe1; word 0xef;
    word 0x57; word 0x40; word 0xc5; word 0xe1; word 0xef; word 0x5f;
    word 0x50; word 0xc4; word 0x62; word 0x31; word 0xdd; word 0xcc;
    word 0xc4; word 0x62; word 0x29; word 0xdd; word 0xd5; word 0xc4;
    word 0x62; word 0x21; word 0xdd; word 0xde; word 0xc4; word 0x42;
    word 0x19; word 0xdd; word 0xe0; word 0xc4; word 0x62; word 0x11;
    word 0xdd; word 0xea; word 0xc4; word 0x62; word 0x09; word 0xdd;
    word 0xf3; word 0xc5; word 0x7a; word 0x7f; word 0x0e; word 0xc5;
    word 0x7a; word 0x7f; word 0x56; word 0x10; word 0xc5; word 0x7a;
    word 0x7f; word 0x5e; word 0x20; word 0xc5; word 0x7a; word 0x7f;
    word 0x66; word 0x30; word 0xc5; word 0x7a; word 0x7f; word 0x6e;
    word 0x40; word 0xc5; word 0x7a; word 0x7f; word 0x76; word 0x50;
    word 0xc3]:byte list`
  [0xc5; 0xfa; 0x6f; 0x22; 0xc5; 0x7a; 0x6f; 0x09; 0xc5; 0x31; 0xef; 0xcc;
   0xc5; 0x7a; 0x6f; 0x51; 0x10; 0xc5; 0x29; 0xef; 0xd4; 0xc5; 0x7a; 0x6f;
   0x59; 0x20; 0xc5; 0x21; 0xef; 0xdc; 0xc5; 0x7a; 0x6f; 0x61; 0x30; 0xc5;
   0x19; 0xef; 0xe4; 0xc5; 0x7a; 0x6f; 0x69; 0x40; 0xc5; 0x11; 0xef; 0xec;
   0xc5; 0x7a; 0x6f; 0x71; 0x50; 0xc5; 0x09; 0xef; 0xf4; 0xc5; 0x7a; 0x6f;
   0x7a; 0x10; 0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7;
   0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42;
   0x11; 0xdc; 0xef; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x7a;
   0x20; 0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4;
   0x42; 0x21; 0xdc; 0xdf; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11;
   0xdc; 0xef; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x7a; 0x30;
   0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42;
   0x21; 0xdc; 0xdf; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc;
   0xef; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x7a; 0x40; 0xc4;
   0x42; 0x31; 0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42; 0x21;
   0xdc; 0xdf; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef;
   0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x7a; 0x50; 0xc4; 0x42;
   0x31; 0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42; 0x21; 0xdc;
   0xdf; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc4;
   0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x7a; 0x60; 0xc4; 0x42; 0x31;
   0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42; 0x21; 0xdc; 0xdf;
   0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc4; 0x42;
   0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0x7a; 0x70; 0xc4; 0x42; 0x31; 0xdc;
   0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42; 0x21; 0xdc; 0xdf; 0xc4;
   0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc4; 0x42; 0x09;
   0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0xba; 0x80; 0x00; 0x00; 0x00; 0xc4; 0x42;
   0x31; 0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42; 0x21; 0xdc;
   0xdf; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc; 0xef; 0xc4;
   0x42; 0x09; 0xdc; 0xf7; 0xc5; 0x7a; 0x6f; 0xba; 0x90; 0x00; 0x00; 0x00;
   0xc4; 0x42; 0x31; 0xdc; 0xcf; 0xc4; 0x42; 0x29; 0xdc; 0xd7; 0xc4; 0x42;
   0x21; 0xdc; 0xdf; 0xc4; 0x42; 0x19; 0xdc; 0xe7; 0xc4; 0x42; 0x11; 0xdc;
   0xef; 0xc4; 0x42; 0x09; 0xdc; 0xf7; 0xc5; 0xfa; 0x6f; 0x9a; 0xa0; 0x00;
   0x00; 0x00; 0xc5; 0xe1; 0xef; 0x27; 0xc5; 0xe1; 0xef; 0x6f; 0x10; 0xc5;
   0xe1; 0xef; 0x77; 0x20; 0xc5; 0x61; 0xef; 0x47; 0x30; 0xc5; 0xe1; 0xef;
   0x57; 0x40; 0xc5; 0xe1; 0xef; 0x5f; 0x50; 0xc4; 0x62; 0x31; 0xdd; 0xcc;
   0xc4; 0x62; 0x29; 0xdd; 0xd5; 0xc4; 0x62; 0x21; 0xdd; 0xde; 0xc4; 0x42;
   0x19; 0xdd; 0xe0; 0xc4; 0x62; 0x11; 0xdd; 0xea; 0xc4; 0x62; 0x09; 0xdd;
   0xf3; 0xc5; 0x7a; 0x7f; 0x0e; 0xc5; 0x7a; 0x7f; 0x56; 0x10; 0xc5; 0x7a;
   0x7f; 0x5e; 0x20; 0xc5; 0x7a; 0x7f; 0x66; 0x30; 0xc5; 0x7a; 0x7f; 0x6e;
   0x40; 0xc5; 0x7a; 0x7f; 0x76; 0x50;
   0xc3];;

let AESNI_CTR32_6X_CORE_EXEC = X86_MK_CORE_EXEC_RULE aesni_ctr32_6x_core_mc;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary: `word_reversefields 8` distributes over `word_xor` on int128,  *)
(* reused from Milestone 4's `aes128_encrypt.ml`.  WORD_BLAST succeeds on    *)
(* the 128-bit instance; the polymorphic version does not.                    *)
(* ------------------------------------------------------------------------- *)

let WORD_REVERSEFIELDS_XOR_128 = WORD_BLAST
  `!(a:int128) b. word_reversefields 8 (word_xor a b) =
                  word_xor (word_reversefields 8 a) (word_reversefields 8 b)`;;

(* ------------------------------------------------------------------------- *)
(* Spec helper: the encryption-result lane                                   *)
(*                                                                           *)
(*   aes128_ctr_lane c [k0;...;k10] =                                        *)
(*     word_reversefields 8                                                  *)
(*       (aes128_cipher (word_reversefields 8 c)                             *)
(*                      (MAP (word_reversefields 8) [k0;...;k10]))           *)
(*                                                                           *)
(* expresses the hardware-side XMM-layout AES-128 encryption of a counter   *)
(* block `c` under the 11-key schedule at `k0..k10`.  A memory-I/O CTR-mode *)
(* lane stores `input XOR aes128_ctr_lane c ks`.                             *)
(* ------------------------------------------------------------------------- *)

let aes128_ctr_lane = new_definition
  `aes128_ctr_lane (c:int128) (ks:int128 list) =
     word_reversefields 8
       (aes128_cipher (word_reversefields 8 c)
                      (MAP (word_reversefields 8) ks))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(*                                                                           *)
(* `nonoverlapping (word pc,LENGTH mc) (output,96)` is required so the       *)
(* stepper can discharge the 6 final `vmovdqu %xmmN,offset(%rsi)` stores'    *)
(* "updates will not modify program code" side condition.  As in Milestone  *)
(* 4, we evaluate `LENGTH` to a concrete numeral before `ENSURES_INIT_TAC`   *)
(* via a one-shot `REWRITE_CONV[mc] THENC LENGTH_CONV` rewrite.              *)
(*                                                                           *)
(* We do not require `nonoverlapping` between output and input / key /       *)
(* counter buffers: the implementation issues all 12 memory loads (6 input  *)
(* lanes, 11 keys, 6 counter lanes) strictly before the first of its 6      *)
(* ciphertext stores, so read-after-write aliasing cannot arise.             *)
(*                                                                           *)
(* `MAYCHANGE` frames the state change using base ZMM components, not       *)
(* derived YMM/XMM, per project feedback_maychange_ymm.md.  The six lanes   *)
(* end up in XMM9..XMM14; XMM3 holds `k10`, XMM4 holds the initial          *)
(* AddRoundKey value / the first input-xor intermediate; XMM5/6/8/2         *)
(* hold the rest of the k10-input XORs; XMM15 rolls through k1..k9.  Hence  *)
(* we enumerate ZMM2..ZMM6, ZMM8..ZMM15.                                    *)
(* ------------------------------------------------------------------------- *)

let AESNI_CTR32_6X_CORE_CORRECT = prove
 (`!output input key counter
      i0 i1 i2 i3 i4 i5
      c0 c1 c2 c3 c4 c5
      k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
      pc.
      nonoverlapping (word pc,LENGTH aesni_ctr32_6x_core_mc) (output,96)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST aesni_ctr32_6x_core_mc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [input; output; key; counter] s /\
                read (memory :> bytes128 input) s = i0 /\
                read (memory :> bytes128 (word_add input (word 16))) s = i1 /\
                read (memory :> bytes128 (word_add input (word 32))) s = i2 /\
                read (memory :> bytes128 (word_add input (word 48))) s = i3 /\
                read (memory :> bytes128 (word_add input (word 64))) s = i4 /\
                read (memory :> bytes128 (word_add input (word 80))) s = i5 /\
                read (memory :> bytes128 key) s = k0 /\
                read (memory :> bytes128 (word_add key (word 16))) s = k1 /\
                read (memory :> bytes128 (word_add key (word 32))) s = k2 /\
                read (memory :> bytes128 (word_add key (word 48))) s = k3 /\
                read (memory :> bytes128 (word_add key (word 64))) s = k4 /\
                read (memory :> bytes128 (word_add key (word 80))) s = k5 /\
                read (memory :> bytes128 (word_add key (word 96))) s = k6 /\
                read (memory :> bytes128 (word_add key (word 112))) s = k7 /\
                read (memory :> bytes128 (word_add key (word 128))) s = k8 /\
                read (memory :> bytes128 (word_add key (word 144))) s = k9 /\
                read (memory :> bytes128 (word_add key (word 160))) s = k10 /\
                read (memory :> bytes128 counter) s = c0 /\
                read (memory :> bytes128 (word_add counter (word 16))) s = c1 /\
                read (memory :> bytes128 (word_add counter (word 32))) s = c2 /\
                read (memory :> bytes128 (word_add counter (word 48))) s = c3 /\
                read (memory :> bytes128 (word_add counter (word 64))) s = c4 /\
                read (memory :> bytes128 (word_add counter (word 80))) s = c5)
           (\s. read RIP s = word (pc + 0x1da) /\
                read (memory :> bytes128 output) s =
                  word_xor i0
                    (aes128_ctr_lane c0
                       [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
                read (memory :> bytes128 (word_add output (word 16))) s =
                  word_xor i1
                    (aes128_ctr_lane c1
                       [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
                read (memory :> bytes128 (word_add output (word 32))) s =
                  word_xor i2
                    (aes128_ctr_lane c2
                       [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
                read (memory :> bytes128 (word_add output (word 48))) s =
                  word_xor i3
                    (aes128_ctr_lane c3
                       [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
                read (memory :> bytes128 (word_add output (word 64))) s =
                  word_xor i4
                    (aes128_ctr_lane c4
                       [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
                read (memory :> bytes128 (word_add output (word 80))) s =
                  word_xor i5
                    (aes128_ctr_lane c5
                       [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]))
           (MAYCHANGE [RIP] ,,
            MAYCHANGE [ZMM2; ZMM3; ZMM4; ZMM5; ZMM6;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes128 output;
                       memory :> bytes128 (word_add output (word 16));
                       memory :> bytes128 (word_add output (word 32));
                       memory :> bytes128 (word_add output (word 48));
                       memory :> bytes128 (word_add output (word 64));
                       memory :> bytes128 (word_add output (word 80))])`,
  CHEAT_TAC);;
