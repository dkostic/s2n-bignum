(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Single-block GHASH multiply, standalone-artefact form (Milestone 6).      *)
(*                                                                           *)
(* Proves correctness of `gcm_gmult_x86.S`, a VEX-encoded re-expression of   *)
(* aws-lc's `gcm_gmult_clmul` (ghash-x86_64.S, commit                         *)
(* 2ddb1c333f25f0288e8413d32b30260da3802157).  See the .S for the detailed   *)
(* deviations (VEX throughout, `pshufd $78` rewritten as `vpalignr $8`,      *)
(* Karatsuba middle recomputed in-register instead of being loaded from the  *)
(* Htable[2] slot, bswap_mask passed as a pointer argument rather than       *)
(* living in .rodata).                                                       *)
(*                                                                           *)
(* System V ABI:                                                             *)
(*   rdi = Xi pointer         (16 bytes, read + write)                       *)
(*   rsi = H  pointer         (16 bytes, read;  pre-twisted POLYVAL H)       *)
(*   rdx = bswap_mask pointer (16 bytes, read;  byte-reverse permutation)    *)
(*                                                                           *)
(* Correctness (hardware-XMM-layout statement):                              *)
(*                                                                           *)
(*   new_Xi = word_reversefields 8 (                                         *)
(*              polyval_dot (word_reversefields 8 Xi) H)                     *)
(*                                                                           *)
(* The byte-reversal on Xi bridges the hardware XMM little-endian layout to  *)
(* the POLYVAL-orientation value that the multiply consumes (`vpshufb` on    *)
(* the loaded Xi, and again on the reduced result before the store).  H is   *)
(* assumed to already live in POLYVAL orientation -- that is the form aws-lc *)
(* `gcm_init_clmul` writes to memory at the Htable[0] slot.  The caller      *)
(* precondition `bswap = word 0x000102030405060708090a0b0c0d0e0f` selects    *)
(* the byte-reverse permutation that makes the two `vpshufb` applications    *)
(* equal to `word_reversefields 8`.                                          *)
(*                                                                           *)
(* Bridging to the NIST-GHASH / polyval_dot twist / ghash_polyval_acc level  *)
(* (Milestone 1 bridges + ghash_nist_bridge.ml) is deferred to the use site: *)
(* at the stitched-loop scale, the twist on H is applied once and the Xi    *)
(* accumulator never leaves register form, so those bridges will be applied  *)
(* outside this theorem.                                                     *)
(*                                                                           *)
(* This proof is not composed into the eventual `aesni_gcm_encrypt` theorem *)
(* (s2n-bignum does not permit `ensures`-composition across files); its role *)
(* is per plan section 5 Milestone 6: a 1-kernel exercise of the VPCLMULQDQ  *)
(* + Karatsuba + reduction plus bridging tactic, before the full stitched   *)
(* loop in Milestone 7.                                                       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/polyval_ghash.ml";;  (* polyval_dot *)

(* ------------------------------------------------------------------------- *)
(* Machine code: 41 VEX instructions + ret, 187 bytes.                       *)
(* Structure, mirroring the .S layout:                                       *)
(*   03  vmovdqu loads (bswap, H, Xi)                                        *)
(*   01  vpshufb Xi  (byte-reverse into polyval orientation)                 *)
(*   01  vmovdqa xmm0 -> xmm1  (save Xi for hi*hi)                           *)
(*   04  Karatsuba set-up (2 vpalignr + 2 vpxor)                             *)
(*   03  vpclmulqdq: lo*lo, hi*hi, mid*mid                                   *)
(*   02  vpxor: fold lo, hi into mid                                         *)
(*   05  Karatsuba recombine (vmovdqa + vpsrldq + vpslldq + 2 vpxor)         *)
(*   11  reduction step 1 (fold pair)                                        *)
(*   08  reduction step 2                                                    *)
(*   01  vpshufb restore (byte-reverse back)                                 *)
(*   01  vmovdqu store                                                       *)
(*   01  ret                                                                 *)
(* = 41 steppable + 1 ret = 42 total.                                        *)
(* ------------------------------------------------------------------------- *)

let gcm_gmult_x86_mc = define_assert_word_list "gcm_gmult_x86_mc"
  `[word 0xc5; word 0xfa; word 0x6f; word 0x2a; word 0xc5; word 0xfa;
    word 0x6f; word 0x16; word 0xc5; word 0xfa; word 0x6f; word 0x07;
    word 0xc4; word 0xe2; word 0x79; word 0x00; word 0xc5; word 0xc5;
    word 0xf9; word 0x6f; word 0xc8; word 0xc4; word 0xe3; word 0x79;
    word 0x0f; word 0xd8; word 0x08; word 0xc5; word 0xe1; word 0xef;
    word 0xd8; word 0xc4; word 0xe3; word 0x69; word 0x0f; word 0xe2;
    word 0x08; word 0xc5; word 0xd9; word 0xef; word 0xe2; word 0xc4;
    word 0xe3; word 0x79; word 0x44; word 0xc2; word 0x00; word 0xc4;
    word 0xe3; word 0x71; word 0x44; word 0xca; word 0x11; word 0xc4;
    word 0xe3; word 0x61; word 0x44; word 0xdc; word 0x00; word 0xc5;
    word 0xe1; word 0xef; word 0xd8; word 0xc5; word 0xe1; word 0xef;
    word 0xd9; word 0xc5; word 0xf9; word 0x6f; word 0xe3; word 0xc5;
    word 0xe1; word 0x73; word 0xdb; word 0x08; word 0xc5; word 0xd9;
    word 0x73; word 0xfc; word 0x08; word 0xc5; word 0xf1; word 0xef;
    word 0xcb; word 0xc5; word 0xf9; word 0xef; word 0xc4; word 0xc5;
    word 0xf9; word 0x6f; word 0xe0; word 0xc5; word 0xf9; word 0x6f;
    word 0xd8; word 0xc5; word 0xf9; word 0x73; word 0xf0; word 0x05;
    word 0xc5; word 0xe1; word 0xef; word 0xd8; word 0xc5; word 0xf9;
    word 0x73; word 0xf0; word 0x01; word 0xc5; word 0xf9; word 0xef;
    word 0xc3; word 0xc5; word 0xf9; word 0x73; word 0xf0; word 0x39;
    word 0xc5; word 0xf9; word 0x6f; word 0xd8; word 0xc5; word 0xf9;
    word 0x73; word 0xf8; word 0x08; word 0xc5; word 0xe1; word 0x73;
    word 0xdb; word 0x08; word 0xc5; word 0xf9; word 0xef; word 0xc4;
    word 0xc5; word 0xf1; word 0xef; word 0xcb; word 0xc5; word 0xf9;
    word 0x6f; word 0xe0; word 0xc5; word 0xf9; word 0x73; word 0xd0;
    word 0x01; word 0xc5; word 0xf1; word 0xef; word 0xcc; word 0xc5;
    word 0xd9; word 0xef; word 0xe0; word 0xc5; word 0xf9; word 0x73;
    word 0xd0; word 0x05; word 0xc5; word 0xf9; word 0xef; word 0xc4;
    word 0xc5; word 0xf9; word 0x73; word 0xd0; word 0x01; word 0xc5;
    word 0xf9; word 0xef; word 0xc1; word 0xc4; word 0xe2; word 0x79;
    word 0x00; word 0xc5; word 0xc5; word 0xfa; word 0x7f; word 0x07;
    word 0xc3]:byte list`
  [0xc5; 0xfa; 0x6f; 0x2a; 0xc5; 0xfa; 0x6f; 0x16; 0xc5; 0xfa; 0x6f; 0x07;
   0xc4; 0xe2; 0x79; 0x00; 0xc5; 0xc5; 0xf9; 0x6f; 0xc8; 0xc4; 0xe3; 0x79;
   0x0f; 0xd8; 0x08; 0xc5; 0xe1; 0xef; 0xd8; 0xc4; 0xe3; 0x69; 0x0f; 0xe2;
   0x08; 0xc5; 0xd9; 0xef; 0xe2; 0xc4; 0xe3; 0x79; 0x44; 0xc2; 0x00; 0xc4;
   0xe3; 0x71; 0x44; 0xca; 0x11; 0xc4; 0xe3; 0x61; 0x44; 0xdc; 0x00; 0xc5;
   0xe1; 0xef; 0xd8; 0xc5; 0xe1; 0xef; 0xd9; 0xc5; 0xf9; 0x6f; 0xe3; 0xc5;
   0xe1; 0x73; 0xdb; 0x08; 0xc5; 0xd9; 0x73; 0xfc; 0x08; 0xc5; 0xf1; 0xef;
   0xcb; 0xc5; 0xf9; 0xef; 0xc4; 0xc5; 0xf9; 0x6f; 0xe0; 0xc5; 0xf9; 0x6f;
   0xd8; 0xc5; 0xf9; 0x73; 0xf0; 0x05; 0xc5; 0xe1; 0xef; 0xd8; 0xc5; 0xf9;
   0x73; 0xf0; 0x01; 0xc5; 0xf9; 0xef; 0xc3; 0xc5; 0xf9; 0x73; 0xf0; 0x39;
   0xc5; 0xf9; 0x6f; 0xd8; 0xc5; 0xf9; 0x73; 0xf8; 0x08; 0xc5; 0xe1; 0x73;
   0xdb; 0x08; 0xc5; 0xf9; 0xef; 0xc4; 0xc5; 0xf1; 0xef; 0xcb; 0xc5; 0xf9;
   0x6f; 0xe0; 0xc5; 0xf9; 0x73; 0xd0; 0x01; 0xc5; 0xf1; 0xef; 0xcc; 0xc5;
   0xd9; 0xef; 0xe0; 0xc5; 0xf9; 0x73; 0xd0; 0x05; 0xc5; 0xf9; 0xef; 0xc4;
   0xc5; 0xf9; 0x73; 0xd0; 0x01; 0xc5; 0xf9; 0xef; 0xc1; 0xc4; 0xe2; 0x79;
   0x00; 0xc5; 0xc5; 0xfa; 0x7f; 0x07; 0xc3];;

let GCM_GMULT_X86_EXEC = X86_MK_CORE_EXEC_RULE gcm_gmult_x86_mc;;

(* ------------------------------------------------------------------------- *)
(* Canonical byte-reverse mask constant.  VPSHUFB with this mask is          *)
(* semantically `word_reversefields 8` on int128.                            *)
(* Memory byte 0 = 0x0f -> lane 0 of dst sources byte 15 of src, etc.        *)
(* ------------------------------------------------------------------------- *)

let bswap_mask_128 = new_definition
  `bswap_mask_128 : int128 =
   word 0x000102030405060708090a0b0c0d0e0f`;;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(*                                                                           *)
(* `nonoverlapping (word pc,LENGTH mc) (Xi,16)` lets the stepper discharge   *)
(* the single `vmovdqu %xmm0,(%rdi)` store's "will not modify program code"  *)
(* side condition.  As in Milestones 4 and 5, we evaluate `LENGTH` to a      *)
(* concrete numeral before `ENSURES_INIT_TAC` via                             *)
(* `REWRITE_CONV[mc] THENC LENGTH_CONV`.                                      *)
(*                                                                           *)
(* `MAYCHANGE` frames the state change using base `ZMM*` components per      *)
(* project feedback_maychange_ymm.md (the stepper can't canonicalise derived *)
(* YMM/XMM entries).  XMM0,XMM1,XMM2,XMM3,XMM4,XMM5 are all written during   *)
(* the multiply-and-reduce chain, so ZMM0..ZMM5.                              *)
(* ------------------------------------------------------------------------- *)

let GCM_GMULT_X86_CORRECT = prove
 (`!Xi H bswap xi h pc.
      nonoverlapping (word pc,LENGTH gcm_gmult_x86_mc) (Xi,16)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST gcm_gmult_x86_mc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [Xi; H; bswap] s /\
                read (memory :> bytes128 Xi) s = xi /\
                read (memory :> bytes128 H) s = h /\
                read (memory :> bytes128 bswap) s = bswap_mask_128)
           (\s. read RIP s = word (pc + 0xba) /\
                read (memory :> bytes128 Xi) s =
                  word_reversefields 8
                    (polyval_dot (word_reversefields 8 xi) h))
           (MAYCHANGE [RIP] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes128 Xi])`,
  (* Skeleton only.  Observed stepper cost on s2n-x86-aes (2026-05-08):
     steps 1-36 take ~1min 7s user CPU (~12s user CPU reported by HOL).
     Step 37 adds +8s; step 38 adds +18s; step 39 adds +6s; step 40
     does not complete within 9 minutes of wall time.
     The growth is symbolic-state explosion: after the three
     VPCLMULQDQ rounds (steps 11-13) the reduction chain's
     VPXOR/VPSLLDQ/VPSRLDQ/VPSLLQ/VPSRLQ rules unfold into
     nested word_join / word_subword terms that do not canonicalise
     without a per-step refold ("opaque-SIMD simplify") pass.
     Milestone 7's first subtask is to provide that machinery; this
     proof will be closed once SIMD_SIMPLIFY_CONV is in scope. *)
  CHEAT_TAC);;
