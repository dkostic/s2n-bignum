(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Register-only AES-128 single-block encryption.                            *)
(*                                                                           *)
(* Milestone 3 of the AES-GCM x86 plan: the 10-round AES-128 body as 9       *)
(* `vaesenc` instructions followed by `vaesenclast`, with the key schedule   *)
(* pre-loaded into XMM1..XMM10 and the initial state (already XOR'd with     *)
(* round key 0 by the caller) in XMM0.                                       *)
(*                                                                           *)
(*     aes128_one_block:                                                     *)
(*         vaesenc %xmm1,  %xmm0, %xmm0   # round 1                          *)
(*         vaesenc %xmm2,  %xmm0, %xmm0   # round 2                          *)
(*         ... (7 more vaesenc)                                              *)
(*         vaesenc %xmm9,  %xmm0, %xmm0   # round 9                          *)
(*         vaesenclast %xmm10, %xmm0, %xmm0 # round 10 (final)               *)
(*         ret                                                               *)
(*                                                                           *)
(* Correctness: at exit, `XMM0` equals `aes128_cipher` (FIPS 197) applied    *)
(* to the byte-reversed input state and a 11-element key schedule whose     *)
(* first round key is zero (the caller has already folded it into the input *)
(* state) and whose remaining 10 entries are the byte-reversed XMM1..XMM10. *)
(* The leading `word 0` makes the statement align with the standard         *)
(* FIPS 197 definition of `aes128_cipher` without requiring the caller to   *)
(* strip the initial AddRoundKey from the spec.                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/aes_fips197_bridge.ml";;

(* 10 rounds × 5 bytes per VEX-encoded vaesenc/vaesenclast + 1-byte RET =    *)
(* 51 bytes.  The encoding switches from the 3-byte VEX prefix `c4 e2 79`    *)
(* (B bit set) to `c4 c2 79` (B bit clear) at rounds 8–10 because           *)
(* xmm8..xmm10 live in the REX.B-extended register file.                    *)

let aes128_one_block_mc = define_assert_word_list "aes128_one_block_mc"
  `[word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc2;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc3;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc4;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc5;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc6;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc7;
    word 0xc4; word 0xc2; word 0x79; word 0xdc; word 0xc0;
    word 0xc4; word 0xc2; word 0x79; word 0xdc; word 0xc1;
    word 0xc4; word 0xc2; word 0x79; word 0xdd; word 0xc2;
    word 0xc3]:byte list`
  [0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc4; 0xe2; 0x79; 0xdc; 0xc2;
   0xc4; 0xe2; 0x79; 0xdc; 0xc3;
   0xc4; 0xe2; 0x79; 0xdc; 0xc4;
   0xc4; 0xe2; 0x79; 0xdc; 0xc5;
   0xc4; 0xe2; 0x79; 0xdc; 0xc6;
   0xc4; 0xe2; 0x79; 0xdc; 0xc7;
   0xc4; 0xc2; 0x79; 0xdc; 0xc0;
   0xc4; 0xc2; 0x79; 0xdc; 0xc1;
   0xc4; 0xc2; 0x79; 0xdd; 0xc2;
   0xc3];;

let AES128_ONE_BLOCK_EXEC = X86_MK_CORE_EXEC_RULE aes128_one_block_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(*                                                                           *)
(* As in `aes_one_round.ml`, we frame the x86 state change using `ZMM0`     *)
(* rather than `YMM0`/`XMM0` so that `SUBSUMED_MAYCHANGE_TAC` can close the *)
(* MAYCHANGE subgoal under `ENSURES_FINAL_STATE_TAC`.                       *)
(* ------------------------------------------------------------------------- *)

let AES128_ONE_BLOCK_CORRECT = prove
 (`!a k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 pc.
      ensures x86
        (\s. bytes_loaded s (word pc) (BUTLAST aes128_one_block_mc) /\
             read RIP s = word pc /\
             read XMM0 s = a /\
             read XMM1 s = k1 /\ read XMM2 s = k2 /\
             read XMM3 s = k3 /\ read XMM4 s = k4 /\
             read XMM5 s = k5 /\ read XMM6 s = k6 /\
             read XMM7 s = k7 /\ read XMM8 s = k8 /\
             read XMM9 s = k9 /\ read XMM10 s = k10)
        (\s. read RIP s = word(pc + 0x32) /\
             read XMM0 s = word_reversefields 8
               (aes128_cipher (word_reversefields 8 a)
                              [word 0;
                               word_reversefields 8 k1;
                               word_reversefields 8 k2;
                               word_reversefields 8 k3;
                               word_reversefields 8 k4;
                               word_reversefields 8 k5;
                               word_reversefields 8 k6;
                               word_reversefields 8 k7;
                               word_reversefields 8 k8;
                               word_reversefields 8 k9;
                               word_reversefields 8 k10]))
        (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM0] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int128`;
    `k1:int128`; `k2:int128`; `k3:int128`; `k4:int128`; `k5:int128`;
    `k6:int128`; `k7:int128`; `k8:int128`; `k9:int128`; `k10:int128`;
    `pc:num`] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5;
    XMM6; XMM7; XMM8; XMM9; XMM10; READ_ZEROTOP_128]) THEN
  X86_STEPS_TAC AES128_ONE_BLOCK_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN
  ASM_REWRITE_TAC[AESENC_FIPS197_BRIDGE_ALT; AESENCLAST_FIPS197_BRIDGE_ALT] THEN
  REWRITE_TAC[aes128_cipher] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256;
           ARITH_LE; ARITH_LT; ARITH;
           WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_XOR_0]);;
