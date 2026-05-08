(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256 single-block encryption with memory-loaded key schedule.          *)
(*                                                                           *)
(* Milestone 4 of the AES-GCM x86 plan (AES-256 half).  Reads the 16-byte    *)
(* plaintext from the pointer in `rsi`, the fifteen 16-byte round keys       *)
(* (k0..k14) from contiguous 16-byte slots starting at the pointer in `rdx`, *)
(* runs one initial `vpxor` with k0 followed by 13 `vaesenc` and a           *)
(* `vaesenclast`, and stores the 16-byte ciphertext to the pointer in `rdi`. *)
(*                                                                           *)
(* Correctness: the ciphertext buffer holds the byte-reversed output of the  *)
(* FIPS 197 `aes256_cipher` applied to the byte-reversed plaintext and the   *)
(* byte-reversed 15-element key schedule loaded from the `key` buffer.       *)
(* Byte-reversal arises because x86 hardware treats XMM as little-endian     *)
(* byte 0 = LSB while `fips197_round` follows the NIST big-endian layout.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/aes_fips197_bridge.ml";;
needs "x86/proofs/aes128_encrypt.ml";;   (* for WORD_REVERSEFIELDS_XOR_128 *)

(* 32 body instructions: 1 plaintext load, 15 key loads, 1 vpxor, 13 vaesenc *)
(* , 1 vaesenclast, 1 ciphertext store, 1 ret.                               *)
(* Byte count: 178 (0xb2); RET lives at pc+0xb1.                             *)

let aes256_encrypt_mc = define_assert_word_list "aes256_encrypt_mc"
  `[word 0xc5; word 0xfa; word 0x6f; word 0x06;
    word 0xc5; word 0xfa; word 0x6f; word 0x0a;
    word 0xc5; word 0xf9; word 0xef; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x4a; word 0x10;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x4a; word 0x20;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x4a; word 0x30;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x4a; word 0x40;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x4a; word 0x50;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x4a; word 0x60;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x4a; word 0x70;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x8a; word 0x80; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x8a; word 0x90; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x8a; word 0xa0; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x8a; word 0xb0; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x8a; word 0xc0; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x8a; word 0xd0; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0xe2; word 0x79; word 0xdc; word 0xc1;
    word 0xc5; word 0xfa; word 0x6f; word 0x8a; word 0xe0; word 0x00; word 0x00; word 0x00;
    word 0xc4; word 0xe2; word 0x79; word 0xdd; word 0xc1;
    word 0xc5; word 0xfa; word 0x7f; word 0x07;
    word 0xc3]:byte list`
  [0xc5; 0xfa; 0x6f; 0x06;
   0xc5; 0xfa; 0x6f; 0x0a;
   0xc5; 0xf9; 0xef; 0xc1;
   0xc5; 0xfa; 0x6f; 0x4a; 0x10;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x4a; 0x20;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x4a; 0x30;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x4a; 0x40;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x4a; 0x50;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x4a; 0x60;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x4a; 0x70;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x8a; 0x80; 0x00; 0x00; 0x00;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x8a; 0x90; 0x00; 0x00; 0x00;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x8a; 0xa0; 0x00; 0x00; 0x00;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x8a; 0xb0; 0x00; 0x00; 0x00;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x8a; 0xc0; 0x00; 0x00; 0x00;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x8a; 0xd0; 0x00; 0x00; 0x00;
   0xc4; 0xe2; 0x79; 0xdc; 0xc1;
   0xc5; 0xfa; 0x6f; 0x8a; 0xe0; 0x00; 0x00; 0x00;
   0xc4; 0xe2; 0x79; 0xdd; 0xc1;
   0xc5; 0xfa; 0x7f; 0x07;
   0xc3];;

let AES256_ENCRYPT_EXEC = X86_MK_CORE_EXEC_RULE aes256_encrypt_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let AES256_ENCRYPT_CORRECT = prove
 (`!ciphertext plaintext key
      pt k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 pc.
      nonoverlapping (word pc,LENGTH aes256_encrypt_mc) (ciphertext,16)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST aes256_encrypt_mc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [ciphertext; plaintext; key] s /\
                read (memory :> bytes128 plaintext) s = pt /\
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
                read (memory :> bytes128 (word_add key (word 176))) s = k11 /\
                read (memory :> bytes128 (word_add key (word 192))) s = k12 /\
                read (memory :> bytes128 (word_add key (word 208))) s = k13 /\
                read (memory :> bytes128 (word_add key (word 224))) s = k14)
           (\s. read RIP s = word (pc + 0xb1) /\
                read (memory :> bytes128 ciphertext) s =
                  word_reversefields 8
                    (aes256_cipher (word_reversefields 8 pt)
                       [word_reversefields 8 k0;
                        word_reversefields 8 k1;
                        word_reversefields 8 k2;
                        word_reversefields 8 k3;
                        word_reversefields 8 k4;
                        word_reversefields 8 k5;
                        word_reversefields 8 k6;
                        word_reversefields 8 k7;
                        word_reversefields 8 k8;
                        word_reversefields 8 k9;
                        word_reversefields 8 k10;
                        word_reversefields 8 k11;
                        word_reversefields 8 k12;
                        word_reversefields 8 k13;
                        word_reversefields 8 k14]))
           (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM0; ZMM1] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes128 ciphertext])`,
  MAP_EVERY X_GEN_TAC
   [`ciphertext:int64`; `plaintext:int64`; `key:int64`;
    `pt:int128`;
    `k0:int128`; `k1:int128`; `k2:int128`; `k3:int128`;
    `k4:int128`; `k5:int128`; `k6:int128`; `k7:int128`;
    `k8:int128`; `k9:int128`; `k10:int128`;
    `k11:int128`; `k12:int128`; `k13:int128`; `k14:int128`;
    `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[(REWRITE_CONV[aes256_encrypt_mc] THENC LENGTH_CONV)
                `LENGTH aes256_encrypt_mc`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC AES256_ENCRYPT_EXEC (1--32) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[AESENC_FIPS197_BRIDGE_ALT; AESENCLAST_FIPS197_BRIDGE_ALT] THEN
  REWRITE_TAC[aes256_cipher] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256;
           ARITH_LE; ARITH_LT; ARITH;
           WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_XOR_0;
           WORD_REVERSEFIELDS_XOR_128]);;
