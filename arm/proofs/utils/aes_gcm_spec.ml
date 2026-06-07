(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM specification.                                                *)
(*                                                                           *)
(* Layered on:                                                               *)
(*   - aes128_cipher  (common/fips197.ml)         FIPS 197 block cipher.     *)
(*   - nist_ghash     (common/ghash_nist_bridge.ml) NIST GHASH Horner fold.  *)
(*                                                                           *)
(* This spec describes the byte-level computation that the                   *)
(* `aes_gcm_enc_kernel` AArch64 routine implements (AES-128 fork, encrypt    *)
(* only).  Two layers:                                                       *)
(*                                                                           *)
(*   (a) `aes_gcm_encrypt_blocks`: kernel-level block-wise AES-CTR keystream *)
(*       XOR plaintext + NIST-GHASH update over the resulting ciphertext     *)
(*       blocks.  The signature mirrors what the kernel takes:               *)
(*       (number of full blocks, plaintext blocks, current Y_i counter,      *)
(*        running NIST GHASH tag, AES-128 key schedule, GHASH key H) ->      *)
(*        (ciphertext blocks, updated NIST GHASH tag, updated Y_i counter).  *)
(*                                                                           *)
(*   (b) `aes_gcm_encrypt_bytes` / `aes_gcm_decrypt_bytes`: full NIST AES-   *)
(*       128-GCM byte-level wrappers driving the kernel block math plus      *)
(*       AAD GHASH, length block, and tag finalization.  This is the         *)
(*       byte-level KAT shape used in tests/test.c::kernel_aes128_gcm_       *)
(*       encrypt.                                                            *)
(*                                                                           *)
(* Byte conventions: NIST byte order throughout.  Byte 0 of any 16-byte      *)
(* buffer corresponds to the most-significant 8 bits of the 128-bit word     *)
(* used by aes128_cipher and nist_ghash.  This matches both FIPS 197         *)
(* (`fips197_*` in common/fips197.ml) and NIST SP 800-38D.                   *)
(* ========================================================================= *)

needs "common/fips197.ml";;
needs "common/ghash_nist_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* NIST byte order conversion: byte 0 is the most-significant 8 bits.        *)
(* This differs from `bytes_to_int128` in aes_xts_common_spec.ml, which uses *)
(* little-endian (byte 0 = LSB).  GCM tests pass plaintext in NIST order, so *)
(* a NIST-byte form is the natural shape for the spec.                       *)
(* ------------------------------------------------------------------------- *)

let nist_bytes_to_int128 = define
 `nist_bytes_to_int128 (bs:byte list) : int128 =
    word_join
      (word_join
        (word_join (word_join (EL 0 bs)  (EL 1 bs)  : int16)
                   (word_join (EL 2 bs)  (EL 3 bs)  : int16) : int32)
        (word_join (word_join (EL 4 bs)  (EL 5 bs)  : int16)
                   (word_join (EL 6 bs)  (EL 7 bs)  : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 8 bs)  (EL 9 bs)  : int16)
                   (word_join (EL 10 bs) (EL 11 bs) : int16) : int32)
        (word_join (word_join (EL 12 bs) (EL 13 bs) : int16)
                   (word_join (EL 14 bs) (EL 15 bs) : int16) : int32) : int64)`;;

let int128_to_nist_bytes = define
 `int128_to_nist_bytes (w:int128) : byte list =
    [word_subword w (120, 8); word_subword w (112, 8);
     word_subword w (104, 8); word_subword w  (96, 8);
     word_subword w  (88, 8); word_subword w  (80, 8);
     word_subword w  (72, 8); word_subword w  (64, 8);
     word_subword w  (56, 8); word_subword w  (48, 8);
     word_subword w  (40, 8); word_subword w  (32, 8);
     word_subword w  (24, 8); word_subword w  (16, 8);
     word_subword w   (8, 8); word_subword w   (0, 8)]`;;

(* ------------------------------------------------------------------------- *)
(* Counter increment.                                                        *)
(*                                                                           *)
(* The kernel maintains the Y_i counter as a 16-byte value where the upper   *)
(* 12 bytes are fixed (the IV-derived prefix) and the lower 4 bytes are a    *)
(* big-endian 32-bit counter that increments per block, with wrap.  At the   *)
(* int128 level the lower 4 bytes occupy bits [0..31] (since byte 15 is the  *)
(* LSB in NIST order).                                                       *)
(* ------------------------------------------------------------------------- *)

let aes_gcm_ctr_increment = new_definition
 `aes_gcm_ctr_increment (c:int128) : int128 =
    word_or
      (word_and c (word 0xffffffffffffffffffffffff00000000))
      (word_zx
         (word_add (word_subword c (0,32) : int32) (word 1) : int32))`;;

(* ------------------------------------------------------------------------- *)
(* Kernel-level AES-CTR keystream + NIST-GHASH update.                       *)
(*                                                                           *)
(* `aes_gcm_encrypt_blocks num_blocks plaintext ctr0 tag0 keysched H` walks  *)
(*   over num_blocks 128-bit plaintext blocks, producing:                    *)
(*     - the ciphertext block list (same length),                            *)
(*     - the NIST-GHASH tag obtained by feeding the ciphertext blocks into   *)
(*       `nist_ghash H` starting from `tag0`,                                *)
(*     - the counter value reached after num_blocks BE-32 increments         *)
(*       (which the kernel stores back to ivec_io).                          *)
(*                                                                           *)
(* This is exactly the byte-level computation `ref_aes_gcm_enc_kernel` does  *)
(* in tests/ref_aes_gcm.c, restated at the int128 level.                     *)
(* ------------------------------------------------------------------------- *)

let aes_gcm_encrypt_blocks = define
 `(aes_gcm_encrypt_blocks 0 (plaintext:int128 list) (ctr:int128) (tag:int128)
                            (keysched:int128 list) (h:int128) =
        ([]:int128 list, tag, ctr)) /\
  (aes_gcm_encrypt_blocks (SUC n) plaintext ctr tag keysched h =
     let ks = aes128_cipher ctr keysched in
     let cblock = word_xor (HD plaintext) ks in
     let new_tag = nist_dot (word_xor tag cblock) h in
     let new_ctr = aes_gcm_ctr_increment ctr in
     let rec_ct, rec_tag, rec_ctr =
       aes_gcm_encrypt_blocks n (TL plaintext) new_ctr new_tag keysched h in
     (CONS cblock rec_ct, rec_tag, rec_ctr))`;;

(* ------------------------------------------------------------------------- *)
(* J0 derivation for the standard 96-bit IV case (NIST SP 800-38D 7.1).      *)
(* J0 = nonce || 0x00000001 (16 bytes total).                                *)
(* ------------------------------------------------------------------------- *)

let aes_gcm_j0_96bit_iv = new_definition
 `aes_gcm_j0_96bit_iv (nonce:byte list) : int128 =
    nist_bytes_to_int128
      (APPEND nonce
              [word 0; word 0; word 0; word 1])`;;

(* ------------------------------------------------------------------------- *)
(* AAD GHASH: feed each 16-byte block of AAD (zero-padded last block) into   *)
(* nist_ghash, starting from the all-zero accumulator.                       *)
(* ------------------------------------------------------------------------- *)

(* Pack a 16-byte chunk of `bs` starting at byte offset `i*16`, padding with *)
(* zero bytes if `bs` is exhausted before the chunk is full.                 *)
let aes_gcm_block_at = define
 `aes_gcm_block_at (bs:byte list) (i:num) : int128 =
    nist_bytes_to_int128
      (MAP (\j. if i * 16 + j < LENGTH bs then EL (i * 16 + j) bs
                else word 0) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15])`;;

(* Number of GHASH blocks needed for a byte buffer (rounded up to 16).       *)
let aes_gcm_num_blocks = new_definition
 `aes_gcm_num_blocks (n:num) : num = (n + 15) DIV 16`;;

(* Convert a byte buffer into a list of n int128 blocks (zero-padding the   *)
(* last short block if needed).  Used to feed AAD or ciphertext bytes into  *)
(* `nist_ghash`.                                                             *)
let aes_gcm_blocks_of_bytes = define
 `(aes_gcm_blocks_of_bytes 0 (bs:byte list) : int128 list = []) /\
  (aes_gcm_blocks_of_bytes (SUC n) bs =
     CONS (aes_gcm_block_at bs 0)
          (aes_gcm_blocks_of_bytes n
             (SUB_LIST (16, LENGTH bs - 16) bs)))`;;

(* ------------------------------------------------------------------------- *)
(* Byte-level AES-128-GCM full encrypt (mirrors NIST SP 800-38D Algo 4).     *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   key    : 16-byte AES-128 key (we accept the expanded schedule directly *)
(*            as a (128 word) list of length 11 for proof convenience)      *)
(*   nonce  : 12-byte IV (only 96-bit IVs supported, matching the kernel)   *)
(*   pt     : plaintext byte list                                           *)
(*   aad    : associated data byte list                                     *)
(*                                                                           *)
(* Output: (ciphertext byte list, 16-byte tag).                              *)
(*                                                                           *)
(* The structure exactly mirrors tests/ref_aes_gcm.c::ref_aes128_gcm_encrypt *)
(* and tests/test.c::kernel_aes128_gcm_encrypt.                              *)
(* ------------------------------------------------------------------------- *)

(* CTR-mode keystream: produces a list of `n` 128-bit keystream blocks       *)
(* starting from counter `ctr` (which is BE-incremented per block).         *)
let aes_gcm_ctr_keystream = define
 `(aes_gcm_ctr_keystream 0 (ctr:int128) (keysched:int128 list)
       : int128 list = []) /\
  (aes_gcm_ctr_keystream (SUC n) ctr keysched =
     CONS (aes128_cipher ctr keysched)
          (aes_gcm_ctr_keystream n (aes_gcm_ctr_increment ctr) keysched))`;;

(* Block-level AES-CTR over a list of plaintext blocks (full blocks only).  *)
let aes_gcm_ctr_encrypt_blocks = new_definition
 `aes_gcm_ctr_encrypt_blocks (pt:int128 list) (ctr:int128)
                              (keysched:int128 list) : int128 list =
    MAP2 word_xor pt (aes_gcm_ctr_keystream (LENGTH pt) ctr keysched)`;;

(* Byte-level AES-CTR over an arbitrary byte list.                          *)
(* Implementation strategy: produce ceil(LENGTH bs / 16) full keystream     *)
(* blocks, flatten to a byte list, XOR pointwise with the (zero-padded)    *)
(* plaintext byte list, then truncate back to LENGTH bs.  This avoids the  *)
(* well-founded-recursion overhead and matches what the kernel computes.    *)

(* Concatenate a list of int128 blocks into a byte list (NIST byte order). *)
let aes_gcm_bytes_of_blocks = define
 `(aes_gcm_bytes_of_blocks ([]:int128 list) : byte list = []) /\
  (aes_gcm_bytes_of_blocks (CONS w ws) =
     APPEND (int128_to_nist_bytes w) (aes_gcm_bytes_of_blocks ws))`;;

let aes_gcm_ctr_encrypt_bytes = new_definition
 `aes_gcm_ctr_encrypt_bytes (bs:byte list) (ctr:int128)
                             (keysched:int128 list) : byte list =
    let n = aes_gcm_num_blocks (LENGTH bs) in
    let ks_bytes =
      aes_gcm_bytes_of_blocks (aes_gcm_ctr_keystream n ctr keysched) in
    SUB_LIST (0, LENGTH bs)
             (MAP2 word_xor
                   (APPEND bs (REPLICATE (16 * n - LENGTH bs) (word 0)))
                   ks_bytes)`;;

(* ------------------------------------------------------------------------- *)
(* Partial-block / per-block spec helpers (Phase 11b functional uplift, A4). *)
(*                                                                           *)
(* The kernel works at the 16-byte block level even for a partial last       *)
(* block: the tail (`Lenc_blocks_{1,2,3,4}_remaining`) reads 16 bytes from   *)
(* the input buffer (caller-supplied; trailing bytes beyond `byte_len` are   *)
(* assumed valid memory), runs one full AES-128 cipher, XORs, and stores 16 *)
(* bytes of ciphertext.  Only the first `byte_len mod 16` (or 16 if exactly  *)
(* aligned) bytes of the last block are "real" ciphertext; the remainder is *)
(* unspecified-but-deterministically-derived junk.                           *)
(*                                                                           *)
(* GHASH consumes the full 16-byte ciphertext block (the kernel doesn't      *)
(* zero the tail bytes in v5 before `rev64`-ing), but the public spec        *)
(* truncates to `byte_len` bytes via SUB_LIST.                                *)
(*                                                                           *)
(* These helpers expose the per-block keystream and ciphertext cleanly so    *)
(* per-N tail wrappers (B3) can identify their POSTs against simple block-   *)
(* level expressions instead of unfolding the full byte-list machinery.      *)
(* ------------------------------------------------------------------------- *)

(* The i-th counter value: i increments of `aes_gcm_ctr_increment` from      *)
(* `ctr0`.                                                                   *)
let aes_gcm_ctr_at = new_definition
 `aes_gcm_ctr_at (ctr0:int128) (i:num) : int128 =
    ITER i aes_gcm_ctr_increment ctr0`;;

(* The i-th keystream block: AES-128 cipher applied to the i-th counter.    *)
let aes_gcm_ks_block_at = new_definition
 `aes_gcm_ks_block_at (ctr0:int128) (keysched:int128 list) (i:num) : int128 =
    aes128_cipher (aes_gcm_ctr_at ctr0 i) keysched`;;

(* The i-th ciphertext block as an int128, given block-list plaintext       *)
(* (treats trailing bytes beyond LENGTH bs as zero — matches the kernel     *)
(* reading 16 bytes per block into v4, after `eor v4, v4, v0` produces the  *)
(* corresponding ciphertext block).                                          *)
(*                                                                           *)
(* For block i fully within [0, LENGTH bs / 16) (i.e. all 16 bytes of input *)
(* present), this is exactly the spec ciphertext for that block.            *)
(* For the partial-final-block case, this is the FULL 16-byte stored block *)
(* (junk-padded with zero-XOR'd keystream tail bytes).                       *)
let aes_gcm_ct_block_at = new_definition
 `aes_gcm_ct_block_at (pt_bytes:byte list) (ctr0:int128)
                       (keysched:int128 list) (i:num) : int128 =
    word_xor (aes_gcm_block_at pt_bytes i)
             (aes_gcm_ks_block_at ctr0 keysched i)`;;

(* Number of bytes belonging to the last block of `byte_len` total bytes.    *)
(* Convention: `byte_len = 0` → 0; `byte_len > 0 ∧ 16 | byte_len` → 16;     *)
(* otherwise → `byte_len mod 16`.  Matches the kernel's "tail processes at  *)
(* least 1 byte" convention from `byte_len - 1; AND 0xFFC0; +X0` (line 64). *)
let aes_gcm_last_block_bytes = new_definition
 `aes_gcm_last_block_bytes (byte_len:num) : num =
    if byte_len = 0 then 0
    else (let r = byte_len MOD 16 in if r = 0 then 16 else r)`;;

(* "Padded plaintext byte list" for spec consumption: the input bytes plus  *)
(* enough zero padding to reach a multiple of 16.  The kernel reads from    *)
(* the actual plaintext buffer (caller-supplied) but the spec treats those  *)
(* trailing bytes as zero, since GHASH on the kernel side mixes in the     *)
(* keystream-XOR'd junk bytes; the public spec then truncates to byte_len.  *)
let aes_gcm_zero_padded_pt = new_definition
 `aes_gcm_zero_padded_pt (bs:byte list) : byte list =
    APPEND bs (REPLICATE (16 * aes_gcm_num_blocks (LENGTH bs) - LENGTH bs)
                          (word 0))`;;

(* H = AES_E(K, 0^128); the "raw" GHASH key value used by the NIST spec.    *)
let aes_gcm_h_raw = new_definition
 `aes_gcm_h_raw (keysched:int128 list) : int128 =
    aes128_cipher (word 0) keysched`;;

(* Final 128-bit length block: 64-bit BE aad-bit-len || 64-bit BE pt-bit-len *)
let aes_gcm_len_block = new_definition
 `aes_gcm_len_block (aad_bytes:num) (pt_bytes:num) : int128 =
    word_join
      (word (8 * aad_bytes) : int64)
      (word (8 * pt_bytes)  : int64)`;;

(* Full-encrypt entry point.                                                 *)
(* Returns (ciphertext, tag).                                                *)
let aes_gcm_encrypt_bytes = new_definition
 `aes_gcm_encrypt_bytes (keysched:int128 list) (nonce:byte list)
                         (pt:byte list) (aad:byte list)
        : (byte list)#(byte list) =
    let h    = aes_gcm_h_raw keysched in
    let j0   = aes_gcm_j0_96bit_iv nonce in
    let ctr0 = aes_gcm_ctr_increment j0 in
    let n_aad   = aes_gcm_num_blocks (LENGTH aad) in
    let aad_blocks = aes_gcm_blocks_of_bytes n_aad aad in
    let tag1 = nist_ghash h (word 0) aad_blocks in
    let ct = aes_gcm_ctr_encrypt_bytes pt ctr0 keysched in
    let n_ct   = aes_gcm_num_blocks (LENGTH ct) in
    let ct_blocks = aes_gcm_blocks_of_bytes n_ct ct in
    let tag2 = nist_ghash h tag1 ct_blocks in
    let len_blk = aes_gcm_len_block (LENGTH aad) (LENGTH pt) in
    let tag3 = nist_ghash h tag2 [len_blk] in
    let ekj0 = aes128_cipher j0 keysched in
    let tag  = word_xor ekj0 tag3 in
    (ct, int128_to_nist_bytes tag)`;;

(* Decrypt is the same on the keystream side (CTR is symmetric); the tag    *)
(* is computed over the ciphertext exactly as on encrypt.  The caller is   *)
(* expected to compare against the received tag.                            *)
let aes_gcm_decrypt_bytes = new_definition
 `aes_gcm_decrypt_bytes (keysched:int128 list) (nonce:byte list)
                         (ct:byte list) (aad:byte list)
        : (byte list)#(byte list) =
    let h    = aes_gcm_h_raw keysched in
    let j0   = aes_gcm_j0_96bit_iv nonce in
    let ctr0 = aes_gcm_ctr_increment j0 in

    let n_aad   = aes_gcm_num_blocks (LENGTH aad) in
    let aad_blocks = aes_gcm_blocks_of_bytes n_aad aad in
    let tag1 = nist_ghash h (word 0) aad_blocks in

    let n_ct   = aes_gcm_num_blocks (LENGTH ct) in
    let ct_blocks = aes_gcm_blocks_of_bytes n_ct ct in
    let tag2 = nist_ghash h tag1 ct_blocks in

    let len_blk = aes_gcm_len_block (LENGTH aad) (LENGTH ct) in
    let tag3 = nist_ghash h tag2 [len_blk] in

    let pt = aes_gcm_ctr_encrypt_bytes ct ctr0 keysched in

    let ekj0 = aes128_cipher j0 keysched in
    let tag  = word_xor ekj0 tag3 in

    (pt, int128_to_nist_bytes tag)`;;

(* ========================================================================= *)
(* KAT validation against NIST SP 800-38D AES-128-GCM test vector            *)
(* (mirroring KAT 0 from tests/test.c::aes128_gcm_kats):                     *)
(*                                                                           *)
(*   key   = feffe9928665731c6d6a8f9467308308                                *)
(*   nonce = cafebabefacedbaddecaf888                                        *)
(*   pt    = 0^128                                                            *)
(*   aad   = (empty)                                                          *)
(*   ct    = 9bb22ce7d9f372c1ee2b28722b25f206                                *)
(*   tag   = 271dbbbc06e78d7c6be9ca74d0baba1e                                *)
(*                                                                           *)
(* This is a staged check rather than a single CONV_TAC reduction of         *)
(* `aes_gcm_encrypt_bytes` end-to-end (which stack-overflows because the     *)
(* combined GHASH + AES + key-schedule rewriter is too aggressive).  The     *)
(* stages here cover every algebraic step of the spec on this concrete      *)
(* input:                                                                    *)
(*   1. AES-CTR ciphertext block:                                            *)
(*        aes128_cipher(J0+1, keysched) = expected ct                        *)
(*   2. GHASH key:                                                           *)
(*        H = aes128_cipher(0, keysched) = 0xb83b5337...80d53b78              *)
(*   3. tag2 = nist_dot(ct, H)                                               *)
(*        (verified to compute, value 0x44ca6712...ae6f1804)                 *)
(*   4. tag3 = nist_dot(tag2 XOR len_block, H) where len_block =             *)
(*      aes_gcm_len_block 0 16 = word 0x80                                   *)
(*   5. ekj0 = aes128_cipher(J0, keysched) = 0x3247184b...87bbb418           *)
(*   6. tag = ekj0 XOR tag3 = expected 0x271dbbbc...d0baba1e                 *)
(*                                                                           *)
(* The conjunction (ct = expected_ct) AND (tag = expected_tag) is the KAT.  *)
(* ========================================================================= *)

(* Define KAT 0 inputs as constants. *)
let kat0_gcm_keysched = new_definition
 `kat0_gcm_keysched : (128 word) list =
    aes128_key_expansion (word 0xfeffe9928665731c6d6a8f9467308308)`;;

(* Pre-compute the schedule (so all later AES applications fast-fold). *)
let KAT0_GCM_KEYSCHED_VAL =
  CONV_RULE(RAND_CONV(REWRITE_CONV[kat0_gcm_keysched] THENC
                      AES128_KEY_EXPANSION_CONV))
   (REFL `kat0_gcm_keysched`);;

(* A conv that reduces nist_dot on concrete inputs by unfolding to bit-     *)
(* level word_pmul + ghash_reduce + bit_reflect128, then applying the       *)
(* relevant word-arithmetic conversions.                                    *)
let NIST_DOT_REDUCE_CONV =
  REWRITE_CONV[nist_dot; bit_reflect128; ghash_reduce; ghash_reduce1] THENC
  DEPTH_CONV(WORD_REVERSEFIELDS_CONV ORELSEC WORD_PMUL_CONV
             ORELSEC WORD_USHR_CONV  ORELSEC WORD_SHL_CONV
             ORELSEC WORD_SUBWORD_CONV ORELSEC WORD_XOR_CONV
             ORELSEC WORD_ZX_CONV    ORELSEC NUM_RED_CONV
             ORELSEC WORD_RED_CONV);;

(* Stage 1: AES-CTR ciphertext block matches expected ct.                   *)
prove(`aes128_cipher (word 0xcafebabefacedbaddecaf88800000002 : 128 word)
                     kat0_gcm_keysched =
       word 0x9bb22ce7d9f372c1ee2b28722b25f206 : 128 word`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes128_cipher
                       KAT0_GCM_KEYSCHED_VAL)) THEN
  REFL_TAC);;

(* Stage 2: GHASH key H.                                                    *)
prove(`aes_gcm_h_raw kat0_gcm_keysched =
       word 0xb83b533708bf535d0aa6e52980d53b78 : 128 word`,
  REWRITE_TAC[aes_gcm_h_raw] THEN
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes128_cipher
                       KAT0_GCM_KEYSCHED_VAL)) THEN
  REFL_TAC);;

(* Stage 3: tag2 = nist_dot(ct, H).                                         *)
prove(`nist_dot (word 0x9bb22ce7d9f372c1ee2b28722b25f206 : 128 word)
                (word 0xb83b533708bf535d0aa6e52980d53b78 : 128 word) =
       word 0x44ca6712f1a4f33dfc7eee92ae6f1804 : 128 word`,
  CONV_TAC(LAND_CONV NIST_DOT_REDUCE_CONV) THEN REFL_TAC);;

(* Stage 4: len_block for empty AAD + 16-byte plaintext is 0x80.            *)
prove(`aes_gcm_len_block 0 16 = word 0x80 : int128`,
  REWRITE_TAC[aes_gcm_len_block] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
                     WORD_REDUCE_CONV)) THEN
  REFL_TAC);;

(* Stage 5: tag3 = nist_dot(tag2 XOR len, H).                                *)
prove(`nist_dot (word_xor (word 0x44ca6712f1a4f33dfc7eee92ae6f1804 : 128 word)
                          (word 0x80 : 128 word))
                (word 0xb83b533708bf535d0aa6e52980d53b78 : 128 word) =
       word 0x155aa3f73aa8e4d82655185c57010e06 : 128 word`,
  CONV_TAC(LAND_CONV NIST_DOT_REDUCE_CONV) THEN REFL_TAC);;

(* Stage 6: ekj0 = aes128_cipher(J0, keysched).                              *)
prove(`aes128_cipher (word 0xcafebabefacedbaddecaf88800000001 : 128 word)
                     kat0_gcm_keysched =
       word 0x3247184b3c4f69a44dbcd22887bbb418 : 128 word`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes128_cipher
                       KAT0_GCM_KEYSCHED_VAL)) THEN
  REFL_TAC);;

(* Stage 7: final tag = ekj0 XOR tag3.                                       *)
prove(`word_xor (word 0x3247184b3c4f69a44dbcd22887bbb418 : 128 word)
                (word 0x155aa3f73aa8e4d82655185c57010e06 : 128 word) =
       word 0x271dbbbc06e78d7c6be9ca74d0baba1e : 128 word`,
  CONV_TAC WORD_REDUCE_CONV);;

(* Stage 8: J0 derivation from the 12-byte nonce.                            *)
prove(`aes_gcm_j0_96bit_iv
         [word 0xca; word 0xfe; word 0xba; word 0xbe;
          word 0xfa; word 0xce; word 0xdb; word 0xad;
          word 0xde; word 0xca; word 0xf8; word 0x88] =
       word 0xcafebabefacedbaddecaf88800000001 : int128`,
  REWRITE_TAC[aes_gcm_j0_96bit_iv; APPEND; nist_bytes_to_int128] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV(map (fun n ->
    EL_CONV(subst[mk_small_numeral n,`n:num`]
      `EL n [word 0xca; word 0xfe; word 0xba; word 0xbe;
             word 0xfa; word 0xce; word 0xdb; word 0xad;
             word 0xde; word 0xca; word 0xf8; word 0x88;
             word 0; word 0; word 0; word 1]:byte`)) (0--15)))) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* Stage 9: ctr0 = J0 + 1.                                                   *)
prove(`aes_gcm_ctr_increment
         (word 0xcafebabefacedbaddecaf88800000001 : int128) =
       word 0xcafebabefacedbaddecaf88800000002 : int128`,
  REWRITE_TAC[aes_gcm_ctr_increment] THEN
  CONV_TAC WORD_REDUCE_CONV);;

