(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridge lemmas for AES-128-GCM kernel verification.                        *)
(*                                                                           *)
(* This file connects the ISA-level AES + GHASH instructions used by         *)
(* `aes_gcm_enc_kernel` (AES-128 fork) to the algorithmic spec in            *)
(* `arm/proofs/utils/aes_gcm_spec.ml`.                                       *)
(*                                                                           *)
(* Three groups of lemmas:                                                   *)
(*                                                                           *)
(*   3a. AES round bridge: AESE+AESMC pair = one AES round step.             *)
(*       AESE last (without AESMC) + EOR with last round key = final round.  *)
(*       Composed: 9*(AESE+AESMC) + AESE + EOR = full AES-128 cipher.        *)
(*                                                                           *)
(*   3c. NIST byte-order bridge: rev64 v.16b + ext v,v,v,#8 = byte-reverse   *)
(*       of 16 bytes; the kernel uses this to convert between NIST byte      *)
(*       order in memory and the int128 form for the Karatsuba pmull        *)
(*       chain.  Connects to `bit_reflect128`/`NIST_GHASH_IS_POLYVAL` from   *)
(*       `common/ghash_nist_bridge.ml`.                                      *)
(*                                                                           *)
(*   3b. GHASH 4-block Karatsuba bridge: the 30+ instruction sequence        *)
(*       pmull/pmull2/eor producing v9, v10, v11 (high/mid/low 64-bit        *)
(*       accumulators) followed by `MODULO` polynomial reduction             *)
(*       (movi v8.8b, #0xc2; shl d8, d8, #56; pmull/ext/eor) computes        *)
(*       exactly `nist_ghash h prev_tag [b0;b1;b2;b3]` given the             *)
(*       Htable-in-memory precondition `htable_mem h kptr s`.  Routes        *)
(*       through `GHASH_BATCHED_FROM_HTABLE` from                            *)
(*       `common/polyval_ghash.ml`.                                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/aes_gcm_spec.ml";;
needs "arm/proofs/utils/aes.ml";;

(* ========================================================================= *)
(* Phase 3a: AES round bridge.                                               *)
(*                                                                           *)
(* The kernel encodes one full AES round as the pair:                        *)
(*                                                                           *)
(*    aese  Qd, Qrk    ; Qd := SubBytes(ShiftRows(Qd ⊕ Qrk))                  *)
(*    aesmc Qd, Qd     ; Qd := MixColumns(Qd)                                *)
(*                                                                           *)
(* Composed in HOL Light:                                                    *)
(*    aesmc (aese state rk) =                                                *)
(*      aes_mix_columns (aes_sub_bytes joined_GF2                            *)
(*        (aes_shift_rows (word_xor state rk)))                              *)
(*                                                                           *)
(* This matches the s2n-bignum `aes256_encrypt_round` shape exactly, with    *)
(* the round key absorbed into state *before* the SR/SB chain (the AES-NI    *)
(* convention).  We define an ARM-AES-NI-style round function that exposes   *)
(* this absorption explicitly.                                               *)
(* ========================================================================= *)

(* `aes_arm_round` is the s2n-bignum-style AES round, parametrised so the    *)
(* round key is absorbed into the state *before* the SR/SB/MC chain (this    *)
(* is the AES-NI convention, where the previous round's last operation      *)
(* implicitly absorbs the next round's key).  Equivalent (up to operand      *)
(* ordering) to `aes256_encrypt_round` in arm/proofs/utils/aes_encrypt_spec  *)
(* but stated with explicit absorption of the rk before SR/SB.               *)
let aes_arm_round = new_definition
 `aes_arm_round (state:int128) (rk:int128) : int128 =
    aes_mix_columns
      (aes_sub_bytes joined_GF2
         (aes_shift_rows (word_xor state rk)))`;;

(* `aes_arm_final_round` corresponds to the last AES round, which omits      *)
(* MixColumns.                                                               *)
let aes_arm_final_round = new_definition
 `aes_arm_final_round (state:int128) (rk:int128) : int128 =
    aes_sub_bytes joined_GF2 (aes_shift_rows (word_xor state rk))`;;

(* The AES-NI primitive bridge: the ARM `aesmc(aese ...)` pair computes      *)
(* exactly `aes_arm_round`.                                                  *)
let AESMC_AESE_AS_ARM_ROUND = prove
 (`!s k. aesmc (aese s k) = aes_arm_round s k`,
  REWRITE_TAC[aesmc; aese; aes_arm_round]);;

(* The AES-NI primitive bridge for the final round: the ARM `aese`           *)
(* (without AESMC) followed by an EOR with the last round key computes       *)
(* `aes_arm_final_round`.                                                    *)
let AESE_EOR_AS_ARM_FINAL_ROUND = prove
 (`!s k0 k1. word_xor (aese s k0) k1 = word_xor (aes_arm_final_round s k0) k1`,
  REWRITE_TAC[aese; aes_arm_final_round]);;

(* AES-128 cipher in AES-NI shape: 1 initial XOR (absorbed into round 1's    *)
(* AESE), then 9 full rounds, then 1 final round (no MC) with k_9, then XOR  *)
(* with k_10.                                                                *)
let aes128_cipher_arm = new_definition
 `aes128_cipher_arm (plaintext:int128) (ks:(int128) list) : int128 =
    let s1 = aes_arm_round plaintext (EL 0 ks) in
    let s2 = aes_arm_round s1 (EL 1 ks) in
    let s3 = aes_arm_round s2 (EL 2 ks) in
    let s4 = aes_arm_round s3 (EL 3 ks) in
    let s5 = aes_arm_round s4 (EL 4 ks) in
    let s6 = aes_arm_round s5 (EL 5 ks) in
    let s7 = aes_arm_round s6 (EL 6 ks) in
    let s8 = aes_arm_round s7 (EL 7 ks) in
    let s9 = aes_arm_round s8 (EL 8 ks) in
    let s10 = aes_arm_final_round s9 (EL 9 ks) in
    word_xor s10 (EL 10 ks)`;;

(* TODO: prove the equivalence between `aes128_cipher_arm` and the spec's   *)
(* `aes128_cipher` (which uses FIPS-order `fips197_round` from              *)
(* common/fips197.ml).  Both compute the same byte-level cipher because     *)
(* `joined_GF2` is constructed so SubBytes-via-joined_GF2 commutes with     *)
(* ShiftRows.  The single fact that wraps it up is:                         *)
(*                                                                           *)
(*   `aes_sub_bytes joined_GF2 (aes_shift_rows x) =                         *)
(*    aes_shift_rows (aes_sub_bytes joined_GF2 x)`                          *)
(*                                                                           *)
(* (the SR↔SB commutation).  After this, `aes128_cipher_arm pt ks =          *)
(* aes128_cipher pt ks` falls out by induction over the 10 rounds + final.  *)
(*                                                                           *)
(* This commutation is *NOT* directly closed by `BITBLAST_TAC` because       *)
(* `aes_sub_byte joined_GF2` involves a 8-bit symbolic shift into a 2048-   *)
(* bit constant `joined_GF2`, which makes the SAT instance combinatorially  *)
(* expensive.  A workable proof is byte-wise extensional: split each side   *)
(* into 16 byte projections via `WORD_SUBWORD_JOIN_LOWER`/`UPPER`, observe  *)
(* both byte projections at position `i` reduce to                          *)
(* `aes_sub_byte joined_GF2 (word_subword x (n_i, 8))` for the same `n_i`,  *)
(* and conclude.  Single-byte projection of `aes_shift_rows` does close     *)
(* under `WORD_BLAST` (fast); the obstacle is automating the                *)
(* `WORD_SUBWORD_JOIN_*` push-throughs because the dimension-index          *)
(* hypotheses must be discharged at non-power-of-2 widths (120, 112, 104,   *)
(* …).  Punted to a follow-on session.                                      *)
(*                                                                           *)
(* Until the bridge is proved, downstream proofs should phrase their        *)
(* algorithmic statements in terms of `aes128_cipher_arm` rather than        *)
(* `aes128_cipher`; the public byte-level theorem (Phase 11) will discharge *)
(* the equivalence once at the top level.                                   *)

(* ========================================================================= *)
(* Phase 3c: NIST byte-order bridge.                                         *)
(*                                                                           *)
(* The kernel applies `rev64 v.16b; ext v.16b, v.16b, v.16b, #8` to a        *)
(* 16-byte block before feeding it into the GHASH pmull chain.               *)
(*                                                                           *)
(* `rev64 v.16b` reverses the byte order WITHIN each 8-byte half.            *)
(* `ext v.16b, v.16b, v.16b, #8` swaps the high and low 8-byte halves.       *)
(*                                                                           *)
(* Composed, this is full byte-reversal of all 16 bytes — equivalently,      *)
(* the int128 `word_bytereverse` function.                                   *)
(* ========================================================================= *)

(* `rev64` on a 16-byte vector splits into two independent 8-byte byte-      *)
(* reversals.  Stated at the int128 level: take the low 64 bits, reverse    *)
(* their bytes; do the same with the high 64 bits; rejoin in the same        *)
(* high/low order.                                                           *)
let aes_gcm_rev64_int128 = new_definition
 `aes_gcm_rev64_int128 (x:int128) : int128 =
    word_join
      (word_bytereverse (word_subword x (64,64) : int64) : int64)
      (word_bytereverse (word_subword x ( 0,64) : int64) : int64)`;;

(* `ext v, v, v, #8` rotates an int128 by 64 bits — equivalent to swapping  *)
(* the high and low halves.                                                  *)
let aes_gcm_ext_swap_int128 = new_definition
 `aes_gcm_ext_swap_int128 (x:int128) : int128 =
    word_join
      (word_subword x ( 0,64) : int64)
      (word_subword x (64,64) : int64)`;;

(* The composition of `rev64` then `ext..., #8` is full byte-reversal.       *)
let REV64_EXT_IS_BYTEREVERSE = prove
 (`!x:int128.
    aes_gcm_ext_swap_int128 (aes_gcm_rev64_int128 x) = word_bytereverse x`,
  GEN_TAC THEN
  REWRITE_TAC[aes_gcm_ext_swap_int128; aes_gcm_rev64_int128] THEN
  BITBLAST_TAC);;

(* The same composition the other way: ext-then-rev64 also yields byte-     *)
(* reversal, since rev64 commutes with halving when the halves are           *)
(* swapped.                                                                  *)
let EXT_REV64_IS_BYTEREVERSE = prove
 (`!x:int128.
    aes_gcm_rev64_int128 (aes_gcm_ext_swap_int128 x) = word_bytereverse x`,
  GEN_TAC THEN
  REWRITE_TAC[aes_gcm_ext_swap_int128; aes_gcm_rev64_int128] THEN
  BITBLAST_TAC);;

(* `byteswap128` from common/polyval_ghash.ml is the half-swap variant       *)
(* used in `htable_mem` to describe the kernel's H-table layout (the         *)
(* kernel stores `H_power_k` with halves swapped relative to the             *)
(* algebraic form).  This is the same operation as `aes_gcm_ext_swap_int128` *)
(* — reused under both names for ergonomic reasons.                          *)
let AES_GCM_EXT_SWAP_IS_BYTESWAP128 = prove
 (`!x:int128. aes_gcm_ext_swap_int128 x = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[aes_gcm_ext_swap_int128; byteswap128]);;

(* The reverse direction: byte-reversal can be obtained by composing         *)
(* `aes_gcm_rev64_int128` and `aes_gcm_ext_swap_int128`.                     *)
let WORD_BYTEREVERSE_AS_REV64_EXT = prove
 (`!x:int128.
    word_bytereverse x = aes_gcm_ext_swap_int128 (aes_gcm_rev64_int128 x)`,
  REWRITE_TAC[REV64_EXT_IS_BYTEREVERSE]);;

(* ========================================================================= *)
(* Phase 3b: GHASH 4-block Karatsuba bridge — STUBBED.                       *)
(*                                                                           *)
(* The Karatsuba-Comba 4-block GHASH pattern in the kernel:                  *)
(*                                                                           *)
(*   v9  := pmull2  (high 64 of bit-rev block)  (high 64 of H_power)        *)
(*   v11 := pmull   (low  64 of bit-rev block)  (low  64 of H_power)        *)
(*   v10 := pmull   (xor of halves of bit-rev block)                        *)
(*                  (xor of halves of H_power)                               *)
(*   ... repeat for blocks 1, 2, 3 with H^4..H^1 ...                        *)
(*   v9  := xor of all four blocks' v9                                       *)
(*   v10 := xor of all four blocks' v10                                       *)
(*   v11 := xor of all four blocks' v11                                       *)
(*   ... MODULO reduction ...                                                *)
(*                                                                           *)
(* Bridge target: this whole sequence equals                                 *)
(* `nist_ghash h prev_tag [b0;b1;b2;b3]` (4-block batched GHASH).            *)
(*                                                                           *)
(* The mathematical content is in `GHASH_BATCHED_FROM_HTABLE` from           *)
(* `common/polyval_ghash.ml`; the work here is connecting the bit-level      *)
(* Karatsuba expansion in the asm to the `word_pmul` form.                   *)
(*                                                                           *)
(* TODO (>= 1 follow-on session per plan): write out the Karatsuba pattern   *)
(* as a HOL Light combinator, prove its equivalence to `word_pmul` /         *)
(* `word_xor` / `polyval_reduce_prop3`, then compose with                    *)
(* `GHASH_BATCHED_FROM_HTABLE` to get the full 4-block bridge.               *)
(* ========================================================================= *)
