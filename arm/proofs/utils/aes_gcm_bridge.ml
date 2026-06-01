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
needs "common/karatsuba_pmul.ml";;

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

(* The AES-NI primitive bridge for the last AES round:  ARM `aese` (with no  *)
(* trailing AESMC) directly computes `aes_arm_final_round`.  This is a       *)
(* renaming bridge — the right-hand side has the same definition shape, but  *)
(* downstream proofs work with `aes_arm_final_round`/`aes_arm_round` only,   *)
(* not the raw `aese`/`aesmc` primitives.  The kernel's final round is then  *)
(* `word_xor (aes_arm_final_round s9 k9) k10` after one application.         *)
let AESE_AS_ARM_FINAL_ROUND = prove
 (`!s k. aese s k = aes_arm_final_round s k`,
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
(* the high and low halves.  This is exactly `byteswap128` from              *)
(* `common/polyval_ghash.ml` (the half-swap variant used in `htable_mem` to  *)
(* describe the kernel's H-table layout).  We use `byteswap128` directly     *)
(* downstream rather than introducing an alias.                              *)

(* The composition of `rev64` then `ext..., #8` is full byte-reversal.       *)
let REV64_EXT_IS_BYTEREVERSE = prove
 (`!x:int128.
    byteswap128 (aes_gcm_rev64_int128 x) = word_bytereverse x`,
  GEN_TAC THEN
  REWRITE_TAC[byteswap128; aes_gcm_rev64_int128] THEN
  BITBLAST_TAC);;

(* The same composition the other way: ext-then-rev64 also yields byte-     *)
(* reversal, since rev64 commutes with halving when the halves are           *)
(* swapped.                                                                  *)
let EXT_REV64_IS_BYTEREVERSE = prove
 (`!x:int128.
    aes_gcm_rev64_int128 (byteswap128 x) = word_bytereverse x`,
  GEN_TAC THEN
  REWRITE_TAC[byteswap128; aes_gcm_rev64_int128] THEN
  BITBLAST_TAC);;

(* The reverse direction: byte-reversal decomposes into rev64 then ext.     *)
let WORD_BYTEREVERSE_AS_REV64_EXT = prove
 (`!x:int128.
    word_bytereverse x = byteswap128 (aes_gcm_rev64_int128 x)`,
  REWRITE_TAC[REV64_EXT_IS_BYTEREVERSE]);;

(* ========================================================================= *)
(* Phase 3b/c: GHASH 4-block Karatsuba bridge — framework + sub-lemmas.      *)
(*                                                                           *)
(* The Karatsuba-Comba 4-block GHASH pattern in the kernel:                  *)
(*                                                                           *)
(*   v9  := pmull2  (high 64 of rev64-block)  (high 64 of H_power_stored)   *)
(*   v11 := pmull   (low  64 of rev64-block)  (low  64 of H_power_stored)   *)
(*   v10 := pmull   (xor of halves of rev64-block)                          *)
(*                  (xor of halves of H_power_stored)                        *)
(*   ... repeat for blocks 1, 2, 3 with H^4..H^1 ...                        *)
(*   v9  := xor of all four blocks' v9                                       *)
(*   v10 := xor of all four blocks' v10                                      *)
(*   v11 := xor of all four blocks' v11                                      *)
(*   ... MODULO reduction (movi v8 #0xc2; shl d8 56; pmull/ext/eor) ...     *)
(*                                                                           *)
(* Bridge target: this whole sequence equals                                 *)
(* `nist_ghash h prev_tag [c0;c1;c2;c3]` (4-block batched GHASH).            *)
(*                                                                           *)
(* The mathematical chain to discharge:                                      *)
(*                                                                           *)
(*   nist_ghash h prev_tag [c0;c1;c2;c3]                                     *)
(*     = ghash_polyval_acc (ghash_twist h) prev_tag [c0;c1;c2;c3]            *)
(*       (NIST_GHASH_IS_POLYVAL)                                             *)
(*     = polyval_reduce_prop3                                                *)
(*         (word_xor (word_pmul (prev_tag XOR c0) (h_power H 3))             *)
(*                   (ghash_wide H 2 [c1;c2;c3]))                            *)
(*       (GHASH_POLYVAL_ACC_BATCHED, with H = ghash_twist h)                 *)
(*     = (kernel's 4-block Karatsuba+reduction output, byte-swap'd back).    *)
(*                                                                           *)
(* The last step is the substantive bridge.  It in turn factors into:        *)
(*                                                                           *)
(*   (i)   How `word_pmul` decomposes via Karatsuba (pmull2 + pmull + pmull  *)
(*         on (h⊕l)*(h⊕l)).  Standard 64x64 → 128 Karatsuba.                 *)
(*   (ii)  How `byteswap128` of operands relates to `byteswap` of the 256    *)
(*         Karatsuba components (this is NOT a simple half-swap of the       *)
(*         result — see analysis below).                                     *)
(*   (iii) How the kernel's MODULO sequence implements                        *)
(*         `polyval_reduce_prop3` (256→128 reduction modulo Q(x)).           *)
(*                                                                           *)
(* TODO (>= 1 follow-on session per plan): work out (i)-(iii).  The          *)
(* simplest progression: prove (iii) first against an abstract              *)
(* 256-bit input (the kernel's reduction routine is operand-shape-           *)
(* independent), then specialize to the Karatsuba result.                    *)
(* ========================================================================= *)

(* The kernel's per-block Karatsuba 64x64-multiply triple, abstracted: given *)
(* two 128-bit operands `a` and `b`, produce the high/low/mid Karatsuba      *)
(* components (each a 128-bit polynomial multiplication output).             *)
let karatsuba_components = new_definition
 `karatsuba_components (a:int128) (b:int128) : int128 # int128 # int128 =
    let a_hi = (word_subword a (64,64) : int64) in
    let a_lo = (word_subword a ( 0,64) : int64) in
    let b_hi = (word_subword b (64,64) : int64) in
    let b_lo = (word_subword b ( 0,64) : int64) in
    let h = (word_pmul a_hi b_hi : int128) in
    let l = (word_pmul a_lo b_lo : int128) in
    let m = (word_pmul (word_xor a_hi a_lo) (word_xor b_hi b_lo) : int128) in
    (h, l, m)`;;

(* The kernel's Karatsuba-combine: assembles the 256-bit product from the    *)
(* three 128-bit components.  Since pmull and pmull2 each take one half of   *)
(* the source operands, the assembly is:                                      *)
(*    result = h * x^128 + (h XOR l XOR m) * x^64 + l                          *)
(*           = h.high : (h.low XOR m.high XOR l.high XOR h.high)              *)
(*             : (m.low XOR l.high XOR h.low XOR l.low) : l.low                *)
(* but at the kernel level this is just XORing the three 128-bit pmull        *)
(* outputs at the right offsets.                                              *)
let karatsuba_combine = new_definition
 `karatsuba_combine (h:int128) (l:int128) (m:int128) : 256 word =
    word_xor
      (word_xor (word_join (h:int128) (word 0 : int128) : 256 word)
                (word_join (word 0 : int128) (l:int128) : 256 word))
      (word_shl (word_zx (word_xor h (word_xor l m)) : 256 word) 64)`;;

(* The natural identity: Karatsuba assembly equals straight pmul on the      *)
(* original operands.  Discharged via `PMUL_KARATSUBA` from                  *)
(* `common/karatsuba_pmul.ml` (the standard schoolbook + char-2 tidy-up      *)
(* result), bridged across XOR-commutativity on the cross-term and the      *)
(* word_join/word_zx shape difference between the two formulations.         *)
let KARATSUBA_PMUL_NATURAL = prove
 (`!a b:int128.
    let h, l, m = karatsuba_components a b in
    karatsuba_combine h l m = (word_pmul a b : 256 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[karatsuba_components; karatsuba_combine] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC RAND_CONV
    [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  ONCE_REWRITE_TAC[WORD_RULE
    `word_xor (word_subword (a:int128) (0,64) :64 word)
              (word_subword a (64,64) :64 word) =
     word_xor (word_subword a (64,64) :64 word)
              (word_subword a (0,64) :64 word)`;
   WORD_RULE
    `word_xor (word_subword (b:int128) (0,64) :64 word)
              (word_subword b (64,64) :64 word) =
     word_xor (word_subword b (64,64) :64 word)
              (word_subword b (0,64) :64 word)`] THEN
  CONV_TAC BITBLAST_RULE);;

(* The kernel's pmulls operate on byteswap128'd H-power operands (since      *)
(* htable_mem stores `byteswap128(h_power h k)`).  The Karatsuba components  *)
(* with byteswap128'd a and b are related to natural ones by                  *)
(* swapping h↔l (since byteswap128 swaps the 64-bit halves of its             *)
(* operand).  The mid term is preserved because XOR is commutative.           *)
let KARATSUBA_COMPONENTS_BYTESWAP = prove
 (`!a b:int128.
    karatsuba_components (byteswap128 a) (byteswap128 b) =
      (let h, l, m = karatsuba_components a b in (l, h, m))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[karatsuba_components; byteswap128] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN
  SIMP_TAC[WORD_SUBWORD_TRIVIAL; DIMINDEX_64; LE_REFL; ARITH;
           SUB_REFL] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE
    `word_xor (word_subword (a:int128) (64,64) :64 word)
              (word_subword a (0,64) :64 word) =
     word_xor (word_subword a (0,64) :64 word)
              (word_subword a (64,64) :64 word)`;
   WORD_RULE
    `word_xor (word_subword (b:int128) (64,64) :64 word)
              (word_subword b (0,64) :64 word) =
     word_xor (word_subword b (0,64) :64 word)
              (word_subword b (64,64) :64 word)`] THEN
  REFL_TAC);;

(* The kernel's "modulo" reduction step: takes an h, l, m triple and         *)
(* combines them through the polyval reduction (matches the assembly         *)
(* sequence `movi v8.8b, #0xc2; shl d8, d8, #56; pmull v7,v9,v8;             *)
(*  ext v9,v9,v9,#8; eor v10,v10,v4; eor v10,v10,v7; pmull v9,v10,v8;        *)
(*  eor v10,v10,v9` at lines 356–402 of the kernel).                          *)
(*                                                                           *)
(* The expected algebraic content: `kernel_modulo(h, l, m)` = `byteswap128`  *)
(* of `polyval_reduce_prop3(karatsuba_combine(h, l, m))`.                    *)
(*                                                                           *)
(* TODO: define `kernel_modulo` from the kernel's actual assembly and prove  *)
(* the algebraic equality.                                                   *)

(* The end-to-end 4-block bridge.  Composes via NIST_GHASH_IS_POLYVAL,       *)
(* GHASH_BATCHED_FROM_HTABLE, the byteswap-vs-polyval-dot relation, and the  *)
(* per-block Karatsuba lemma.                                                *)
(*                                                                           *)
(* TODO: state and prove.                                                    *)

(* ========================================================================= *)
(* End Phase 3b/c framework.                                                 *)
(* ========================================================================= *)
