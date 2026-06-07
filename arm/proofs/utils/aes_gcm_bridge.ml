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

(* The SR↔SB commutation lemma — workhorse for the                         *)
(* `aes128_cipher_arm = aes128_cipher` equivalence (still pending).         *)
(*                                                                           *)
(* The proof is byte-wise extensional: 16 separate equations of the form    *)
(* `word_subword (aes_shift_rows op) (k*8, 8) = word_subword op (perm(k)*8, *)
(*  8)` are each proved by `BITBLAST_RULE` (fast, ~25-30ms each).            *)
(* These let us simplify the LHS of the commutation by ASM_REWRITE.  The   *)
(* RHS unfolds via `WORD_SIMPLE_SUBWORD_CONV` (push word_subword through   *)
(* word_join chain).  Both sides reduce to the same 16-fold word_join of   *)
(* `aes_sub_byte joined_GF2 (word_subword op (n,8))` at matching offsets;   *)
(* `REFL_TAC` closes.                                                        *)
(*                                                                           *)
(* Why direct `BITBLAST_TAC` on the unprojected goal fails: `aes_sub_byte   *)
(* joined_GF2 X` is opaque to the BDD engine (BDD treats it as              *)
(* uninterpreted because it involves `val X` indexing into a 2048-bit       *)
(* constant).  Without bridging the indexing, the LHS's                     *)
(* `aes_sub_byte joined_GF2 (word_subword (aes_shift_rows op) (k,8))` does  *)
(* not unify with the RHS's                                                  *)
(* `aes_sub_byte joined_GF2 (word_subword op (perm(k)*8, 8))`.               *)
let AES_SUB_BYTES_SHIFT_ROWS_COMM = prove
 (`!op:128 word.
     aes_sub_bytes joined_GF2 (aes_shift_rows op) =
     aes_shift_rows (aes_sub_bytes joined_GF2 op)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(word_subword (aes_shift_rows op) (0,8) :8 word = word_subword op (0,8)) /\
    (word_subword (aes_shift_rows op) (8,8) :8 word = word_subword op (40,8)) /\
    (word_subword (aes_shift_rows op) (16,8) :8 word = word_subword op (80,8)) /\
    (word_subword (aes_shift_rows op) (24,8) :8 word = word_subword op (120,8)) /\
    (word_subword (aes_shift_rows op) (32,8) :8 word = word_subword op (32,8)) /\
    (word_subword (aes_shift_rows op) (40,8) :8 word = word_subword op (72,8)) /\
    (word_subword (aes_shift_rows op) (48,8) :8 word = word_subword op (112,8)) /\
    (word_subword (aes_shift_rows op) (56,8) :8 word = word_subword op (24,8)) /\
    (word_subword (aes_shift_rows op) (64,8) :8 word = word_subword op (64,8)) /\
    (word_subword (aes_shift_rows op) (72,8) :8 word = word_subword op (104,8)) /\
    (word_subword (aes_shift_rows op) (80,8) :8 word = word_subword op (16,8)) /\
    (word_subword (aes_shift_rows op) (88,8) :8 word = word_subword op (56,8)) /\
    (word_subword (aes_shift_rows op) (96,8) :8 word = word_subword op (96,8)) /\
    (word_subword (aes_shift_rows op) (104,8) :8 word = word_subword op (8,8)) /\
    (word_subword (aes_shift_rows op) (112,8) :8 word = word_subword op (48,8)) /\
    (word_subword (aes_shift_rows op) (120,8) :8 word = word_subword op (88,8))`
  MP_TAC THENL
   [REWRITE_TAC[aes_shift_rows; word_join_list_16_8; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REPEAT CONJ_TAC THEN CONV_TAC BITBLAST_RULE;
    STRIP_TAC THEN
    REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[word_join_list_16_8] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(RAND_CONV(REWRITE_CONV[aes_shift_rows; word_join_list_16_8]) THENC
             RAND_CONV(DEPTH_CONV EL_CONV) THENC
             RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THENC
             RAND_CONV(DEPTH_CONV NUM_RED_CONV)) THEN
    REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Byte-permutation conjugation lemmas (s136).                              *)
(*                                                                           *)
(* The byte permutation π conjugating ARM↔FIPS byte order is exactly        *)
(* `word_bytereverse` (involutive — `byterev(byterev x) = x`).  The         *)
(* ARM convention puts HOL byte 0 = NIST byte 0 = state[0,0]                 *)
(* (column-major from top-left).  The FIPS convention puts HOL byte 0       *)
(* = NIST byte 15 = state[3,3] (HOL byte k = state[(15-k) MOD 4,            *)
(* (15-k) DIV 4]) because `word 0xN..` puts byte 0 at the LSB while         *)
(* FIPS 197 numbers state bytes upper-left-first.                            *)
(*                                                                           *)
(* Concretely:                                                               *)
(*   `aes_shift_rows = byterev ∘ fips197_shift_rows ∘ byterev`              *)
(*   `aes_mix_columns = byterev ∘ fips197_mix_columns ∘ byterev`            *)
(*   `aes_sub_bytes joined_GF2 ∘ byterev = byterev ∘ aes_sub_bytes joined_GF2` *)
(*     (SubBytes is byte-wise so commutes with any byte permutation)         *)
(*                                                                           *)
(* These conjugation lemmas (proved below) imply the relationship            *)
(*                                                                           *)
(*   aes128_cipher_arm pt ks =                                               *)
(*     byterev (aes128_cipher (byterev pt) (MAP byterev ks))                 *)
(*                                                                           *)
(* (NOT `aes128_cipher_arm pt ks = aes128_cipher pt ks` — this stronger     *)
(* equality is FALSE.  Verified by direct evaluation: round 1 of the        *)
(* FIPS 197 Appendix B test vector via `aes_arm_round` produces             *)
(* `0xd4b42de533b1a833b711b95b016f84ec`, while FIPS round 1 produces        *)
(* `0xa49c7ff2689f352b6b5bea43026a5049` — different bit patterns.)          *)
(* ------------------------------------------------------------------------- *)

(* SR conjugation: aes_shift_rows = byterev ∘ fips197_shift_rows ∘ byterev. *)
(* Closes via direct BITBLAST after unfolding both shift_rows definitions    *)
(* and the underlying word_join_list_16_8.  ~0.7 sec.                       *)
let AES_SHIFT_ROWS_VS_FIPS = prove
 (`!op:128 word.
     aes_shift_rows op =
     word_bytereverse (fips197_shift_rows (word_bytereverse op))`,
  GEN_TAC THEN
  REWRITE_TAC[aes_shift_rows; fips197_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC BITBLAST_RULE);;

(* SB-byterev commutation: aes_sub_bytes joined_GF2 ∘ byterev =             *)
(* byterev ∘ aes_sub_bytes joined_GF2.  This holds because SubBytes is      *)
(* byte-wise (each output byte depends only on the corresponding input      *)
(* byte through `aes_sub_byte joined_GF2`, opaque to BITBLAST).             *)
(*                                                                           *)
(* Proof strategy: unfold aes_sub_bytes / aes_sub_bytes_select to expose    *)
(* 16 explicit `aes_sub_byte joined_GF2 (word_subword op (k*8, 8))` calls,  *)
(* then push word_bytereverse through word_join_list_16_8 (reversing the   *)
(* list — provable by BITBLAST since each list element is :8 word so      *)
(* word_bytereverse is identity at that width), then push word_bytereverse *)
(* through word_subword (each instance closes by BITBLAST).  Both sides    *)
(* reduce to the same word_join_list_16_8 of                                *)
(* `aes_sub_byte joined_GF2 (word_subword op (k*8, 8))`.                    *)
let AES_SUB_BYTES_BYTEREVERSE_COMM = prove
 (`!op:128 word.
     word_bytereverse (aes_sub_bytes joined_GF2 op) =
     aes_sub_bytes joined_GF2 (word_bytereverse op)`,
  GEN_TAC THEN
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV
   [prove(`!t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15:8 word.
            word_bytereverse
              (word_join_list_16_8
                [t0;t1;t2;t3;t4;t5;t6;t7;t8;t9;t10;t11;t12;t13;t14;t15]) =
            word_join_list_16_8
              [t15;t14;t13;t12;t11;t10;t9;t8;t7;t6;t5;t4;t3;t2;t1;t0]`,
          REWRITE_TAC[word_join_list_16_8] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          BITBLAST_TAC)] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [prove(`(word_subword (word_bytereverse (op:128 word)) (0,8) :8 word =
            word_subword op (120,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (8,8) :8 word =
            word_subword op (112,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (16,8) :8 word =
            word_subword op (104,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (24,8) :8 word =
            word_subword op (96,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (32,8) :8 word =
            word_subword op (88,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (40,8) :8 word =
            word_subword op (80,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (48,8) :8 word =
            word_subword op (72,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (56,8) :8 word =
            word_subword op (64,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (64,8) :8 word =
            word_subword op (56,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (72,8) :8 word =
            word_subword op (48,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (80,8) :8 word =
            word_subword op (40,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (88,8) :8 word =
            word_subword op (32,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (96,8) :8 word =
            word_subword op (24,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (104,8) :8 word =
            word_subword op (16,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (112,8) :8 word =
            word_subword op (8,8)) /\
           (word_subword (word_bytereverse (op:128 word)) (120,8) :8 word =
            word_subword op (0,8))`,
          REPEAT CONJ_TAC THEN BITBLAST_TAC)] THEN
  REFL_TAC);;

(* MC conjugation: aes_mix_columns = byterev ∘ fips197_mix_columns ∘ byterev. *)
(*                                                                           *)
(* Proof strategy: unfold aes_mix_columns and fips197_mix_columns to expose  *)
(* the 16-element word_join_list_16_8 of aes_mix_word calls.  `aes_mix_word` *)
(* is opaque to BITBLAST (it uses FFmul02/FFmul03 which are 2048-bit lookup *)
(* table indexings).  But:                                                   *)
(*  1. Each `aes_mix_word (byterev op) a b c d` equals                      *)
(*     `aes_mix_word op (120-a) (120-b) (120-c) (120-d)` via                *)
(*     subword/byterev rewrites (BITBLAST closes the per-byte instance),    *)
(*  2. word_bytereverse on word_join_list_16_8 reverses the list.            *)
(* Combining these turns the FIPS-side expression into the ARM-side one.    *)
let AES_MIX_COLUMNS_VS_FIPS = prove
 (`!op:128 word.
     aes_mix_columns op =
     word_bytereverse (fips197_mix_columns (word_bytereverse op))`,
  GEN_TAC THEN
  REWRITE_TAC[aes_mix_columns; fips197_mix_columns; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPEC `op:128 word`
   (prove(`!op:128 word.
     (aes_mix_word (word_bytereverse op) 120 112 104 96 =
      aes_mix_word op 0 8 16 24) /\
     (aes_mix_word (word_bytereverse op) 112 104 96 120 =
      aes_mix_word op 8 16 24 0) /\
     (aes_mix_word (word_bytereverse op) 104 96 120 112 =
      aes_mix_word op 16 24 0 8) /\
     (aes_mix_word (word_bytereverse op) 96 120 112 104 =
      aes_mix_word op 24 0 8 16) /\
     (aes_mix_word (word_bytereverse op) 88 80 72 64 =
      aes_mix_word op 32 40 48 56) /\
     (aes_mix_word (word_bytereverse op) 80 72 64 88 =
      aes_mix_word op 40 48 56 32) /\
     (aes_mix_word (word_bytereverse op) 72 64 88 80 =
      aes_mix_word op 48 56 32 40) /\
     (aes_mix_word (word_bytereverse op) 64 88 80 72 =
      aes_mix_word op 56 32 40 48) /\
     (aes_mix_word (word_bytereverse op) 56 48 40 32 =
      aes_mix_word op 64 72 80 88) /\
     (aes_mix_word (word_bytereverse op) 48 40 32 56 =
      aes_mix_word op 72 80 88 64) /\
     (aes_mix_word (word_bytereverse op) 40 32 56 48 =
      aes_mix_word op 80 88 64 72) /\
     (aes_mix_word (word_bytereverse op) 32 56 48 40 =
      aes_mix_word op 88 64 72 80) /\
     (aes_mix_word (word_bytereverse op) 24 16 8 0 =
      aes_mix_word op 96 104 112 120) /\
     (aes_mix_word (word_bytereverse op) 16 8 0 24 =
      aes_mix_word op 104 112 120 96) /\
     (aes_mix_word (word_bytereverse op) 8 0 24 16 =
      aes_mix_word op 112 120 96 104) /\
     (aes_mix_word (word_bytereverse op) 0 24 16 8 =
      aes_mix_word op 120 96 104 112)`,
    GEN_TAC THEN REWRITE_TAC[aes_mix_word] THEN
    MP_TAC(prove(`(word_subword (word_bytereverse (op:128 word)) (0,8) :8 word =
                   word_subword op (120,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (8,8) :8 word =
                   word_subword op (112,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (16,8) :8 word =
                   word_subword op (104,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (24,8) :8 word =
                   word_subword op (96,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (32,8) :8 word =
                   word_subword op (88,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (40,8) :8 word =
                   word_subword op (80,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (48,8) :8 word =
                   word_subword op (72,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (56,8) :8 word =
                   word_subword op (64,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (64,8) :8 word =
                   word_subword op (56,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (72,8) :8 word =
                   word_subword op (48,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (80,8) :8 word =
                   word_subword op (40,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (88,8) :8 word =
                   word_subword op (32,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (96,8) :8 word =
                   word_subword op (24,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (104,8) :8 word =
                   word_subword op (16,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (112,8) :8 word =
                   word_subword op (8,8)) /\
                  (word_subword (word_bytereverse (op:128 word)) (120,8) :8 word =
                   word_subword op (0,8))`,
                 REPEAT CONJ_TAC THEN BITBLAST_TAC)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL
    [`aes_mix_word op 0 8 16 24`; `aes_mix_word op 8 16 24 0`;
     `aes_mix_word op 16 24 0 8`; `aes_mix_word op 24 0 8 16`;
     `aes_mix_word op 32 40 48 56`; `aes_mix_word op 40 48 56 32`;
     `aes_mix_word op 48 56 32 40`; `aes_mix_word op 56 32 40 48`;
     `aes_mix_word op 64 72 80 88`; `aes_mix_word op 72 80 88 64`;
     `aes_mix_word op 80 88 64 72`; `aes_mix_word op 88 64 72 80`;
     `aes_mix_word op 96 104 112 120`; `aes_mix_word op 104 112 120 96`;
     `aes_mix_word op 112 120 96 104`; `aes_mix_word op 120 96 104 112`]
    (prove(`!t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15:8 word.
              word_bytereverse
                (word_join_list_16_8
                   [t0;t1;t2;t3;t4;t5;t6;t7;t8;t9;t10;t11;t12;t13;t14;t15]) =
              word_join_list_16_8
                [t15;t14;t13;t12;t11;t10;t9;t8;t7;t6;t5;t4;t3;t2;t1;t0]`,
            REWRITE_TAC[word_join_list_16_8] THEN
            CONV_TAC(DEPTH_CONV EL_CONV) THEN
            BITBLAST_TAC))) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(* TODO (Phase 11b A1, deferred — corrected target): the kernel-vs-FIPS    *)
(* cipher relationship is                                                    *)
(*                                                                           *)
(*   aes128_cipher_arm pt ks =                                               *)
(*     word_bytereverse (aes128_cipher (word_bytereverse pt)                 *)
(*                                     (MAP word_bytereverse ks))            *)
(*                                                                           *)
(* (NOT `aes128_cipher_arm pt ks = aes128_cipher pt ks` — confirmed FALSE   *)
(* by direct evaluation in s136: `aes_arm_round` on the FIPS Appendix B     *)
(* round-1 inputs gives `0xd4b42de533b1a833b711b95b016f84ec` but FIPS        *)
(* round 1 yields `0xa49c7ff2689f352b6b5bea43026a5049`.)                    *)
(*                                                                           *)
(* Proof sketch (induction on round count using the conjugations above):    *)
(*   • Define τ_i = byterev (s_arm_i).  Show by induction that under         *)
(*     ks_fips := MAP byterev ks_arm and pt_fips := byterev pt_arm,         *)
(*     `s_arm_i ⊕ ks_arm_i = byterev (s_fips_i)` for i = 1..9.              *)
(*   • Final round: ARM final = SR_arm(SB(s_arm_9 ⊕ k9)) ⊕ k10 reduces      *)
(*     via the conjugations to `byterev(SR_fips(SB(s_fips_9))) ⊕ k10`,      *)
(*     while FIPS output = SR_fips(SB(s_fips_9)) ⊕ byterev(k10).            *)
(*     Then ARM output = byterev(FIPS output ⊕ byterev(k10)) ⊕ k10          *)
(*                     = byterev(FIPS output) ⊕ k10 ⊕ k10                  *)
(*                     = byterev(FIPS output).                              *)
(*                                                                           *)
(* Open question for human direction: the right phrasing for the Phase 11   *)
(* public theorem.  Two options:                                             *)
(*   (i) keep the spec wrapper as `aes128_cipher` (FIPS-form) and            *)
(*       discharge the byterev-of-keys relation in the public theorem       *)
(*       (caller-obligation: keys-in-memory are byterev of FIPS-form keys), *)
(*  (ii) redefine `aes_gcm_encrypt_bytes` to use `aes128_cipher_arm`        *)
(*       directly — this matches what the kernel actually computes from    *)
(*       in-memory bytes, but diverges from the FIPS-197-flavoured spec    *)
(*       layer.                                                              *)
(*                                                                           *)
(* Option (ii) is closer to the kernel's actual behavior and avoids needing *)
(* a global byterev fixup at the public-theorem boundary.  Option (i) keeps *)
(* the spec textually faithful to FIPS 197 but the public theorem has to    *)
(* state both pt-byterev and key-byterev hypotheses.                        *)
(*                                                                           *)
(* Until the cipher equivalence is proved with the corrected RHS, downstream *)
(* proofs phrase algorithmic statements in terms of `aes128_cipher_arm`;    *)
(* the public byte-level theorem (Phase 11) will discharge the equivalence  *)
(* once at the top.                                                          *)

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

(* Phase 8 helper.  The kernel emits Q5/Q6/Q7 at main-loop body exit in     *)
(* the form `aese qi rk9 XOR word_insert (word_zx x_lo) (64,64) x_hi` —     *)
(* AES final-round output XOR'd with a plaintext-derived 128-bit value     *)
(* assembled by `fmov d, x_lo; fmov v.d[1], x_hi`.  The kernel's `rev64`   *)
(* of these emit forms applied at the top of the next iteration must equal *)
(* the byteswap128 of a spec-level ciphertext block.  This lemma           *)
(* decomposes `aes_gcm_rev64_int128` of the emit form into                  *)
(* word_join'd byte-reversed XORs of the AES round output halves with the *)
(* low/high plaintext-derived 64-bit halves — the canonical building block *)
(* the Phase 8 loop invariant uses to identify Q5/Q6/Q7 with byteswapped   *)
(* ciphertexts of the previous iteration.                                   *)
let AES_GCM_REV64_OF_EMIT_FORM = prove
 (`!q rk x_lo x_hi.
     aes_gcm_rev64_int128
        (word_xor (aese q rk)
                  (word_insert (word_zx x_lo :int128) (64,64) x_hi)) =
     word_join
       (word_bytereverse
          (word_xor (word_subword (aese q rk) (64,64) :int64) x_hi))
       (word_bytereverse
          (word_xor (word_subword (aese q rk) (0,64) :int64) x_lo))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aes_gcm_rev64_int128] THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 8/11 helper (A2 — emit-form ↔ ciphertext bridge).                   *)
(*                                                                           *)
(* Two lemmas connect the kernel's main-loop-body Q4..Q7 emit form (the      *)
(* shape produced by the first half of `Lenc_main_loop` after the v-block-   *)
(* level `eor` of plaintext-XOR'd-rk10 with the AESE-of-9-round output) to   *)
(* the spec-level ciphertext expression `pt XOR aes128_cipher_arm ctr ks`.   *)
(*                                                                           *)
(* Concretely, the kernel emits (e.g. for Q4) the term                       *)
(*                                                                           *)
(*    word_xor (aese s9 rk9)                                                 *)
(*             (word_insert (word_zx (pt_lo XOR rk10_lo)) (64,64)            *)
(*                          (pt_hi XOR rk10_hi))                             *)
(*                                                                           *)
(* where:                                                                    *)
(*   - `s9 = aes_arm_round^9 ctr [rk0..rk8]` is the 9-round AES output       *)
(*     (held in V0..V3 just before `aese vi, v31` for round 9),              *)
(*   - `rk10_lo` = `word_subword rk10 (0,64) :int64`,                        *)
(*     `rk10_hi` = `word_subword rk10 (64,64) :int64` are the halves of the  *)
(*     AES-128 last round key (held in scalar regs X13/X14 for the body),    *)
(*   - `pt_lo`, `pt_hi` are the 64-bit halves of the plaintext block (just   *)
(*     loaded via `ldp` from `[X0]`).                                        *)
(*                                                                           *)
(* The first lemma (KERNEL_PT_RK10_INSERT_AS_XOR) is purely structural: the  *)
(* kernel's split-half XOR-then-insert assembly equals the natural "build a  *)
(* full int128 plaintext block, then XOR with rk10".                         *)
(*                                                                           *)
(* The second lemma (AES_GCM_EMIT_FORM_AS_PT_XOR_CIPHER) chains in the AES   *)
(* round structure: when `s9` is the result of 9 `aes_arm_round`s applied to *)
(* a counter `ctr` with round keys `rk0..rk8`, the kernel emit form is       *)
(* `pt XOR aes128_cipher_arm ctr [rk0..rk10]` where `pt` is the assembled    *)
(* full plaintext block.                                                     *)
(*                                                                           *)
(* These bridges are required by Stage 1 / Stage 2 of the functional uplift  *)
(* plan: the per-N tail wrappers (B3) and the main-loop wrapper (B1) need    *)
(* to identify their byte-level memory POSTs against `pt XOR aes-cipher`     *)
(* spec terms.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Structural identity: the kernel's split-half rk10 absorption.             *)
(* Equivalent forms:                                                         *)
(*   LHS — "XOR rk10 in scalar half-by-half before inserting into v-reg":    *)
(*     word_insert (word_zx (pt_lo XOR rk10_lo)) (64,64) (pt_hi XOR rk10_hi) *)
(*   RHS — "build the full plaintext int128, then XOR rk10":                 *)
(*     word_xor (word_insert (word_zx pt_lo) (64,64) pt_hi) rk10              *)
let KERNEL_PT_RK10_INSERT_AS_XOR = prove
 (`!pt_lo pt_hi rk10:int128.
     word_insert
        (word_zx (word_xor pt_lo (word_subword rk10 (0,64) :64 word))
         :int128)
        (64,64)
        (word_xor pt_hi (word_subword rk10 (64,64) :64 word))
     = word_xor (word_insert (word_zx pt_lo :int128) (64,64) pt_hi) rk10`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The full emit-form ↔ "pt XOR aes128_cipher_arm" bridge.                   *)
(*                                                                           *)
(* When `s9` is the result of 9 `aes_arm_round`s over a counter `ctr`        *)
(* (with round keys rk0..rk8), the kernel's body-exit emit form for one of  *)
(* Q4..Q7 equals `pt XOR aes128_cipher_arm ctr [rk0..rk10]` where            *)
(* `pt = word_insert (word_zx pt_lo) (64,64) pt_hi`.                         *)
(*                                                                           *)
(* Proof: unfold `aes128_cipher_arm` to expose `aes_arm_final_round s9 rk9   *)
(* XOR rk10` on the RHS; rewrite `aese` to `aes_arm_final_round` via         *)
(* AESE_AS_ARM_FINAL_ROUND; close the residual word-arithmetic identity      *)
(* via BITBLAST.                                                             *)
let AES_GCM_EMIT_FORM_AS_PT_XOR_CIPHER = prove
 (`!ctr (rk0:int128) rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10
        pt_lo pt_hi.
     let s1 = aes_arm_round ctr rk0 in
     let s2 = aes_arm_round s1 rk1 in
     let s3 = aes_arm_round s2 rk2 in
     let s4 = aes_arm_round s3 rk3 in
     let s5 = aes_arm_round s4 rk4 in
     let s6 = aes_arm_round s5 rk5 in
     let s7 = aes_arm_round s6 rk6 in
     let s8 = aes_arm_round s7 rk7 in
     let s9 = aes_arm_round s8 rk8 in
     word_xor (aese s9 rk9)
              (word_insert
                 (word_zx (word_xor pt_lo (word_subword rk10 (0,64) :64 word))
                  :int128)
                 (64,64)
                 (word_xor pt_hi (word_subword rk10 (64,64) :64 word)))
     = word_xor (word_insert (word_zx pt_lo :int128) (64,64) pt_hi)
                (aes128_cipher_arm ctr
                   [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aes128_cipher_arm; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[AESE_AS_ARM_FINAL_ROUND] THEN
  BITBLAST_TAC);;

(* A "thin" form of the emit bridge that does not bind the 9-round state    *)
(* schedule: parametric in an opaque `s9`, identifying the kernel's emit    *)
(* form with `pt XOR (aes_arm_final_round s9 rk9 XOR rk10)`.  Useful when   *)
(* the upstream caller wants to discharge the s9 ↔ ctr correspondence       *)
(* separately (e.g. from a slice-exit ARM_STEPS chain that already has the  *)
(* 9-round expanded form in scope).                                         *)
let AES_GCM_EMIT_FORM_THIN = prove
 (`!s9 rk9 rk10 pt_lo pt_hi.
     word_xor (aese s9 rk9)
              (word_insert
                 (word_zx (word_xor pt_lo (word_subword rk10 (0,64) :64 word))
                  :int128)
                 (64,64)
                 (word_xor pt_hi (word_subword rk10 (64,64) :64 word)))
     = word_xor (word_insert (word_zx pt_lo :int128) (64,64) pt_hi)
                (word_xor (aes_arm_final_round s9 rk9) rk10)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[AESE_AS_ARM_FINAL_ROUND] THEN
  BITBLAST_TAC);;

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
(* The mathematical chain (all steps proved as lemmas below):                *)
(*                                                                           *)
(*   nist_ghash h prev_tag [c0;c1;c2;c3]                                     *)
(*     = ghash_polyval_acc (ghash_twist h) prev_tag [c0;c1;c2;c3]            *)
(*       (NIST_GHASH_IS_POLYVAL)                                             *)
(*     = polyval_reduce_prop3                                                *)
(*         (word_xor (word_pmul (prev_tag XOR c0) (h_power H 3))             *)
(*                   (ghash_wide H 2 [c1;c2;c3]))                            *)
(*       (GHASH_POLYVAL_ACC_BATCHED, with H = ghash_twist h)                 *)
(*     = (kernel's 4-block Karatsuba+reduction output, byte-swap'd back)     *)
(*       (KERNEL_4BLOCK_GHASH_BRIDGE).                                       *)
(*                                                                           *)
(* The last step decomposes into the per-block bridge (KARATSUBA_PMUL_-      *)
(* NATURAL ; KARATSUBA_COMPONENTS_BYTESWAP ; KERNEL_MODULO_CORRECT, all      *)
(* combined in KERNEL_PER_BLOCK_BRIDGE) plus the XOR-linearities of          *)
(* `karatsuba_combine` and `polyval_reduce_prop3` (KARATSUBA_COMBINE_XOR,    *)
(* POLYVAL_REDUCE_PROP3_XOR, hence KERNEL_MODULO_XOR).                       *)
(*                                                                           *)
(*   (i)   Karatsuba decomposition of `word_pmul a b`:                       *)
(*           KARATSUBA_PMUL_NATURAL                                          *)
(*   (ii)  Effect of `byteswap128` on the Karatsuba components:              *)
(*           KARATSUBA_COMPONENTS_BYTESWAP                                   *)
(*   (iii) Kernel MODULO sequence as `polyval_reduce_prop3`:                 *)
(*           KERNEL_MODULO_CORRECT                                           *)
(*                                                                           *)
(* End-to-end: KERNEL_4BLOCK_NIST_BRIDGE.                                    *)
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

(* The kernel's "modulo" reduction step: takes an (h, l, m) triple and       *)
(* combines them through the polyval reduction.  Mirrors the kernel's        *)
(* assembly sequence at lines 356–414 of                                     *)
(* arm/aes-gcm/aes_gcm_enc_kernel_aes128.S:                                  *)
(*                                                                           *)
(*   movi v8.8b, #0xc2;  shl d8, d8, #56          // c64 = 0xC2..0:64 word   *)
(*   eor  v4, v11, v9                              // v4 = l XOR h           *)
(*   pmull v7, v9, v8                              // v7 = pmul(h_lo, c64)   *)
(*   ext  v9, v9, v9, #8                           // h_swap = byteswap128 h *)
(*   eor  v10, v10, v4                             // v10 = m XOR l XOR h    *)
(*   eor  v7, v9, v7                               // v7 = h_swap XOR v7     *)
(*   eor  v10, v10, v7                             // v10 = M XOR L XOR H    *)
(*                                                 //       XOR h_swap XOR pmul(h_lo,c64) *)
(*   pmull v9, v10, v8                             // v9 = pmul(v10_lo, c64) *)
(*   eor  v11, v11, v9                             // v11 = l XOR v9_new     *)
(*   ext  v10, v10, v10, #8                        // v10 = byteswap128 v10  *)
(*   eor  v11, v11, v10                            // final = v11 XOR v10    *)
(*                                                                           *)
(* `kernel_modulo h l m` is the kernel's MODULO step abstracted: the kernel  *)
(* names its accumulators "high" (v9 ↦ h), "low" (v11 ↦ l), and "mid"        *)
(* (v10 ↦ m), and we keep that calling convention here.                      *)
let kernel_modulo = new_definition
 `kernel_modulo (h:int128) (l:int128) (m:int128) : int128 =
   let c64 = (word 0xC200000000000000 : 64 word) in
   let v4 = word_xor l h in
   let v7 = (word_pmul (word_subword h (0,64) : 64 word) c64 : int128) in
   let h_swap = byteswap128 h in
   let v10_a = word_xor m v4 in
   let v7_a = word_xor h_swap v7 in
   let v10_b = word_xor v10_a v7_a in
   let v9_new = (word_pmul (word_subword v10_b (0,64) : 64 word) c64 : int128) in
   let v11_a = word_xor l v9_new in
   let v10_swap = byteswap128 v10_b in
   word_xor v11_a v10_swap`;;

(* The kernel's MODULO chain computes exactly `polyval_reduce_prop3` of      *)
(* the natural Karatsuba assembly with arguments swapped.  The argument     *)
(* swap reflects that the kernel applies pmull2/pmull on byteswap128'd      *)
(* operands (since `htable_mem` stores the H-power table in byteswapped     *)
(* form), so the kernel's "h" accumulator (v9, computed via pmull2) holds   *)
(* the natural-low Karatsuba product, and its "l" accumulator (v11,         *)
(* computed via pmull) holds the natural-high product.                       *)
(*                                                                           *)
(* Proof: BITBLAST after expanding pmul-by-c64 via PMUL_W_64_128 (so the     *)
(* 256-bit BDD reduces to shifts + XORs; ~4s).                               *)
let KERNEL_MODULO_CORRECT = prove
 (`!h l m:int128.
    kernel_modulo h l m = polyval_reduce_prop3 (karatsuba_combine l h m)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[kernel_modulo; karatsuba_combine; polyval_reduce_prop3;
              byteswap128; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  CONV_TAC BITBLAST_RULE);;

(* Per-block bridge: composing KARATSUBA_COMPONENTS_BYTESWAP +              *)
(* KARATSUBA_PMUL_NATURAL + KERNEL_MODULO_CORRECT shows that the kernel's   *)
(* full per-block "Karatsuba + reduction" sequence (applied to one block    *)
(* with one H-power, both byteswapped per htable_mem) equals exactly        *)
(* `polyval_dot block H` — the basic POLYVAL multiplication primitive.      *)
let KERNEL_PER_BLOCK_BRIDGE = prove
 (`!block H:int128.
    (let (h, l, m) = karatsuba_components (byteswap128 block) (byteswap128 H) in
     kernel_modulo h l m) = polyval_dot block H`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[KARATSUBA_COMPONENTS_BYTESWAP] THEN
  REWRITE_TAC[karatsuba_components; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[KERNEL_MODULO_CORRECT] THEN
  REWRITE_TAC[polyval_dot] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`block:int128`; `H:int128`] KARATSUBA_PMUL_NATURAL) THEN
  REWRITE_TAC[karatsuba_components; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bilinearity / linearity facts used to chain per-block bridges into the    *)
(* 4-block accumulator the kernel actually executes.                         *)
(*                                                                           *)
(* The kernel does NOT call `kernel_modulo` 4 times; instead it XOR-         *)
(* accumulates the per-block triples (h_i, l_i, m_i) componentwise, then     *)
(* runs `kernel_modulo` once on the summed triple.  By:                      *)
(*                                                                           *)
(*   * KARATSUBA_COMBINE_XOR  — `karatsuba_combine` distributes over xor in  *)
(*     each of its three inputs (a tri-linearity statement, since the kernel *)
(*     XOR-accumulates all three), and                                       *)
(*                                                                           *)
(*   * POLYVAL_REDUCE_PROP3_XOR — `polyval_reduce_prop3` distributes over    *)
(*     XOR (the reduction is a linear function of its 256-bit input),        *)
(*                                                                           *)
(* the kernel's "accumulate-then-reduce" pattern equals "reduce-then-        *)
(* accumulate", which lets us apply KERNEL_PER_BLOCK_BRIDGE four times.      *)
(* ------------------------------------------------------------------------- *)

(* `karatsuba_combine` is XOR-linear in each of (h, l, m): summing the inputs *)
(* componentwise and combining gives the same result as combining each block  *)
(* and XORing the outputs.                                                    *)
let KARATSUBA_COMBINE_XOR = prove
 (`!h1 h2 l1 l2 m1 m2:int128.
    karatsuba_combine (word_xor h1 h2) (word_xor l1 l2) (word_xor m1 m2) =
    word_xor (karatsuba_combine h1 l1 m1) (karatsuba_combine h2 l2 m2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[karatsuba_combine] THEN
  CONV_TAC BITBLAST_RULE);;

(* `polyval_reduce_prop3` is XOR-linear: `prop3 (a XOR b) = prop3 a XOR       *)
(* prop3 b`.  This is a 4-second BITBLAST after expanding pmul-by-c64 via     *)
(* PMUL_W_64_128 (the same workaround as KERNEL_MODULO_CORRECT).             *)
let POLYVAL_REDUCE_PROP3_XOR = prove
 (`!a b:256 word.
    polyval_reduce_prop3 (word_xor a b) =
    word_xor (polyval_reduce_prop3 a) (polyval_reduce_prop3 b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_prop3; LET_DEF; LET_END_DEF; PMUL_W_64_128] THEN
  CONV_TAC BITBLAST_RULE);;

(* `kernel_modulo` is XOR-trilinear (linear in each of (h, l, m)), an        *)
(* immediate consequence of KERNEL_MODULO_CORRECT + KARATSUBA_COMBINE_XOR +  *)
(* POLYVAL_REDUCE_PROP3_XOR.  This is what makes the kernel's "accumulate    *)
(* triples first, reduce once" pattern equivalent to "reduce per block,      *)
(* sum results".                                                             *)
let KERNEL_MODULO_XOR = prove
 (`!h1 h2 l1 l2 m1 m2:int128.
    kernel_modulo (word_xor h1 h2) (word_xor l1 l2) (word_xor m1 m2) =
    word_xor (kernel_modulo h1 l1 m1) (kernel_modulo h2 l2 m2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[KERNEL_MODULO_CORRECT;
              KARATSUBA_COMBINE_XOR;
              POLYVAL_REDUCE_PROP3_XOR]);;

(* The 4-block bridge.  The kernel computes its 4-block GHASH by:           *)
(*                                                                           *)
(*   1. Decomposing each ciphertext block c_i and corresponding H-power H_i  *)
(*      (both held in byteswap128'd form per `htable_mem`) into Karatsuba    *)
(*      components (h_i, l_i, m_i).                                          *)
(*   2. Componentwise XOR-accumulating the four triples into a single         *)
(*      summed triple (H, L, M).                                              *)
(*   3. Running the kernel's MODULO chain on the summed triple.               *)
(*                                                                           *)
(* By KERNEL_MODULO_XOR followed by KERNEL_PER_BLOCK_BRIDGE applied per       *)
(* block, the resulting 128-bit value equals the XOR of four `polyval_dot`s  *)
(* (one per block × power pair).                                              *)
let KERNEL_4BLOCK_BRIDGE = prove
 (`!c0 c1 c2 c3 H0 H1 H2 H3:int128.
    (let h0,l0,m0 = karatsuba_components (byteswap128 c0) (byteswap128 H0) in
     let h1,l1,m1 = karatsuba_components (byteswap128 c1) (byteswap128 H1) in
     let h2,l2,m2 = karatsuba_components (byteswap128 c2) (byteswap128 H2) in
     let h3,l3,m3 = karatsuba_components (byteswap128 c3) (byteswap128 H3) in
     kernel_modulo (word_xor (word_xor h0 h1) (word_xor h2 h3))
                   (word_xor (word_xor l0 l1) (word_xor l2 l3))
                   (word_xor (word_xor m0 m1) (word_xor m2 m3))) =
    word_xor (word_xor (polyval_dot c0 H0) (polyval_dot c1 H1))
             (word_xor (polyval_dot c2 H2) (polyval_dot c3 H3))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[KERNEL_MODULO_XOR] THEN
  MP_TAC(SPECL [`c0:int128`; `H0:int128`] KERNEL_PER_BLOCK_BRIDGE) THEN
  MP_TAC(SPECL [`c1:int128`; `H1:int128`] KERNEL_PER_BLOCK_BRIDGE) THEN
  MP_TAC(SPECL [`c2:int128`; `H2:int128`] KERNEL_PER_BLOCK_BRIDGE) THEN
  MP_TAC(SPECL [`c3:int128`; `H3:int128`] KERNEL_PER_BLOCK_BRIDGE) THEN
  REWRITE_TAC[karatsuba_components; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REFL_TAC);;

(* `ghash_polyval_acc h a [b0; b1; b2; b3]` expressed as the XOR of four    *)
(* `polyval_dot` terms.  Direct unfolding of the BATCHED form +              *)
(* prop3-linearity.  This is the form the kernel's per-block bridge          *)
(* matches.                                                                  *)
let GHASH_POLYVAL_ACC_4DOT = prove
 (`!h a b0 b1 b2 b3:int128.
    ghash_polyval_acc h a [b0;b1;b2;b3] =
    word_xor (word_xor (polyval_dot (word_xor a b0) (h_power h 3))
                       (polyval_dot b1 (h_power h 2)))
             (word_xor (polyval_dot b2 (h_power h 1))
                       (polyval_dot b3 (h_power h 0)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`h:int128`; `[b1:int128; b2; b3]`; `a:int128`; `b0:int128`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[polyval_dot; WORD_XOR_0] THEN
  REWRITE_TAC[POLYVAL_REDUCE_PROP3_XOR; WORD_XOR_ASSOC]);;

(* The end-to-end 4-block kernel ↔ GHASH bridge.  The kernel's per-iteration *)
(* main-loop work — Karatsuba decompose 4 ciphertext blocks against H^4..H^1 *)
(* (in the kernel's stored byteswap128 form), accumulate componentwise,      *)
(* MODULO-reduce — equals `ghash_polyval_acc h prev_tag [ct0;ct1;ct2;ct3]`.  *)
(*                                                                           *)
(* The kernel naturally XORs `prev_tag` into the first ciphertext block      *)
(* before the per-block Karatsuba, matching `word_xor prev_tag ct0` here.    *)
(*                                                                           *)
(* Discharge: KERNEL_4BLOCK_BRIDGE rewrites the LHS into XOR of polyval_dots; *)
(* GHASH_POLYVAL_ACC_4DOT rewrites the RHS into the same XOR of polyval_dots.*)
let KERNEL_4BLOCK_GHASH_BRIDGE = prove
 (`!h prev_tag ct0 ct1 ct2 ct3:int128.
    (let h0,l0,m0 =
       karatsuba_components (byteswap128 (word_xor prev_tag ct0))
                            (byteswap128 (h_power h 3)) in
     let h1,l1,m1 =
       karatsuba_components (byteswap128 ct1) (byteswap128 (h_power h 2)) in
     let h2,l2,m2 =
       karatsuba_components (byteswap128 ct2) (byteswap128 (h_power h 1)) in
     let h3,l3,m3 =
       karatsuba_components (byteswap128 ct3) (byteswap128 (h_power h 0)) in
     kernel_modulo (word_xor (word_xor h0 h1) (word_xor h2 h3))
                   (word_xor (word_xor l0 l1) (word_xor l2 l3))
                   (word_xor (word_xor m0 m1) (word_xor m2 m3))) =
    ghash_polyval_acc h prev_tag [ct0; ct1; ct2; ct3]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[KERNEL_4BLOCK_BRIDGE; GHASH_POLYVAL_ACC_4DOT]);;

(* The end-to-end NIST 4-block bridge.  The kernel pre-twists its H input    *)
(* at htable-init time (so the H-power table holds powers of                  *)
(* `ghash_twist h` rather than `h`), and the spec uses `nist_ghash`, which   *)
(* by NIST_GHASH_IS_POLYVAL equals `ghash_polyval_acc (ghash_twist h) ...`.  *)
(*                                                                           *)
(* So this is just KERNEL_4BLOCK_GHASH_BRIDGE with `h ↦ ghash_twist h_spec`,  *)
(* combined with NIST_GHASH_IS_POLYVAL.                                       *)
let KERNEL_4BLOCK_NIST_BRIDGE = prove
 (`!h prev_tag ct0 ct1 ct2 ct3:int128.
    (let h0,l0,m0 =
       karatsuba_components (byteswap128 (word_xor prev_tag ct0))
                            (byteswap128 (h_power (ghash_twist h) 3)) in
     let h1,l1,m1 =
       karatsuba_components (byteswap128 ct1)
                            (byteswap128 (h_power (ghash_twist h) 2)) in
     let h2,l2,m2 =
       karatsuba_components (byteswap128 ct2)
                            (byteswap128 (h_power (ghash_twist h) 1)) in
     let h3,l3,m3 =
       karatsuba_components (byteswap128 ct3)
                            (byteswap128 (h_power (ghash_twist h) 0)) in
     kernel_modulo (word_xor (word_xor h0 h1) (word_xor h2 h3))
                   (word_xor (word_xor l0 l1) (word_xor l2 l3))
                   (word_xor (word_xor m0 m1) (word_xor m2 m3))) =
    nist_ghash h prev_tag [ct0; ct1; ct2; ct3]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL; KERNEL_4BLOCK_GHASH_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Input-binding form of the 4-block NIST bridge — matches the shape that    *)
(* the kernel's GHASH composition cut produces.                              *)
(*                                                                           *)
(* The composition cut                                                       *)
(*   AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_COMPOSED_CORRECT             *)
(* leaves Q11 in the form                                                    *)
(*   kernel_modulo (word_xor q9_in q5)                                       *)
(*                 (word_xor q11_in q6)                                      *)
(*                 (word_xor q10_in (word_pmul q4_in_lo q16_lo))             *)
(* where q5/q6 are the per-block-3 high/low Karatsuba products and the      *)
(* third argument's inner pmul is the per-block-3 mid Karatsuba product.    *)
(*                                                                           *)
(* When the per-block 0/1/2 cuts have already accumulated their Karatsuba   *)
(* contributions into q9_in/q10_in/q11_in (XOR-summed left-associatively   *)
(* over blocks 0/1/2), the kernel's final XOR with the block-3 contributions*)
(* corresponds to the left-associated 4-block sum                           *)
(*   `word_xor (word_xor (word_xor h0 h1) h2) h3` etc.                      *)
(*                                                                           *)
(* This bridge takes the kernel's input-binding shape directly (LHS of the  *)
(* assumption) and concludes the spec-form GHASH update (RHS of the         *)
(* conclusion).  The proof reduces to the right-associated bridge after     *)
(* re-associating the 4-block XOR sums.                                     *)
let KERNEL_4BLOCK_NIST_BRIDGE_LASSOC = prove
 (`!(h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128) (q5:int128) (q6:int128) (q9_in:int128) (q10_in:int128)
        (q11_in:int128) (q4_in:int128) (q16:int128).
    (let h0,l0,m0 =
       karatsuba_components (byteswap128 (word_xor prev_tag ct0))
                            (byteswap128 (h_power (ghash_twist h) 3)) in
     let h1,l1,m1 =
       karatsuba_components (byteswap128 ct1)
                            (byteswap128 (h_power (ghash_twist h) 2)) in
     let h2,l2,m2 =
       karatsuba_components (byteswap128 ct2)
                            (byteswap128 (h_power (ghash_twist h) 1)) in
     let h3,l3,m3 =
       karatsuba_components (byteswap128 ct3)
                            (byteswap128 (h_power (ghash_twist h) 0)) in
     word_xor q9_in q5 = word_xor (word_xor (word_xor h0 h1) h2) h3 /\
     word_xor q11_in q6 = word_xor (word_xor (word_xor l0 l1) l2) l3 /\
     word_xor q10_in
              (word_pmul (word_subword q4_in (0,64) :64 word)
                         (word_subword q16 (0,64) :64 word) :int128) =
     word_xor (word_xor (word_xor m0 m1) m2) m3)
    ==> kernel_modulo
            (word_xor q9_in q5) (word_xor q11_in q6)
            (word_xor q10_in
                      (word_pmul (word_subword q4_in (0,64) :64 word)
                                 (word_subword q16 (0,64) :64 word)
                       :int128)) =
        nist_ghash h prev_tag [ct0; ct1; ct2; ct3]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[karatsuba_components; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`h:int128`; `prev_tag:int128`; `ct0:int128`;
                `ct1:int128`; `ct2:int128`; `ct3:int128`]
               KERNEL_4BLOCK_NIST_BRIDGE) THEN
  REWRITE_TAC[karatsuba_components; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `!a b c d:int128.
       word_xor (word_xor a b) (word_xor c d) =
       word_xor (word_xor (word_xor a b) c) d`
   (fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* End Phase 3b/c framework.                                                 *)
(* ========================================================================= *)
