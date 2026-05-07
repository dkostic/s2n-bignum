(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridge lemmas between the hardware-oriented AES round functions           *)
(* `aesenc` / `aesenclast` (from `x86/proofs/aes.ml`, driven by aesni        *)
(* instructions) and the NIST FIPS 197 specification `fips197_round` /      *)
(* `fips197_final_round` (from `common/fips197.ml`).                         *)
(*                                                                           *)
(* The two formulations differ in two ways:                                  *)
(*   1. Byte ordering.  `aes_shift_rows` / `aes_mix_columns` in              *)
(*      `common/aes.ml` address bytes in XMM (little-endian) order, where    *)
(*      byte 0 is the LSB of the 128-bit word.  The FIPS 197 spec addresses  *)
(*      the same AES state array in big-endian order, where byte 0 is the    *)
(*      MSB.  The two views are related by `word_reversefields 8`.           *)
(*   2. Round ordering.  AES-NI's `aesenc` performs ShiftRows then SubBytes  *)
(*      then MixColumns then AddRoundKey; FIPS 197 Algorithm 1 performs      *)
(*      SubBytes then ShiftRows then MixColumns then AddRoundKey.  SubBytes  *)
(*      is a byte-wise operation and ShiftRows is a byte permutation, so     *)
(*      they commute — that is the only substantive proof step below.       *)
(*                                                                           *)
(* Main theorems:                                                            *)
(*                                                                           *)
(*   AESENC_FIPS197_BRIDGE:                                                  *)
(*     word_reversefields 8 (aesenc s k) =                                   *)
(*       fips197_round (word_reversefields 8 s) (word_reversefields 8 k)     *)
(*                                                                           *)
(*   AESENCLAST_FIPS197_BRIDGE:                                              *)
(*     word_reversefields 8 (aesenclast s k) =                               *)
(*       fips197_final_round                                                 *)
(*         (word_reversefields 8 s) (word_reversefields 8 k)                 *)
(*                                                                           *)
(* plus `_ALT` forms with `word_reversefields 8` pushed to the right-hand    *)
(* side (convenient for symbolic simulation where `aesenc` appears          *)
(* directly in the post-step state).                                         *)
(* ========================================================================= *)

needs "x86/proofs/aes.ml";;
needs "common/fips197.ml";;

(* ------------------------------------------------------------------------- *)
(* Helper: extracting an 8-bit byte from `word_reversefields 8 s` at         *)
(* position `8*i` equals extracting the byte at position `8*(15-i)` of the   *)
(* original 128-bit word, for all i < 16.                                    *)
(* ------------------------------------------------------------------------- *)

let SUBWORD_REVERSEFIELDS_128_8 = prove
 (`!s:128 word i. i < 16 ==>
    (word_subword (word_reversefields 8 s) (8*i,8):8 word) =
    word_subword s (8*(15-i),8)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
   (ARITH_RULE `i < 16 ==>
     i=0\/i=1\/i=2\/i=3\/i=4\/i=5\/i=6\/i=7\/
     i=8\/i=9\/i=10\/i=11\/i=12\/i=13\/i=14\/i=15`)) THEN
  CONV_TAC(NUM_REDUCE_CONV) THEN CONV_TAC WORD_BLAST);;

(* Unfolded, ready-to-rewrite form of the lemma above. *)
let SUBWORD_REVERSEFIELDS_128_8_CLAUSES = end_itlist CONJ
 (map (fun i ->
    let i_tm = mk_small_numeral i in
    let lt_thm =
      EQT_ELIM(NUM_REDUCE_CONV
        (mk_comb(mk_comb(`(<):num->num->bool`,i_tm),`16`))) in
    CONV_RULE (BINOP_CONV NUM_REDUCE_CONV)
      (MP (SPECL [`s:128 word`; i_tm] SUBWORD_REVERSEFIELDS_128_8) lt_thm))
  (0--15));;

(* ------------------------------------------------------------------------- *)
(* Helper: applying `word_reversefields 8` to a 16-byte join simply          *)
(* reverses the list of bytes.  Used to push a byte-reversal through the    *)
(* join at the outermost layer of each AES primitive.                       *)
(* ------------------------------------------------------------------------- *)

let REVERSEFIELDS_JOIN_LIST_16_8 = prove
 (`word_reversefields 8 (word_join_list_16_8
    [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
     b8; b9; b10; b11; b12; b13; b14; b15]) =
   word_join_list_16_8
    [b15; b14; b13; b12; b11; b10; b9; b8;
     b7; b6; b5; b4; b3; b2; b1; b0]`,
  REWRITE_TAC([word_join_list_16_8] @ EL_16_8_CLAUSES) THEN
  CONV_TAC WORD_BLAST);;

(* Helper: every per-byte extraction from an explicit 16-byte join. *)
let SUBWORD_WORD_JOIN_LIST_16_8 = prove
 (`word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (0,8) = b15 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (8,8) = b14 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (16,8) = b13 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (24,8) = b12 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (32,8) = b11 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (40,8) = b10 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (48,8) = b9 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (56,8) = b8 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (64,8) = b7 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (72,8) = b6 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (80,8) = b5 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (88,8) = b4 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (96,8) = b3 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (104,8) = b2 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (112,8) = b1 /\
   word_subword (word_join_list_16_8
     [b0:8 word; b1; b2; b3; b4; b5; b6; b7;
      b8; b9; b10; b11; b12; b13; b14; b15]) (120,8) = b0`,
  REWRITE_TAC([word_join_list_16_8] @ EL_16_8_CLAUSES) THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Component bridges: each AES round primitive on the hardware side (with a *)
(* byte-reversal applied to the output) equals the corresponding FIPS 197   *)
(* primitive applied to the byte-reversed input.                            *)
(* ------------------------------------------------------------------------- *)

let AES_SHIFT_ROWS_FIPS197 = prove
 (`!s:128 word.
    word_reversefields 8 (aes_shift_rows s) =
    fips197_shift_rows (word_reversefields 8 s)`,
  GEN_TAC THEN
  REWRITE_TAC[aes_shift_rows; fips197_shift_rows;
              REVERSEFIELDS_JOIN_LIST_16_8;
              SUBWORD_REVERSEFIELDS_128_8_CLAUSES]);;

let AES_SUB_BYTES_FIPS197 = prove
 (`!s:128 word.
    word_reversefields 8 (aes_sub_bytes joined_GF2 s) =
    fips197_sub_bytes (word_reversefields 8 s)`,
  GEN_TAC THEN
  REWRITE_TAC[aes_sub_bytes; fips197_sub_bytes; aes_sub_bytes_select;
              REVERSEFIELDS_JOIN_LIST_16_8] THEN
  CONV_TAC (DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[SUBWORD_REVERSEFIELDS_128_8_CLAUSES]);;

let AES_MIX_COLUMNS_FIPS197 = prove
 (`!s:128 word.
    word_reversefields 8 (aes_mix_columns s) =
    fips197_mix_columns (word_reversefields 8 s)`,
  GEN_TAC THEN
  REWRITE_TAC[aes_mix_columns] THEN
  CONV_TAC (DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REVERSEFIELDS_JOIN_LIST_16_8] THEN
  REWRITE_TAC[fips197_mix_columns; aes_mix_word] THEN
  CONV_TAC (DEPTH_CONV let_CONV) THEN
  CONV_TAC (DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[SUBWORD_REVERSEFIELDS_128_8_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* FIPS 197 SubBytes and ShiftRows commute (SubBytes is byte-wise,          *)
(* ShiftRows is a byte permutation).                                        *)
(* ------------------------------------------------------------------------- *)

let FIPS197_SUB_SHIFT_COMMUTE = prove
 (`!s:128 word.
    fips197_sub_bytes (fips197_shift_rows s) =
    fips197_shift_rows (fips197_sub_bytes s)`,
  GEN_TAC THEN
  REWRITE_TAC[fips197_sub_bytes; fips197_shift_rows; aes_sub_bytes;
              aes_sub_bytes_select; SUBWORD_WORD_JOIN_LIST_16_8] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SUBWORD_WORD_JOIN_LIST_16_8]);;

(* ========================================================================= *)
(* Main theorems                                                             *)
(* ========================================================================= *)

let AESENC_FIPS197_BRIDGE = prove
 (`!s k:128 word.
    word_reversefields 8 (aesenc s k) =
    fips197_round (word_reversefields 8 s) (word_reversefields 8 k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aesenc; fips197_round] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM FIPS197_SUB_SHIFT_COMMUTE;
              GSYM AES_MIX_COLUMNS_FIPS197;
              GSYM AES_SUB_BYTES_FIPS197;
              GSYM AES_SHIFT_ROWS_FIPS197;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

let AESENCLAST_FIPS197_BRIDGE = prove
 (`!s k:128 word.
    word_reversefields 8 (aesenclast s k) =
    fips197_final_round (word_reversefields 8 s) (word_reversefields 8 k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aesenclast; fips197_final_round] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM FIPS197_SUB_SHIFT_COMMUTE;
              GSYM AES_SUB_BYTES_FIPS197;
              GSYM AES_SHIFT_ROWS_FIPS197;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

(* Alternative forms: `word_reversefields 8` on the FIPS-197 side.           *)
(* Convenient when `aesenc` / `aesenclast` appear directly in a             *)
(* post-step symbolic state and we want to rewrite them into the spec form. *)

let AESENC_FIPS197_BRIDGE_ALT = prove
 (`!s k:128 word.
    aesenc s k =
    word_reversefields 8
      (fips197_round (word_reversefields 8 s) (word_reversefields 8 k))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM AESENC_FIPS197_BRIDGE;
              WORD_REVERSEFIELDS_REVERSEFIELDS]);;

let AESENCLAST_FIPS197_BRIDGE_ALT = prove
 (`!s k:128 word.
    aesenclast s k =
    word_reversefields 8
      (fips197_final_round (word_reversefields 8 s)
                           (word_reversefields 8 k))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM AESENCLAST_FIPS197_BRIDGE;
              WORD_REVERSEFIELDS_REVERSEFIELDS]);;
