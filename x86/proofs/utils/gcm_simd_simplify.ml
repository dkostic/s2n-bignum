(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Per-step SIMD-refold machinery for GHASH-style reduction chains.           *)
(*                                                                            *)
(* Stock `X86_STEPS_TAC` on the s2n-x86-aes checkpoint unfolds each           *)
(* VPCLMULQDQ round plus the follow-up VPXOR / VPSLLDQ / VPSRLDQ / VPSLLQ /  *)
(* VPSRLQ reduction chain into nested `word_join` / `word_subword` trees     *)
(* that do not canonicalise.  Without a refold pass the symbolic state        *)
(* explodes and later steps never terminate.                                  *)
(*                                                                            *)
(* Milestone 6 (single-block `gcm_gmult_x86`) and Milestone 7 (the stitched  *)
(* 6-way loop body in `aesni_gcm_encrypt`) both drive this machinery:         *)
(*                                                                            *)
(*   1. `SIMD_SIMPLIFY_CONV` / `SIMD_SIMPLIFY_TAC` apply                     *)
(*      `WORD_SUBWORD_AND` + `WORD_SIMPLE_SUBWORD_CONV` + word-num reduction *)
(*      to collapse byte-level permutations into closed form.  Copied        *)
(*      verbatim from `common/mlkem_mldsa.ml`, which is not in the           *)
(*      s2n-x86-aes checkpoint.                                               *)
(*   2. `VPSHUFB_BYTEREV_128` folds the 16-byte join that `vpshufb` emits    *)
(*      for `bswap_mask_128` back into `word_reversefields 8`.               *)
(*   3. `VPALIGNR_8_SWAP_128` canonicalises `vpalignr $8 x,x` (64-bit halves *)
(*      swap) and `VPALIGNR_8_SWAP_128_VIA_ZX_256` handles the same identity *)
(*      through the 128->256->128 `word_zx` round-trip the x86 stepper       *)
(*      introduces for 128-bit instructions that decode into int256 slots.  *)
(*   4. `WORD_ZX_ZX_128` strips residual `word_zx : 128 -> 256 -> 128` pairs. *)
(*   5. `GHASH_ABBREV_STEP_TAC`: after each instruction step, abbreviate the *)
(*      single largest `read SIMD_REG s = <rhs>` hypothesis (past a size      *)
(*      threshold) to a fresh variable, preventing quadratic blowup when      *)
(*      multiple registers reference the same large subtree.                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic SIMD simplification -- copied verbatim from common/mlkem_mldsa.ml *)
(* because that file is not in the s2n-x86-aes checkpoint (loading it would  *)
(* add ~5 minutes of needs to every session).  The body depends only on       *)
(* `WORD_SUBWORD_AND`, `WORD_SIMPLE_SUBWORD_CONV`, and `WORD_NUM_RED_CONV`,  *)
(* all pre-loaded in base.                                                    *)
(* ------------------------------------------------------------------------- *)

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let arm_simdable =
    can (term_match [] `read X (s:armstate):int128 = whatever`) in
  let x86_simdable =
    can (term_match [] `read X (s:x86state):int256 = whatever`) in
  let simdable tm = arm_simdable tm || x86_simdable tm in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

(* ------------------------------------------------------------------------- *)
(* VPSHUFB_BYTEREV_128: VPSHUFB with the canonical bswap mask                 *)
(* `word 0x000102030405060708090a0b0c0d0e0f` equals `word_reversefields 8`   *)
(* on int128.  The LHS is the explicit 16-byte permutation the x86 stepper   *)
(* emits when the mask is a concrete byte-reverse pattern.                    *)
(* ------------------------------------------------------------------------- *)

let VPSHUFB_BYTEREV_128 = prove
 (`!(xi:int128).
    (word_join:64 word->64 word->128 word)
      ((word_join:32 word->32 word->64 word)
        ((word_join:16 word->16 word->32 word)
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (0,8)) (word_subword xi (8,8)))
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (16,8)) (word_subword xi (24,8))))
        ((word_join:16 word->16 word->32 word)
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (32,8)) (word_subword xi (40,8)))
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (48,8)) (word_subword xi (56,8)))))
      ((word_join:32 word->32 word->64 word)
        ((word_join:16 word->16 word->32 word)
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (64,8)) (word_subword xi (72,8)))
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (80,8)) (word_subword xi (88,8))))
        ((word_join:16 word->16 word->32 word)
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (96,8)) (word_subword xi (104,8)))
          ((word_join:8 word->8 word->16 word)
            (word_subword xi (112,8)) (word_subword xi (120,8)))))
    = word_reversefields 8 xi`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* VPALIGNR_8_SWAP_128: `vpalignr $8 x,x,dst` swaps the 64-bit halves of x.  *)
(* The stepper expresses it as `subword (ushr (join x x) 64) (0,128)`.        *)
(* ------------------------------------------------------------------------- *)

let VPALIGNR_8_SWAP_128 = prove
 (`!(x:int128).
    (word_subword (word_ushr (word_join x x:int256) 64) (0,128)):int128
    = word_join ((word_subword x (0,64)):64 word)
                ((word_subword x (64,64)):64 word)`,
  CONV_TAC WORD_BLAST);;

(* Variant wrapped in the stepper's 128->256->128 `word_zx`-pair.             *)
let VPALIGNR_8_SWAP_128_VIA_ZX_256 = prove
 (`!(x:int128).
    (word_subword
     (word_ushr
       ((word_join:int128->int128->int256)
         (word_zx (word_zx x:int256):int128)
         (word_zx (word_zx x:int256):int128))
       64)
     (0,128)):int128
    = word_join ((word_subword x (0,64)):64 word)
                ((word_subword x (64,64)):64 word)`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256; ARITH_LE; ARITH_LT; LE_REFL;
           VPALIGNR_8_SWAP_128]);;

(* ------------------------------------------------------------------------- *)
(* WORD_ZX_ZX_128: the 128->256->128 `word_zx`-pair is the identity.  Used   *)
(* to clean up after VPALIGNR_8_SWAP_128_VIA_ZX_256 and other round-trips.   *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_ZX_128 = prove
 (`!(x:int128). (word_zx (word_zx x:int256):int128) = x`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* GHASH_ABBREV_STEP_TAC: after a step, find the largest                      *)
(* `read SIMD_REG s = rhs` hypothesis with |rhs| > threshold and abbreviate  *)
(* the rhs to a fresh genvar.  Without this the reduction-chain state grows  *)
(* quadratically even with the fold rewrites, because multiple registers     *)
(* reference the same large subtree.                                          *)
(* ------------------------------------------------------------------------- *)

let GHASH_ABBREV_STEP_TAC : tactic =
  let thresh = 400 in
  let is_simd_state_eq th =
    let c = concl th in
    is_eq c &&
    (let l = lhand c and r = rand c in
     (not (is_var r)) &&
     is_comb l &&
     (match rator l with
      | Comb(Const("read", _), _) -> true
      | _ -> false) &&
     String.length (string_of_term r) > thresh) in
  fun (asl, w) ->
    let candidates = filter (fun (_, th) -> is_simd_state_eq th) asl in
    let ranked =
      List.sort (fun (_,a) (_,b) ->
        compare (String.length (string_of_term (rand (concl b))))
                (String.length (string_of_term (rand (concl a)))))
      candidates in
    match ranked with
    | [] -> ALL_TAC (asl, w)
    | (_, th) :: _ ->
        let rhs = rand (concl th) in
        let gv = genvar (type_of rhs) in
        ABBREV_TAC (mk_eq (gv, rhs)) (asl, w);;
