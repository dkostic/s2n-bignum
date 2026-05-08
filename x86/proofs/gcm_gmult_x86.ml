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
needs "common/karatsuba_pmul.ml";; (* PMUL_KARATSUBA *)

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
(* Per-step SIMD-refold machinery for the GHASH reduction chain.              *)
(*                                                                            *)
(* Stock `X86_STEPS_TAC` on s2n-x86-aes unfolds the three VPCLMULQDQ rounds   *)
(* plus the following VPXOR / VPSLLDQ / VPSRLDQ / VPSLLQ / VPSRLQ reduction   *)
(* chain into nested `word_join` / `word_subword` trees that do not           *)
(* canonicalise; without a refold pass, state explodes and steps 37+ never    *)
(* terminate.  Three ingredients together tame the state:                     *)
(*                                                                            *)
(*   1. `SIMD_SIMPLIFY_CONV` (from common/mlkem_mldsa.ml; re-defined inline   *)
(*       here since that file is not in the s2n-x86-aes checkpoint) applies  *)
(*       `WORD_SUBWORD_AND` / `WORD_SIMPLE_SUBWORD_CONV` / word-num reduction *)
(*       to collapse byte-level permutations into closed form.                *)
(*   2. A small set of fold rewrites -- `VPSHUFB_BYTEREV_128` collapses the   *)
(*       byte-reverse join back into `word_reversefields 8`;                  *)
(*       `VPALIGNR_8_SWAP_128_VIA_ZX_256` canonicalises the `vpalignr $8`     *)
(*       halves-swap through the 128->256->128 zx round trip the stepper      *)
(*       introduces; `WORD_ZX_ZX_128` strips the resulting `word_zx`-pair.    *)
(*   3. `GHASH_ABBREV_STEP_TAC`: after each step, find the single largest    *)
(*       `read SIMD_REG s = <rhs>` hypothesis whose rhs grew past a size      *)
(*       threshold and abbreviate it to a fresh variable, preventing          *)
(*       quadratic blowup when the same subtree is referenced multiple times  *)
(*       across the reduction chain.                                          *)
(*                                                                            *)
(* With this combination, all 41 instruction steps complete in under 5s user  *)
(* CPU on s2n-x86-aes and `ENSURES_FINAL_STATE_TAC` closes the frame goal.    *)
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

(* VPSHUFB with `bswap_mask_128` = `word_reversefields 8` on int128.          *)
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

(* VPALIGNR $8 on (x,x): swap 64-bit halves.                                  *)
let VPALIGNR_8_SWAP_128 = prove
 (`!(x:int128).
    (word_subword (word_ushr (word_join x x:int256) 64) (0,128)):int128
    = word_join ((word_subword x (0,64)):64 word)
                ((word_subword x (64,64)):64 word)`,
  CONV_TAC WORD_BLAST);;

(* As above but with the stepper's 128->256->128 `word_zx`-pair wrappers.     *)
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

(* `word_zx : 128 -> 256 -> 128 = id` cleanup after VPALIGNR fold.            *)
let WORD_ZX_ZX_128 = prove
 (`!(x:int128). (word_zx (word_zx x:int256):int128) = x`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_128; DIMINDEX_256; ARITH]);;

(* Abbreviate the biggest `read SIMD_REG s = rhs` once per step so subsequent *)
(* instructions reference a variable instead of rebuilding the whole subtree. *)
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

(* ------------------------------------------------------------------------- *)
(* Helpers for the final GF(2) identity closing Milestone 6.                  *)
(*                                                                            *)
(* The stepper-produced expression is the hand-written Karatsuba + Prop 3    *)
(* reduction in terms of six per-step abbreviations over the three 64x64     *)
(* polynomial products `pLo = (xi_lo)*(h_lo)`, `pHi = (xi_hi)*(h_hi)`,        *)
(* `pMid = (xi_lo ^ xi_hi)*(h_lo ^ h_hi)`.  The RHS is                        *)
(* `polyval_dot = polyval_reduce_prop3 (word_pmul xi h : int256)`.  Both      *)
(* sides become expressions in `pLo`, `pHi`, `pMid` after:                    *)
(*                                                                            *)
(*   1. Unfolding the RHS `word_pmul xi h` via `PMUL_KARATSUBA`.              *)
(*   2. Extracting the four 64-bit limbs of the 256-bit Karatsuba product    *)
(*      via `KARATSUBA_LIMB_{0_63,64_127,128_191,192_255}` (see aws-lc's      *)
(*      `arm/proofs/gcm_gmult_v8_nist.ml` PR for the arm analogue).           *)
(*   3. Expanding `word_pmul _ W` into XOR of shifts via `PMUL_W_64_128`.    *)
(*   4. Abbreviating `pLo`, `pHi`, `pMid` so the bit-level identity is in    *)
(*      only three 128-bit free variables.                                    *)
(*   5. Decomposing the 128-bit equation into two 64-bit lanes via            *)
(*      `WORD_EQ_LANES_128_LOCAL` and closing each lane with `BITBLAST_TAC`. *)
(*                                                                            *)
(* Empirically the two 64-bit BITBLAST_TAC calls build BDDs of 6k and 9k     *)
(* nodes over 385 Boolean variables and close in ~8 s user CPU on            *)
(* s2n-x86-aes.  The key to making BITBLAST tractable is step (4): with the  *)
(* three Karatsuba products opaque, the 64-bit BDD depends on only 3 x 128 + *)
(* 128 + 1 = 513 literal slots before CSE, which BITBLAST compiles in        *)
(* seconds; without the abbreviations the stepper's fully-unfolded form has  *)
(* >2000 leaf variables and blows up.                                         *)
(* ------------------------------------------------------------------------- *)

(* Flattened `word_pmul` Karatsuba identity (let-binders stripped). *)
let PMUL_KARATSUBA_FLAT = CONV_RULE(DEPTH_CONV let_CONV) PMUL_KARATSUBA;;

(* Fold `subword(xor(join(lo,hi), x), 0, 64) = xor(subword(x,0,64),           *)
(* subword(x,64,64))` — the canonical form `vpalignr $8 ; vpxor` emits for    *)
(* computing the Karatsuba middle operand.                                    *)
let MID_SUBWORD_FOLD = prove
 (`!a:int128.
    word_subword
      (word_xor ((word_join:int64->int64->int128)
         (word_subword a (0,64)) (word_subword a (64,64))) a)
      (0,64):int64
    = word_xor (word_subword a (0,64)) (word_subword a (64,64))`,
  CONV_TAC WORD_BLAST);;

(* 128-bit equality decomposes into two independent 64-bit lane equalities.   *)
let WORD_EQ_LANES_128_LOCAL = prove
 (`!(x:int128) (y:int128).
    x = y <=>
    (word_subword x (0,64):int64) = word_subword y (0,64) /\
    (word_subword x (64,64):int64) = word_subword y (64,64)`,
  BITBLAST_TAC);;

(* The four 64-bit limbs of the Karatsuba 256-bit product in terms of the    *)
(* 128-bit partials xl = lo*lo, xh = hi*hi, mid = lo*hi ^ hi*lo (or the      *)
(* Karatsuba xor-variant).  Pattern-for-pattern copy of                       *)
(* `KARATSUBA_LIMB_{0_63,...,192_255}` in the arm PR #390 (see                *)
(* arm/proofs/gcm_gmult_v8_nist.ml).                                          *)

let KARATSUBA_LIMB_0_63 = prove
 (`!(xl:int128) (xh:int128) (mid:int128).
    word_subword
      (word_xor (word_xor (word_zx xl : int256)
                          (word_shl (word_zx mid : int256) 64))
                (word_shl (word_zx xh : int256) 128))
      (0,64) : int64 =
    word_subword xl (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_64_127 = prove
 (`!(xl:int128) (xh:int128) (mid:int128).
    word_subword
      (word_xor (word_xor (word_zx xl : int256)
                          (word_shl (word_zx mid : int256) 64))
                (word_shl (word_zx xh : int256) 128))
      (64,64) : int64 =
    word_xor (word_subword xl (64,64)) (word_subword mid (0,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_128_191 = prove
 (`!(xl:int128) (xh:int128) (mid:int128).
    word_subword
      (word_xor (word_xor (word_zx xl : int256)
                          (word_shl (word_zx mid : int256) 64))
                (word_shl (word_zx xh : int256) 128))
      (128,64) : int64 =
    word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_192_255 = prove
 (`!(xl:int128) (xh:int128) (mid:int128).
    word_subword
      (word_xor (word_xor (word_zx xl : int256)
                          (word_shl (word_zx mid : int256) 64))
                (word_shl (word_zx xh : int256) 128))
      (192,64) : int64 =
    word_subword xh (64,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMBS =
  CONJ (CONJ KARATSUBA_LIMB_0_63 KARATSUBA_LIMB_64_127)
       (CONJ KARATSUBA_LIMB_128_191 KARATSUBA_LIMB_192_255);;

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
  MAP_EVERY X_GEN_TAC
   [`Xi:int64`; `H:int64`; `bswap:int64`;
    `xi:int128`; `h:int128`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[(REWRITE_CONV[gcm_gmult_x86_mc] THENC LENGTH_CONV)
                `LENGTH gcm_gmult_x86_mc`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bswap_mask_128]) THEN
  MAP_EVERY (fun n ->
    X86_STEPS_TAC GCM_GMULT_X86_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [VPSHUFB_BYTEREV_128;
      VPALIGNR_8_SWAP_128_VIA_ZX_256;
      WORD_ZX_ZX_128]) THEN
    GHASH_ABBREV_STEP_TAC)
   (1--41) THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o
    check (can (term_match[] `read (memory :> bytes128 xi) s41 = w`) o concl)) THEN
  AP_TERM_TAC THEN
  (* Reorient any `<expr> = read YMM_ s41` assumption produced by the stepper
     so that we can substitute the (single) `read YMM1 s41` left in the goal
     by its pLo/pHi/pMid expression. *)
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
   check (fun th -> let c = concl th in
     is_eq c && is_comb (rand c) &&
     (match (rator (rand c)) with
      | Comb(Const("read",_),_) -> true | _ -> false)))) THEN
  (* Unfold the genvar per-step abbreviations created by
     GHASH_ABBREV_STEP_TAC so the residual is purely in the three Karatsuba
     products. *)
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
   check (fun th -> let c = concl th in
     is_eq c && is_var(rand c) &&
     String.length(fst(dest_var(rand c))) > 1 &&
     String.get (fst(dest_var(rand c))) 0 = Char.chr 95))) THEN
  (* The YMM1 hypothesis became available only after the genvar unfold;
     reorient/substitute it into the goal now. *)
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
   check (fun th -> let c = concl th in
     is_eq c && is_comb (rand c) &&
     (match (rator (rand c)) with
      | Comb(Const("read",_),_) -> true | _ -> false)))) THEN
  (* The stepper emitted the Karatsuba middle operand as
     `subword(xor(join(lo,hi), xi), 0, 64)`; normalise to `xor(lo,hi)`. *)
  REWRITE_TAC[MID_SUBWORD_FOLD] THEN
  (* Unfold polyval_dot, Karatsuba-expand the RHS 128 x 128 -> 256 product,
     extract its four 64-bit limbs, then unfold prop3.  After this the goal's
     two sides are both 128-bit expressions in three 64x64 `word_pmul` terms. *)
  REWRITE_TAC[polyval_dot; PMUL_KARATSUBA_FLAT] THEN
  REWRITE_TAC[polyval_reduce_prop3; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  (* Abbreviate the three 64 x 64 products so BITBLAST sees only three
     opaque 128-bit variables rather than rebuilding the whole multiply. *)
  ABBREV_TAC
   `pLo:int128 = word_pmul
      (word_subword (word_reversefields 8 (xi:int128)) (0,64):int64)
      (word_subword (h:int128) (0,64):int64)` THEN
  ABBREV_TAC
   `pHi:int128 = word_pmul
      (word_subword (word_reversefields 8 (xi:int128)) (64,64):int64)
      (word_subword (h:int128) (64,64):int64)` THEN
  ABBREV_TAC
   `pMid:int128 = word_pmul
      (word_xor
        (word_subword (word_reversefields 8 (xi:int128)) (0,64):int64)
        (word_subword (word_reversefields 8 (xi:int128)) (64,64)))
      (word_xor
        (word_subword (h:int128) (0,64):int64)
        (word_subword (h:int128) (64,64)))` THEN
  ASM_REWRITE_TAC[] THEN
  (* Unfold the two `word_pmul _ W` reduction multiplies. *)
  REWRITE_TAC[PMUL_W_64_128; WORD_ZX_ZX_128] THEN
  (* The residual is a 128-bit GF(2) identity in pLo, pHi, pMid.  Split
     into two 64-bit lanes and close each with BITBLAST_TAC; ~8 s total. *)
  GEN_REWRITE_TAC I [WORD_EQ_LANES_128_LOCAL] THEN
  CONJ_TAC THEN BITBLAST_TAC);;
