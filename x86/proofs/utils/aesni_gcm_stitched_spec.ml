(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Recursive closed-form spec for the .Loop6x bulk loop body of the          *)
(* x86 stitched encrypt routine (aesni_gcm_encrypt).  Modelled on            *)
(* arm/proofs/utils/aes_xts_encrypt_spec.ml: the loop-body operation is      *)
(* expressed as a recursive function over the iteration index, so the        *)
(* outer milestone (M8) can simulate the body inline against this spec       *)
(* instead of stitching together a stand-alone body theorem (M7) whose       *)
(* per-iter existentials must be re-bridged by every downstream caller.     *)
(*                                                                           *)
(* This file is a STUB: every spec primitive is a `new_definition` (so the  *)
(* shape is fixed once and only once — see [[new_definition_no_rebind]]),   *)
(* and the three ring-algebra lemmas at the bottom (GHASH_POLYVAL_ACC_6,    *)
(* GHASH_REDUCTION_SPLIT_LEMMA, GHASH_COMBINE_STEP) are stated with           *)
(* CHEAT_TAC bodies.  The stubs let us type-check the spec via               *)
(* `loadt "x86/proofs/utils/aesni_gcm_stitched_spec.ml"` and iterate on the  *)
(* shape (signatures, types, and lemma statements) before any proof work.    *)
(*                                                                           *)
(* Provenance.  See the recursive-spec-pivot memo (2026-05-16) for the       *)
(* design walkthrough.  Spec primitives correspond to the structural pieces *)
(* of the body that must be stable across iterations:                        *)
(*                                                                           *)
(*   1. Counters    : `cb_at`, `inc32` (counter-block recurrence)            *)
(*   2. Plaintext   : `pt_at` (plaintext block at iptr+16j)                  *)
(*   3. Ciphertext  : `ct_at`, `bswap_ct_at` (per-block CT, byte-reversed)   *)
(*   4. GHASH state : `h_power_1..h_power_5`, `karatsuba_batch_6x`,         *)
(*                    `ghash_combine`, `body_ghash_step`, `ghash_at`         *)
(*                                                                           *)
(* The three ring-algebra lemmas are the only substantive new proof          *)
(* obligations that the recursive spec adds to the existing                  *)
(* polyval/Karatsuba infrastructure (everything else is stitching).          *)
(* ========================================================================= *)

needs "x86/proofs/utils/aes_fips197_bridge.ml";;
   (* aes128_cipher (FIPS-197 cipher), needed by the per-lane CT spec       *)
needs "common/polyval_ghash.ml";;
   (* polyval_dot, h_power, ghash_polyval_acc, GHASH_POLYVAL_ACC_2          *)
needs "common/karatsuba_pmul.ml";;
   (* PMUL_KARATSUBA / PMUL_KARATSUBA_FLAT — needed when phase-1+phase-2    *)
   (* split is proved against asm reduction shape                            *)
needs "common/gcm.ml";;
   (* inc32 (counter-block increment, SP 800-38D §6.2)                      *)

(* The x86 stitched-encrypt routine takes plaintext through r14 (or rsi    *)
(* before the body's leaq advance).  We model the input as a `byte list`   *)
(* and convert each 16-byte slice via `bytes_to_int128`.  The arm side has *)
(* a definition of the same name and body in                                *)
(* `arm/proofs/utils/aes_xts_common_spec.ml`; we duplicate it locally       *)
(* rather than promote it to `common/` for now, since the AES-XTS work     *)
(* that introduced it has not migrated to common either.  CANDIDATE for     *)
(* later promotion to `common/words2.ml` once a second consumer lands.      *)
(* Per [[new_definition_no_rebind]] the binding is one-shot — if the arm   *)
(* and x86 utils are ever co-loaded, we must factor before that.            *)

let bytes_to_int128 = define
 `bytes_to_int128 (bs:byte list) : int128 =
    word_join
      (word_join
        (word_join (word_join (EL 15 bs) (EL 14 bs) : int16)
                   (word_join (EL 13 bs) (EL 12 bs) : int16) : int32)
        (word_join (word_join (EL 11 bs) (EL 10 bs) : int16)
                   (word_join (EL 9 bs)  (EL 8 bs)  : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16)
                   (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16)
                   (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

(* ========================================================================= *)
(* 1. Counter-block recurrence.                                              *)
(*                                                                           *)
(* `cb_at icb j` = inc32^j(icb).  The outer milestone passes the             *)
(* prologue-shuffled icb (already inc32'd once for the .Loop6x entry) so     *)
(* `cb_at icb 0 = icb` matches the value xmm10 holds at body entry.          *)
(* ------------------------------------------------------------------------- *)

let cb_at = define
 `cb_at (icb:int128) 0 = icb /\
  cb_at (icb:int128) (SUC j) = inc32 (cb_at icb j)`;;

(* ========================================================================= *)
(* 2. Plaintext block at j-th 16-byte slot of the input list.                *)
(*                                                                           *)
(* `pt_in` is a `byte list`; `pt_at pt_in j` extracts the j-th 16-byte       *)
(* block as an int128, in the byte-order matching the bytes128 memory read  *)
(* the asm uses at iptr+16j.                                                 *)
(* ------------------------------------------------------------------------- *)

let pt_at = new_definition
 `pt_at (pt_in:byte list) (j:num) : int128 =
    bytes_to_int128 (SUB_LIST (16 * j, 16) pt_in)`;;

(* ========================================================================= *)
(* 3. Ciphertext block at j-th 16-byte slot.                                 *)
(*                                                                           *)
(* `ct_at ks icb pt_in j` is the j-th ciphertext block produced by the       *)
(* stitched 6x encrypt.  The asm stores it at optr+16j (post body-end).     *)
(* The body itself stores the BYTE-REVERSED form via the vmovdqu chain;     *)
(* `bswap_ct_at` is the helper for the GHASH-side absorption.                *)
(*                                                                           *)
(* `stitched_6x_ct_block` lives in `aesni_gcm_stitched_6x.ml` (M7's body    *)
(* file), which we will keep loaded but no longer rely on for the loop      *)
(* invariant — we only need its definition.  TODO: factor                   *)
(* `stitched_6x_ct_block` + `aes128_ctr_lane_m7` into                        *)
(* `aes_fips197_bridge.ml` (or here) so this file can be loaded without M7. *)
(* ------------------------------------------------------------------------- *)

let ct_at = new_definition
 `ct_at (ks:int128 list) (icb:int128) (pt_in:byte list) (j:num) : int128 =
    word_xor (pt_at pt_in j)
             (word_reversefields 8
                (aes128_cipher
                   (word_reversefields 8 (cb_at icb j))
                   (MAP (word_reversefields 8) ks)))`;;
   (* This unfolds `stitched_6x_ct_block ks (cb_at icb j) (pt_at pt_in j)` *)
   (* without taking a dep on aesni_gcm_stitched_6x.ml — once that         *)
   (* dependency is reintroduced or factored, switch to the named form.    *)

let bswap_ct_at = new_definition
 `bswap_ct_at (ks:int128 list) (icb:int128) (pt_in:byte list) (j:num)
      : int128 =
    word_bytereverse (ct_at ks icb pt_in j)`;;

(* ========================================================================= *)
(* 4. H powers H^1..H^5.                                                     *)
(*                                                                           *)
(* The 6x body absorbs six byte-reversed CT blocks against H^1..H^6.  To    *)
(* match `polyval_dot`'s "x^{-128} mod Q" semantics we use `h_power` from   *)
(* common/polyval_ghash.ml: `h_power h 0 = h`, `h_power h (SUC n) =          *)
(* polyval_dot (h_power h n) h`.  We expose H^k named constants only for    *)
(* k in 1..5 — H^6 always appears as `polyval_dot (h_power_5 h) h` and     *)
(* there's no need to give it a separate name.                               *)
(* ------------------------------------------------------------------------- *)

let h_power_1 = new_definition
 `h_power_1 (h:int128) : int128 = h`;;

let h_power_2 = new_definition
 `h_power_2 (h:int128) : int128 = polyval_dot h h`;;

let h_power_3 = new_definition
 `h_power_3 (h:int128) : int128 = polyval_dot (h_power_2 h) h`;;

let h_power_4 = new_definition
 `h_power_4 (h:int128) : int128 = polyval_dot (h_power_3 h) h`;;

let h_power_5 = new_definition
 `h_power_5 (h:int128) : int128 = polyval_dot (h_power_4 h) h`;;

(* Bridge to common/polyval_ghash.ml's `h_power`.  Useful when a downstream
   proof has a goal in terms of one form and a hypothesis in the other.    *)

let H_POWER_K_EQ_H_POWER = prove
 (`(!h. h_power_1 h = h_power h 0) /\
   (!h. h_power_2 h = h_power h 1) /\
   (!h. h_power_3 h = h_power h 2) /\
   (!h. h_power_4 h = h_power h 3) /\
   (!h. h_power_5 h = h_power h 4)`,
  REWRITE_TAC[h_power_1; h_power_2; h_power_3; h_power_4; h_power_5;
              h_power;
              ARITH_RULE `4 = SUC 3`; ARITH_RULE `3 = SUC 2`;
              ARITH_RULE `2 = SUC 1`; ARITH_RULE `1 = SUC 0`]);;

(* ========================================================================= *)
(* 5. Karatsuba batch over 6 blocks.                                         *)
(*                                                                           *)
(* `karatsuba_batch_6x H acc b0..b5 : 256 word` is the algebraic operand     *)
(* that the body's six vpclmulqdq quadruples + their XOR chain produce       *)
(* BEFORE the two-phase reduction.  Concretely: the wide sum                *)
(*                                                                           *)
(*    word_pmul (word_xor acc b0) H^6                                       *)
(*  + word_pmul b1 H^5                                                      *)
(*  + ... + word_pmul b5 H^1   (all in 256-bit XOR-arithmetic)              *)
(*                                                                           *)
(* The phase-1 / phase-2 reductions of `polyval_reduce_prop3` then collapse  *)
(* this 256-bit operand to the 128-bit ghash residue.                        *)
(* ------------------------------------------------------------------------- *)

let karatsuba_batch_6x = new_definition
 `karatsuba_batch_6x
      (h:int128)
      (acc:int128)
      (b0:int128) (b1:int128) (b2:int128)
      (b3:int128) (b4:int128) (b5:int128) : 256 word =
    word_xor
      (word_pmul (word_xor acc b0) (polyval_dot (h_power_5 h) h) : 256 word)
     (word_xor
      (word_pmul b1 (h_power_5 h) : 256 word)
     (word_xor
      (word_pmul b2 (h_power_4 h) : 256 word)
     (word_xor
      (word_pmul b3 (h_power_3 h) : 256 word)
     (word_xor
      (word_pmul b4 (h_power_2 h) : 256 word)
      (word_pmul b5 (h_power_1 h) : 256 word)))))`;;

(* ========================================================================= *)
(* 6. ghash_combine: the 4-tuple algebraic invariant.                        *)
(*                                                                           *)
(* `ghash_combine xi4 xi8 sp16` ties the body's three GHASH-state            *)
(* registers (YMM4 / YMM8 / sp+16 spill) back to a single running-ghash      *)
(* value.  At each loop iter the prior-iter carries (xi4, sp16) get folded   *)
(* into the new xi8 by the body's first two vpxors (asm lines 619-620 in    *)
(* aesni_gcm_encrypt.S), so M9's tail sees only `ghash_at` — no             *)
(* existentials.                                                             *)
(*                                                                           *)
(* We defined this BEFORE `body_ghash_step` so the latter can reference it. *)
(* (xi7 — register YMM7 — is also part of the body's ghost state but is    *)
(* algebraically zero at iter boundaries; we keep it in `body_ghash_step`'s *)
(* signature for traceability but it does not appear here.)                  *)
(* ------------------------------------------------------------------------- *)

let ghash_combine = new_definition
 `ghash_combine (xi4:int128) (xi8:int128) (sp16:int128) : int128 =
    word_xor (word_xor xi8 xi4) sp16`;;

(* ========================================================================= *)
(* 7. body_ghash_step: per-iter (xi4_in, xi7_in, xi8_in, sp16_in) ->         *)
(*                              (xi4_out, xi7_out, xi8_out, sp16_out).       *)
(*                                                                           *)
(* The 6x body's reduction pipeline produces three GHASH-state registers     *)
(* (YMM4 / YMM8 / sp+16) at body exit; their XOR (= `ghash_combine`) is the *)
(* updated running ghash.  M9 reads them as a single ghash via the body's   *)
(* first two vpxors at .Ldec_loop6x_done.                                   *)
(*                                                                           *)
(* DESIGN CHOICE.  We canonicalise the 4-tuple at the spec layer: the       *)
(* output puts the entire running ghash in xi8_out and zeros xi4_out /      *)
(* xi7_out / sp16_out.  This is one valid choice (under the                 *)
(* `ghash_combine = running_ghash` invariant any such choice works) and is  *)
(* the simplest.  The asm of course produces a non-zero xi4 / sp16 at       *)
(* body exit; M8's per-iter inductive step bridges the asm's actual         *)
(* (xi4, xi8, sp16) post values to this canonical form by:                  *)
(*   - showing  asm_xi8 XOR asm_xi4 XOR asm_sp16  = polyval_reduce_prop3 W  *)
(*     where W = the karatsuba_batch_6x of the absorbed CT blocks against H *)
(*   - then ghash_combine of (xi4_out, xi8_out, sp16_out) = (0, prop3 W, 0) *)
(*     equals the same prop3 W via WORD_RULE.                               *)
(*                                                                           *)
(* So the spec-layer 4-tuple becomes a single carrier: M9's tail interface  *)
(* sees only `ghash_at h tag0 ks icb pt_in iter_count` and never inspects   *)
(* the per-iter carry layout.  This avoids the EXT-N existential cycle.    *)
(*                                                                           *)
(* xi7 (register YMM7) is part of the body's ghost state but is             *)
(* algebraically zero at iter boundaries; we keep it in the signature for   *)
(* traceability against the asm.                                             *)
(* ------------------------------------------------------------------------- *)

let body_ghash_step = new_definition
 `body_ghash_step
     (h:int128)
     (xi4_in:int128) (xi7_in:int128) (xi8_in:int128) (sp16_in:int128)
     (b0:int128) (b1:int128) (b2:int128)
     (b3:int128) (b4:int128) (b5:int128)
     : int128 # int128 # int128 # int128 =
    let acc_in = ghash_combine xi4_in xi8_in sp16_in in
    let wide = karatsuba_batch_6x h acc_in b0 b1 b2 b3 b4 b5 in
    word 0 : int128,
    word 0 : int128,
    polyval_reduce_prop3 wide,
    word 0 : int128`;;

(* ========================================================================= *)
(* 8. ghash_at: running GHASH after i 6-block batches.                       *)
(*                                                                           *)
(* `ghash_at h tag0 ks icb pt_in i` is the GHASH residue after the loop      *)
(* has absorbed 6*i byte-reversed CT blocks (i.e. blocks 0..6i-1) starting   *)
(* from the prologue tag `tag0`.  Used as both the precondition (i = 0       *)
(* gives tag0) and the postcondition (i = iter_count gives the GHASH the    *)
(* tail expects in YMM8 at .Ldec_loop6x_done).                               *)
(*                                                                           *)
(* The 6-block batched recurrence: each iter absorbs blocks (6i)..(6i+5)     *)
(* via `ghash_polyval_acc h _ [b0;b1;b2;b3;b4;b5]`, which is exactly        *)
(* `polyval_reduce_prop3 (karatsuba_batch_6x h _ b0..b5)` — the equality    *)
(* the GHASH_POLYVAL_ACC_6 lemma below establishes.                          *)
(* ------------------------------------------------------------------------- *)

let ghash_at = define
 `ghash_at (h:int128) (tag0:int128) (ks:int128 list) (icb:int128)
           (pt_in:byte list) 0 = tag0 /\
  ghash_at (h:int128) (tag0:int128) (ks:int128 list) (icb:int128)
           (pt_in:byte list) (SUC i) =
    ghash_polyval_acc h
      (ghash_at h tag0 ks icb pt_in i)
      [bswap_ct_at ks icb pt_in (6 * i);
       bswap_ct_at ks icb pt_in (6 * i + 1);
       bswap_ct_at ks icb pt_in (6 * i + 2);
       bswap_ct_at ks icb pt_in (6 * i + 3);
       bswap_ct_at ks icb pt_in (6 * i + 4);
       bswap_ct_at ks icb pt_in (6 * i + 5)]`;;

(* ========================================================================= *)
(* 9. Ring-algebra lemmas.                                                   *)
(*                                                                           *)
(* Two load-bearing theorems.  Both proved here.                             *)
(*                                                                           *)
(* The recursive-spec design memo (2026-05-16) listed three lemmas, but the *)
(* third (GHASH_REDUCTION_SPLIT_LEMMA) became unnecessary once               *)
(* `body_ghash_step` was canonicalised to put the entire residue in xi8_out *)
(* and zero the other carriers.  M8's per-iter inductive step now bridges   *)
(* the asm's three-register output to the canonical form locally — see      *)
(* the design-choice note above body_ghash_step.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* GHASH_POLYVAL_ACC_6 — specialises the n-block batched Horner theorem      *)
(* `GHASH_POLYVAL_ACC_BATCHED` (common/polyval_ghash.ml) to 6 blocks and    *)
(* matches the wide-XOR sum to our `karatsuba_batch_6x` definition.          *)
(*                                                                           *)
(* The generic theorem gives                                                 *)
(*   ghash_polyval_acc h a (CONS b bs) =                                     *)
(*     prop3 (pmul (a XOR b) H^|bs| XOR ghash_wide h (|bs|-1) bs)            *)
(* — instantiate with `bs = [b1;b2;b3;b4;b5]` and unfold the ghash_wide     *)
(* recursion + h_power_k constants to match karatsuba_batch_6x's shape.      *)
(* ------------------------------------------------------------------------- *)

let GHASH_POLYVAL_ACC_6 = prove
 (`!(h:int128) (acc:int128)
     (b0:int128) (b1:int128) (b2:int128)
     (b3:int128) (b4:int128) (b5:int128).
    ghash_polyval_acc h acc [b0; b1; b2; b3; b4; b5] =
    polyval_reduce_prop3 (karatsuba_batch_6x h acc b0 b1 b2 b3 b4 b5)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
    [`h:int128`; `[b1;b2;b3;b4;b5]:(int128)list`;
     `acc:int128`; `b0:int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; SUC_SUB1;
              ARITH_RULE `4 - 1 = 3`; ARITH_RULE `3 - 1 = 2`;
              ARITH_RULE `2 - 1 = 1`; ARITH_RULE `1 - 1 = 0`;
              SUB_0; WORD_XOR_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[karatsuba_batch_6x;
              h_power_1; h_power_2; h_power_3; h_power_4; h_power_5]);;

(* ------------------------------------------------------------------------- *)
(* GHASH_COMBINE_STEP — the body's per-iter outputs preserve the              *)
(* `ghash_combine = ghash_at` invariant.                                     *)
(*                                                                           *)
(* This is the load-bearing lemma that lets M8's loopinv carry through one   *)
(* iter at a time without inventing a new bridge per iter (the failure       *)
(* mode of the 5-cycle EXT-N enrichment chain).                             *)
(*                                                                           *)
(* Proof: unfold body_ghash_step's 4-tuple (xi8_out = prop3 wide, others     *)
(* zero), unfold ghash_combine + ghash_at(SUC i), substitute the hypothesis *)
(* `ghash_combine xi4_in xi8_in sp16_in = ghash_at i` into the LHS's        *)
(* karatsuba_batch_6x acc parameter, and close via GHASH_POLYVAL_ACC_6      *)
(* + the WORD_RULE identity                                                  *)
(*    word_xor (word_xor x (word 0)) (word 0) = x.                           *)
(* ------------------------------------------------------------------------- *)

let GHASH_COMBINE_STEP = prove
 (`!(h:int128) (tag0:int128) (ks:int128 list) (icb:int128)
     (pt_in:byte list) (i:num)
     (xi4_in:int128) (xi7_in:int128) (xi8_in:int128) (sp16_in:int128).
    ghash_combine xi4_in xi8_in sp16_in = ghash_at h tag0 ks icb pt_in i
    ==> (let (xi4_out,xi7_out,xi8_out,sp16_out) =
              body_ghash_step h xi4_in xi7_in xi8_in sp16_in
                (bswap_ct_at ks icb pt_in (6 * i))
                (bswap_ct_at ks icb pt_in (6 * i + 1))
                (bswap_ct_at ks icb pt_in (6 * i + 2))
                (bswap_ct_at ks icb pt_in (6 * i + 3))
                (bswap_ct_at ks icb pt_in (6 * i + 4))
                (bswap_ct_at ks icb pt_in (6 * i + 5)) in
         ghash_combine xi4_out xi8_out sp16_out =
         ghash_at h tag0 ks icb pt_in (SUC i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_combine; body_ghash_step; LET_DEF; LET_END_DEF;
              ghash_at] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_6;
              WORD_RULE
                `word_xor (word_xor x (word 0:int128)) (word 0) = x`]);;

(* ========================================================================= *)
(* 10. Consumer-facing helpers.                                              *)
(*                                                                           *)
(* These don't add any new content; they package common unfoldings that      *)
(* downstream M8/M9 proofs would otherwise reprove inline.                   *)
(* ========================================================================= *)

(* Closed-form components of `body_ghash_step`'s 4-tuple output: xi4 / xi7 / *)
(* sp16 are zero, xi8 is the reduced Karatsuba batch.  Used by M8 to extract *)
(* individual components without let-binding gymnastics.                     *)

let BODY_GHASH_STEP_COMPONENTS = prove
 (`!(h:int128)
     (xi4:int128) (xi7:int128) (xi8:int128) (sp16:int128)
     (b0:int128) (b1:int128) (b2:int128)
     (b3:int128) (b4:int128) (b5:int128).
    let (xi4_out,xi7_out,xi8_out,sp16_out) =
        body_ghash_step h xi4 xi7 xi8 sp16 b0 b1 b2 b3 b4 b5 in
    xi4_out = word 0 /\
    xi7_out = word 0 /\
    sp16_out = word 0 /\
    xi8_out =
      polyval_reduce_prop3
        (karatsuba_batch_6x h (ghash_combine xi4 xi8 sp16)
                              b0 b1 b2 b3 b4 b5)`,
  REWRITE_TAC[body_ghash_step; LET_DEF; LET_END_DEF]);;

(* Concrete unfolding of `ghash_at` at i = 1 — the first 6-block batch       *)
(* absorbs blocks 0..5 starting from the prologue tag tag0.  Useful at the   *)
(* base case of M8's induction (iter_count >= 1 minimum).                    *)

let GHASH_AT_1 = prove
 (`!(h:int128) (tag0:int128) (ks:int128 list) (icb:int128)
     (pt_in:byte list).
    ghash_at h tag0 ks icb pt_in 1 =
    ghash_polyval_acc h tag0
      [bswap_ct_at ks icb pt_in 0; bswap_ct_at ks icb pt_in 1;
       bswap_ct_at ks icb pt_in 2; bswap_ct_at ks icb pt_in 3;
       bswap_ct_at ks icb pt_in 4; bswap_ct_at ks icb pt_in 5]`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ghash_at; MULT_CLAUSES; ADD_CLAUSES]);;
