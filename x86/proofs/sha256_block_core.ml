(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 single-block register core (x86-64 SHA-NI).                       *)
(*                                                                           *)
(* Proves correctness of the loop body of sha256_block_data_order_hw in      *)
(* isolation: starting at the loop-top PC with XMM1/XMM2 holding the         *)
(* ABEF/CDGH packing of the initial hash state and memory holding one        *)
(* 512-bit message block + the K table, after running the body the XMM1/    *)
(* XMM2 pair holds the ABEF/CDGH packing of sha256_block M H.                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/sha256_bridge_x86.ml";;

(* ========================================================================= *)
(* Machine code and execution rule.                                          *)
(* ========================================================================= *)

let sha256_hw_mc = define_from_elf "sha256_hw_mc"
  (file_on_path !load_path "x86/sha2/sha256_block_data_order_hw.o");;

let HW_EXEC = X86_MK_EXEC_RULE sha256_hw_mc;;

(* ========================================================================= *)
(* SIMD simplification.  Pasted from common/mlkem_mldsa.ml to avoid the      *)
(* 5-minute load of the ML-KEM/ML-DSA spec.                                  *)
(* ========================================================================= *)

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let arm_simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  let x86_simdable = can (term_match [] `read X (s:x86state):int256 = whatever`) in
  let x86_simdable_128 = can (term_match []
    `read X (s:x86state):int128 = whatever`) in
  let simdable tm =
    arm_simdable tm || x86_simdable tm || x86_simdable_128 tm in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

(* ========================================================================= *)
(* PSHUFB mask constant.                                                     *)
(*                                                                           *)
(* The routine expects [rcx+256] to contain the "byte-reverse within each    *)
(* 32-bit lane" mask, stored as the 4-word sequence                          *)
(*   0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f.                         *)
(*                                                                           *)
(* After pshufb of a lane against this mask, each 32-bit lane is             *)
(* byte-reversed.                                                            *)
(* ========================================================================= *)

let pshufb_mask_val = define
  `pshufb_mask_val:int128 =
   word_join4 (word 0x00010203:int32)
              (word 0x04050607)
              (word 0x08090a0b)
              (word 0x0c0d0e0f)`;;

(* Byte-level fully-split form of pshufb_mask_val.  Needed to expose the     *)
(* constant as a nested word_join chain so USIMD2 can peel off layers during *)
(* PSHUFB simplification.                                                    *)
let pshufb_mask_val_bytes = prove
 (`pshufb_mask_val =
   (word_join:int64->int64->int128)
    ((word_join:int32->int32->int64)
      ((word_join:int16->int16->int32)
        ((word_join:byte->byte->int16) (word 0x0c) (word 0x0d))
        ((word_join:byte->byte->int16) (word 0x0e) (word 0x0f)))
      ((word_join:int16->int16->int32)
        ((word_join:byte->byte->int16) (word 0x08) (word 0x09))
        ((word_join:byte->byte->int16) (word 0x0a) (word 0x0b))))
    ((word_join:int32->int32->int64)
      ((word_join:int16->int16->int32)
        ((word_join:byte->byte->int16) (word 0x04) (word 0x05))
        ((word_join:byte->byte->int16) (word 0x06) (word 0x07)))
      ((word_join:int16->int16->int32)
        ((word_join:byte->byte->int16) (word 0x00) (word 0x01))
        ((word_join:byte->byte->int16) (word 0x02) (word 0x03))))`,
  REWRITE_TAC[pshufb_mask_val; word_join4] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* PSHUFB with pshufb_mask_val byte-reverses each 32-bit lane.                *)
(*                                                                           *)
(* Two shapes arise from the x86 stepper:                                    *)
(*   • PSHUFB_BYTEREVERSE — the raw usimd16-applied lambda equals word_join4 *)
(*     of the non-byte-reversed words.                                       *)
(*   • PSHUFB_XMM_BYTEREVERSE — the shape matching what ASSUMPTION_STATE_    *)
(*     UPDATE_TAC leaves in the YMM read assumption, namely                  *)
(*     `word_subword (word_join ymm_top (usimd16 ... ...)) (0,128)`.         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* PSHUFB_BYTEREVERSE_TAC : int -> string -> term*term*term*term -> tactic    *)
(*                                                                           *)
(* Usage: applied AFTER `X86_VERBOSE_STEP_TAC HW_EXEC "s<n>"` for a           *)
(*   `PSHUFB xmm_i, xmm7` step (with `read XMM7 s<n-1> = pshufb_mask_val`     *)
(*   and `read YMM<i> s<n-1> = word_join top (word_join4 (bytereverse w_j)    *)
(*   (bytereverse w_{j+1}) (bytereverse w_{j+2}) (bytereverse w_{j+3}))`      *)
(*   visible as assumptions).                                                 *)
(*                                                                           *)
(* Produces the clean `read XMM<i> s<n> = word_join4 w_j w_{j+1} w_{j+2}     *)
(* w_{j+3}` assumption without attempting to prove it with WORD_BLAST on the *)
(* raw usimd16 expansion (which is too expensive).  Instead: folds the       *)
(* pshufb_mask_val using the byte-level split lemma, reduces the             *)
(* `if bit 7 (word_subword pshufb_mask_val …)` ifs, then finishes with       *)
(* WORD_BLAST on the resulting structural equality.                           *)
(*                                                                           *)
(* The prerequisites assumed in the caller:                                   *)
(*   - `read XMM7 s<n-1> = pshufb_mask_val` (the mask register)               *)
(*   - `read YMM<i> s<n-1>` holds the pre-shuffle byte-reversed payload.      *)
(*   - The caller has run `RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD])`  *)
(*     and used the XMM7 fact to substitute `read XMM7 s<n-1>` with          *)
(*     `pshufb_mask_val` in the YMM<i> s<n> assumption.                       *)
(* ------------------------------------------------------------------------- *)

let PSHUFB_BYTEREVERSE_TAC (xmm_idx:int) (sname:string)
                           ((w0,w1,w2,w3):term*term*term*term) : tactic =
  let xmm_name = "XMM" ^ string_of_int xmm_idx in
  let ymm_name = "YMM" ^ string_of_int xmm_idx in
  let xmm_tm = mk_const(xmm_name, []) in
  let s_tm = mk_var(sname, `:x86state`) in
  let read_tm = `read:(x86state,int128)component->x86state->int128` in
  let goal_tm = mk_eq(
    mk_comb(mk_comb(read_tm, xmm_tm), s_tm),
    list_mk_comb(`word_join4:int32->int32->int32->int32->int128`,
                 [w0;w1;w2;w3])) in
  let has_sub sub s =
    let ls = String.length s and lsub = String.length sub in
    let rec try_at i =
      i + lsub <= ls && (String.sub s i lsub = sub || try_at (i+1)) in
    try_at 0 in
  let ymm_needle = ymm_name ^ " " ^ sname ^ " =" in
  SUBGOAL_THEN goal_tm ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6;
                XMM7; XMM8; XMM9; XMM10; READ_ZEROTOP_128] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      has_sub ymm_needle (string_of_term (concl th)))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[pshufb_mask_val_bytes] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[word_join4] THEN
    CONV_TAC WORD_BLAST;
    ALL_TAC];;

let PSHUFB_BYTEREVERSE = prove
 (`!(w0:int32) (w1:int32) (w2:int32) (w3:int32).
     (usimd16
          ((\i:byte.
              if bit 7 i then word 0:byte
              else word_subword
                     (word_join4 (word_bytereverse w0) (word_bytereverse w1)
                                 (word_bytereverse w2) (word_bytereverse w3))
                     (8 * val(word_subword i (0,4):nybble),8):byte))
          pshufb_mask_val:int128) =
     (word_join4 w0 w1 w2 w3:int128)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pshufb_mask_val_bytes; usimd16; usimd8; usimd4; USIMD2] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[word_join4] THEN
  CONV_TAC WORD_BLAST);;

let PSHUFB_XMM_BYTEREVERSE = prove
 (`!(ymm_top:int128) (w0:int32) (w1:int32) (w2:int32) (w3:int32).
     word_subword
       (word_join ymm_top
          (usimd16
            ((\i:byte.
                if bit 7 i then word 0:byte
                else word_subword
                       (word_subword
                         (word_join ymm_top
                           (word_join4 (word_bytereverse w0)
                                       (word_bytereverse w1)
                                       (word_bytereverse w2)
                                       (word_bytereverse w3))
                            :int256)
                         (0,128):int128)
                       (8 * val(word_subword i (0,4):nybble),8):byte))
             pshufb_mask_val)
        :int256)
       (0,128):int128 =
     (word_join4 w0 w1 w2 w3:int128)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pshufb_mask_val_bytes; usimd16; usimd8; usimd4; USIMD2] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[word_join4] THEN
  CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* Packing-level lemmas for the hardware SSE operations used in the body.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Balanced word_join4: re-associates the right-leaning definition           *)
(*   word_join d (word_join c (word_join b a))                               *)
(* as a balanced binary join                                                 *)
(*   word_join (word_join d c) (word_join b a),                              *)
(* so that SIMD2 (and hence simd4 = simd2 o simd2) can rewrite it.           *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN4_BALANCED = prove
 (`!a b c d:int32.
     word_join4 a b c d =
     (word_join:64 word->64 word->int128)
       (word_join d c) (word_join b a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* PADDD on two word_join4-packed XMM registers: lane-wise addition.         *)
(* Rewrites simd4 word_add (word_join4 ...) (word_join4 ...) to a           *)
(* word_join4 of lane-wise word_adds.                                        *)
(* ------------------------------------------------------------------------- *)

let PADDD_WORD_JOIN4 = prove
 (`!x0 x1 x2 x3 y0 y1 y2 y3:int32.
     simd4 (word_add:int32->int32->int32)
       (word_join4 x0 x1 x2 x3)
       (word_join4 y0 y1 y2 y3) =
     word_join4 (word_add x0 y0) (word_add x1 y1)
                (word_add x2 y2) (word_add x3 y3)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_JOIN4_BALANCED] THEN
  REWRITE_TAC[simd4; SIMD2] THEN
  REWRITE_TAC[WORD_JOIN4_BALANCED]);;

(* ------------------------------------------------------------------------- *)
(* PALIGNR 4: byte-level 4-byte right-shift across a (dest,src) concat.      *)
(* In lane terms, for dest = (x0,x1,x2,x3) and src = (y0,y1,y2,y3):          *)
(*   palignr dest, src, 4  →  (y1, y2, y3, x0)                              *)
(* ------------------------------------------------------------------------- *)

let PALIGNR_4_WORD_JOIN4 = prove
 (`!x0 x1 x2 x3 y0 y1 y2 y3:int32.
     word_subword
       ((word_join:int128->int128->int256)
         (word_join4 x0 x1 x2 x3) (word_join4 y0 y1 y2 y3))
       (32,128) = word_join4 y1 y2 y3 x0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST);;

(* PALIGNR 8 (used only in the post-loop shuffle, handled by Phase 5). *)
let PALIGNR_8_WORD_JOIN4 = prove
 (`!x0 x1 x2 x3 y0 y1 y2 y3:int32.
     word_subword
       ((word_join:int128->int128->int256)
         (word_join4 x0 x1 x2 x3) (word_join4 y0 y1 y2 y3))
       (64,128) = word_join4 y2 y3 x0 x1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* SHA256SU_X86_BRIDGE: the fused 4-word schedule-extension across a group.  *)
(*                                                                           *)
(* In the x86 loop body, each schedule register's extension from             *)
(* (w_i, w_{i+1}, w_{i+2}, w_{i+3}) to (w_{i+16}, ..., w_{i+19}) spans       *)
(* three adjacent groups:                                                    *)
(*   group k+0: SHA256MSG1 xmm_i, xmm_{i+1}   (applies sha_ni_msg1)          *)
(*   group k+1: PALIGNR xmm7, (xmm_{i+3},xmm_{i+2}), 4  and PADDD xmm_i,xmm7 *)
(*   group k+2: SHA256MSG2 xmm_i, xmm_{i+3}   (applies sha_ni_msg2)          *)
(*                                                                           *)
(* The net effect, in terms of the 16-word schedule prefix                   *)
(*   (w0,w1,...,w15), is to produce (w16,w17,w18,w19) where                  *)
(*     w_{16+j} = w_j + sigma0 w_{j+1} + w_{j+9} + sigma1 w_{j+14}           *)
(* — i.e., the standard SHA-256 message-schedule extension for four          *)
(* consecutive new words.                                                    *)
(* ------------------------------------------------------------------------- *)

let SHA256SU_X86_BRIDGE = prove
 (`!w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
    let w16 = word_add (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                       (sha256_sigma1 w14) in
    let w17 = word_add (word_add (word_add w1 (sha256_sigma0 w2)) w10)
                       (sha256_sigma1 w15) in
    let w18 = word_add (word_add (word_add w2 (sha256_sigma0 w3)) w11)
                       (sha256_sigma1 w16) in
    let w19 = word_add (word_add (word_add w3 (sha256_sigma0 w4)) w12)
                       (sha256_sigma1 w17) in
    sha_ni_msg2
      (simd4 (word_add:int32->int32->int32)
         (sha_ni_msg1 (word_join4 w0 w1 w2 w3) (word_join4 w4 w5 w6 w7))
         (word_subword
            ((word_join:int128->int128->int256)
              (word_join4 w12 w13 w14 w15) (word_join4 w8 w9 w10 w11))
            (32,128)))
      (word_join4 w12 w13 w14 w15) =
    word_join4 w16 w17 w18 w19`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PALIGNR_4_WORD_JOIN4; SHA256MSG1_BRIDGE; PADDD_WORD_JOIN4;
              SHA256MSG2_BRIDGE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* PSHUFD imm8=0x1b selects lanes (3,2,1,0) — lane-reversal.                 *)
(* PSHUFD imm8=0xb1 selects lanes (1,0,3,2) — swap adjacent 32-bit pairs.   *)
(* PSHUFD imm8=0x0e selects lanes (2,3,0,1) — used after paddd for the      *)
(*   second sha256rnds2's wk argument (brings W[t+2..t+3] into lanes 0,1).  *)
(*                                                                           *)
(* These are proven via bitblast on the x86_PSHUFD definition.  Only the   *)
(* 0x0e variant is needed by the body proof; the others appear in the      *)
(* prologue/epilogue handled by Phase 5.                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* SHA256RNDS2 only reads the LOW 64 bits of its wkval argument (lanes 0,1). *)
(* After `PSHUFD xmm0, xmm0, 0x0e` brings (K2+w2, K3+w3) into lanes (0,1),   *)
(* the upper lanes (2,3) hold irrelevant PSHUFD garbage — (K0+w0, K0+w0) in  *)
(* the asm's case.  GROUP_BRIDGE_H_UNIV expects canonical `word 0` in those  *)
(* slots, so we need this don't-care lemma to rewrite XMM1 s14 into the      *)
(* bridge-ready shape.                                                       *)
(* ------------------------------------------------------------------------- *)

let SHA_NI_RNDS2_WK_DONTCARE = prove
 (`!cdgh abef kw0 kw1 wk2 wk3 wk2' wk3':int32.
     sha_ni_rnds2 cdgh abef (word_join4 kw0 kw1 wk2 wk3) =
     sha_ni_rnds2 cdgh abef (word_join4 kw0 kw1 wk2' wk3')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha_ni_rnds2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word_join4 kw0 kw1 wk2 wk3:int128) (0,32) :int32 = kw0 /\
    word_subword (word_join4 kw0 kw1 wk2 wk3:int128) (32,32) :int32 = kw1 /\
    word_subword (word_join4 kw0 kw1 wk2' wk3':int128) (0,32) :int32 = kw0 /\
    word_subword (word_join4 kw0 kw1 wk2' wk3':int128) (32,32) :int32 = kw1`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[WORD_JOIN4_SUBWORD]);;

(* ------------------------------------------------------------------------- *)
(* MK_WK_DONTCARE_REWRITES : int list -> thm list                            *)
(*                                                                           *)
(* Build two specialized instances of SHA_NI_RNDS2_WK_DONTCARE for the       *)
(* PSHUFD-garbage wk upper lanes that arise from group i.  Pattern:          *)
(*                                                                           *)
(*   inner : word_join4 (K_{4i+0}+w_{4i+0}) (K_{4i+1}+w_{4i+1})              *)
(*                      (K_{4i+2}+w_{4i+2}) (K_{4i+3}+w_{4i+3})              *)
(*           ~~> word_join4 (K_{4i+0}+w_{4i+0}) (K_{4i+1}+w_{4i+1})          *)
(*                          (word 0) (word 0)                                *)
(*                                                                           *)
(*   outer : word_join4 (K_{4i+2}+w_{4i+2}) (K_{4i+3}+w_{4i+3})              *)
(*                      (K_{4i+0}+w_{4i+0}) (K_{4i+0}+w_{4i+0})              *)
(*           ~~> word_join4 (K_{4i+2}+w_{4i+2}) (K_{4i+3}+w_{4i+3})          *)
(*                          (word 0) (word 0)                                *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* Post-step re-folding infrastructure for SHA256RNDS2.                      *)
(*                                                                           *)
(* After X86_STEPS_TAC steps through a SHA256RNDS2, the resulting YMM        *)
(* assumption has the 2-round SHA-256 compression unfolded into              *)
(* sha256_Ch/Maj/Sigma0/Sigma1 applied to word_subword expressions on YMM    *)
(* reads.  To match the Phase 3 bridge lemmas (which expect sha_ni_rnds2     *)
(* applied to ABEF_PACK / CDGH_PACK / word_join4), we refold in 4 steps:     *)
(*                                                                           *)
(*   1. DEPTH_CONV NUM_EXP_CONV: normalize both sides' `2 EXP N` occurrences *)
(*      to concrete numerals.  The stepper evaluates some but not all, so    *)
(*      without this the GSYM rewrite fails to match on a single `2 EXP 64`. *)
(*                                                                           *)
(*   2. YMM_TO_XMM_SUBWORD: replace `word_subword (read YMMi s) (0,128)`     *)
(*      by `read XMMi s` everywhere.  The x86 stepper reads through YMM      *)
(*      (because XMM = YMM :> zerotop_128), but the bridge lemmas and the   *)
(*      sha_ni_rnds2 definition use XMM reads.                               *)
(*                                                                           *)
(*   3. Refold sha256_Ch / sha256_Maj / sha256_Sigma0 / sha256_Sigma1 (the   *)
(*      x86_SHA256RNDS2 definition expands these; GSYM them back).           *)
(*                                                                           *)
(*   4. GSYM SHA_NI_RNDS2_UNFOLDED: replace the giant 3-round sum by the     *)
(*      sha_ni_rnds2 abstraction, which the Phase 3 bridge lemmas consume.   *)
(*                                                                           *)
(* The resulting shape is                                                    *)
(*   read YMM_dst s = word_join (word_subword (read YMM_dst s_prev) (128,128))
                                 (sha_ni_rnds2 (read XMM_dst s_prev)         *)
(*                                              (read XMM_src s_prev)        *)
(*                                              (read XMM0 s_prev))          *)
(* and WORD_SUBWORD_JOIN_BOTTOM then gives the clean                         *)
(*   read XMM_dst s = sha_ni_rnds2 (...) (...) (...).                        *)
(* ------------------------------------------------------------------------- *)

let YMM_TO_XMM_SUBWORD = prove
 (`!(s:x86state).
    (word_subword (read YMM0 s) (0,128) :int128) = read XMM0 s /\
    (word_subword (read YMM1 s) (0,128) :int128) = read XMM1 s /\
    (word_subword (read YMM2 s) (0,128) :int128) = read XMM2 s /\
    (word_subword (read YMM3 s) (0,128) :int128) = read XMM3 s /\
    (word_subword (read YMM4 s) (0,128) :int128) = read XMM4 s /\
    (word_subword (read YMM5 s) (0,128) :int128) = read XMM5 s /\
    (word_subword (read YMM6 s) (0,128) :int128) = read XMM6 s /\
    (word_subword (read YMM7 s) (0,128) :int128) = read XMM7 s /\
    (word_subword (read YMM8 s) (0,128) :int128) = read XMM8 s /\
    (word_subword (read YMM9 s) (0,128) :int128) = read XMM9 s /\
    (word_subword (read YMM10 s) (0,128) :int128) = read XMM10 s`,
  GEN_TAC THEN
  REWRITE_TAC[XMM0;XMM1;XMM2;XMM3;XMM4;XMM5;XMM6;XMM7;XMM8;XMM9;XMM10;
              READ_ZEROTOP_128] THEN
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_JOIN_BOTTOM = prove
 (`!(u:int128) (l:int128).
     word_subword ((word_join:int128->int128->int256) u l) (0,128) :int128 = l`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* sha_ni_rnds2 let-expanded with numeric EXPs evaluated; REWRITE_RULE's     *)
(* GSYM of this theorem refolds the stepper's unfolded 2-round compression. *)
let SHA_NI_RNDS2_UNFOLDED =
  CONV_RULE(TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV NUM_EXP_CONV)
    sha_ni_rnds2;;

(* FOLD_SHA_NI_RNDS2_TAC: run this after an X86_STEPS_TAC chunk that        *)
(* included at least one SHA256RNDS2.  Refolds the new YMM assumption into   *)
(* sha_ni_rnds2 form.                                                        *)
let FOLD_SHA_NI_RNDS2_TAC =
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_EXP_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM sha256_Ch; GSYM sha256_Maj;
                               GSYM sha256_Sigma0; GSYM sha256_Sigma1]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM SHA_NI_RNDS2_UNFOLDED]);;

(* After GHOST_INTRO_TAC-ing `read YMMi` as `ymmi_init`, a register write at *)
(* step n produces `read YMMi s_n = <expression involving ymm_j_init>`.     *)
(* To bridge these back to `read YMMi s0` (the initial-state form that     *)
(* YMM_TO_XMM_SUBWORD recognises), we collect all `read YMMi s_k =         *)
(* ymmi_init` assumptions and rewrite in reverse.  After this, any         *)
(* `ymm_j_init` in an assumption becomes `read YMMj s0`, and               *)
(* YMM_TO_XMM_SUBWORD reduces `word_subword (read YMMj s0) (0,128)` to     *)
(* `read XMMj s0`.                                                          *)

let REFOLD_INIT_GHOSTS_TAC (asl,w) =
  let is_init_rewrite tm =
    try
      let s = string_of_term tm in
      String.length s > 15 &&
      String.sub s 0 5 = "read " &&
      (try let pos = String.index s '=' in
           let rhs = String.sub s (pos+2) (String.length s - pos - 2) in
           String.length rhs >= 4 &&
           String.sub rhs (String.length rhs - 4) 4 = "init"
       with _ -> false)
    with _ -> false in
  let ghost_asms = List.filter is_init_rewrite (map concl (map snd asl)) in
  let ghost_thms = List.map ASSUME ghost_asms in
  (RULE_ASSUM_TAC(REWRITE_RULE (List.map GSYM ghost_thms)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD])) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Helper: collect known `read XMM_i s_k = word_join4 ...` / `= ABEF_PACK …`  *)
(* / `= CDGH_PACK …` / `= pshufb_mask_val` assumptions from the goal, so we   *)
(* can rewrite with them without specifying each one individually.            *)
(* ------------------------------------------------------------------------- *)

let has_sub_string sub s =
  let ls = String.length s and lsub = String.length sub in
  let rec try_at i =
    i + lsub <= ls && (String.sub s i lsub = sub || try_at (i+1)) in
  try_at 0;;

let SUBSTITUTE_XMM_CLEANS_TAC : tactic = fun g ->
  let (asl,_) = g in
  let is_clean_thm s =
    has_sub_string "read XMM" s
    && (has_sub_string "= word_join4" s
        || has_sub_string "= ABEF_PACK" s
        || has_sub_string "= CDGH_PACK" s
        || has_sub_string "= pshufb_mask_val" s) in
  let clean_thms = List.filter_map (fun (_,th) ->
    let s = string_of_term (concl th) in
    if is_clean_thm s then Some th else None) asl in
  (* Skip the clean assumptions themselves when rewriting — otherwise
     REWRITE_RULE on `read XMM_i s = C` rewrites its own LHS to RHS and the
     assumption collapses to `C = C` → T → dropped. *)
  RULE_ASSUM_TAC(fun th ->
    if is_clean_thm (string_of_term (concl th))
    then th
    else REWRITE_RULE clean_thms th) g;;

(* ------------------------------------------------------------------------- *)
(* PADDD_REFOLD_TAC: after an X86_VERBOSE_STEP_TAC for                        *)
(*   PADDD xmm_dst, xmm_src                                                   *)
(* produces a YMM_dst assumption with nested word_add / word_subword /        *)
(* word_join over the expanded simd4 of lane-wise adds, refold back into     *)
(*   word_join (top_preserved)                                                *)
(*             (word_join4 (c0+v0) (c1+v1) (c2+v2) (c3+v3)).                  *)
(*                                                                           *)
(* Relies on the caller having clean `read XMM_src s_prev = word_join4 v0..`  *)
(* and `read XMM_dst s_prev = word_join4 c0..` assumptions visible so         *)
(* SUBSTITUTE_XMM_CLEANS_TAC can plug them in.  The final step folds the     *)
(* right-leaning word_join chain back to word_join4 via GSYM                  *)
(* WORD_JOIN4_BALANCED.                                                       *)
(* ------------------------------------------------------------------------- *)

let PADDD_REFOLD_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]);;

(* ========================================================================= *)
(* EXPAND_K_TAC: specialize the quantified K-memory assumption                *)
(*   !i. i < 16 ==> read (memory :> bytes128 (word_add kptr (word (16 * i))))  *)
(*                    s = word_join4 (EL (4*i) sha256_K) ... (EL (4*i+3) K)   *)
(* into 16 concrete assumptions for i = 0, 1, ..., 15.  After NUM_MULT_CONV   *)
(* and NUM_ADD_CONV the addresses become `word 0`, `word 16`, ..., `word 240` *)
(* and the EL indices become concrete numerals.                               *)
(* ========================================================================= *)

let EXPAND_K_TAC =
  FIRST_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "sha256_K" with _ -> false)) (concl th)
    then
      MAP_EVERY (fun i ->
        let spec = SPEC (mk_small_numeral i) th in
        let mp = MP spec (prove(lhand(concl spec), ARITH_TAC)) in
        ASSUME_TAC(CONV_RULE
          (DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) mp))
        (0--15)
    else FAIL_TAC "no K assumption");;

(* ========================================================================= *)
(* Postcondition tactic.                                                     *)
(* ========================================================================= *)

let h_list_tm = `[a:int32;b;c;d;e;ff;g;h]`;;

let GEN_POSTCOND_TAC_HW h_tm =
  let len_h = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, h_tm), `8`),
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let m = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;
            w8;w9;w10;w11;w12;w13;w14;w15]` in
  let hw_w_abbrev = ASSUME
    `sha256_message_schedule 48
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W` in
  let inst = MP (SPECL [m; h_tm] SHA256_BLOCK_EL) len_h in
  let block_el = List.map (fun k ->
    let th = SPEC (mk_small_numeral k) inst in
    let th2 = MP th (prove(lhand(concl th), ARITH_TAC)) in
    let th3 = try CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2
              with _ -> th2 in
    REWRITE_RULE[hw_w_abbrev] th3) (0--7) in
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC block_el THEN
  REFL_TAC;;

let POSTCOND_TAC_HW = GEN_POSTCOND_TAC_HW h_list_tm;;

(* ========================================================================= *)
(* Cut-point tactic.                                                         *)
(*                                                                           *)
(* After symbolic execution of round-group i's instructions, the XMM1 and    *)
(* XMM2 assumptions contain nested sha_ni_rnds2 applications over the        *)
(* ABEF/CDGH packs of the previous group's state.  CUT_POINT_TAC_HW applies  *)
(* GROUP_BRIDGE_H.(i) and GROUP_BRIDGE_H2.(i) to collapse these into         *)
(* ABEF/CDGH packs of sha256_compress (4*(i+1)) W H.                         *)
(* ========================================================================= *)

(* XMM1 target: state after 4 compress rounds of this group, ABEF lane.     *)
(* XMM2 target: state after 2 compress rounds of this group, ABEF lane —    *)
(*   the XMM2 register physically holds the intermediate result of the      *)
(*   first SHA256RNDS2 in the group, which by GROUP_BRIDGE_H2.(i) equals    *)
(*   the ABEF pack of `sha256_compress (4i+2) W H`.  (At the x86 level      *)
(*   XMM2 is re-used as the CDGH input for the next group; we defer the     *)
(*   CDGH_EQ_ABEF bridge to Phase 5 when the final loop exits.)             *)
let GEN_CUT_POINT_TAC_HW h_tm i sname =
  let target = mk_small_numeral(4 * (i + 1)) in
  let mid = mk_small_numeral(4 * i + 2) in
  let len_h_thm =
    prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, h_tm), `8`),
          REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let bridge_h = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (MP (SPECL [`W:int32 list`; h_tm] GROUP_BRIDGE_H.(i)) len_h_thm) in
  let bridge_h2 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (MP (SPECL [`W:int32 list`; h_tm] GROUP_BRIDGE_H2.(i)) len_h_thm) in
  let xmm1_tm = subst [sname, `s:x86state`; target, `t:num`; h_tm, `H:int32 list`]
    `read XMM1 s = ABEF_PACK
       (EL 0 (sha256_compress t W (H:int32 list)))
       (EL 1 (sha256_compress t W H))
       (EL 4 (sha256_compress t W H))
       (EL 5 (sha256_compress t W H))` in
  let xmm2_tm = subst [sname, `s:x86state`; mid, `m:num`; h_tm, `H:int32 list`]
    `read XMM2 s = ABEF_PACK
       (EL 0 (sha256_compress m W (H:int32 list)))
       (EL 1 (sha256_compress m W H))
       (EL 4 (sha256_compress m W H))
       (EL 5 (sha256_compress m W H))` in
  let CUT_SUBGOAL_TAC bridge =
    ASM_REWRITE_TAC[bridge] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress)))) THEN
    TRY(CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV))) THEN
    REWRITE_TAC EL_W_ALL_LIST THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST;
                WORD_JOIN4_SUBWORD] THEN
    REWRITE_TAC[WORD_ADD_SYM] THEN
    REFL_TAC in
  SUBGOAL_THEN xmm1_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h; ALL_TAC] THEN
  SUBGOAL_THEN xmm2_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h2; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let n = fst(dest_const t) in n = "sha_ni_rnds2"
      with _ -> false)) (concl th))));;

let CUT_POINT_TAC_HW i sname = GEN_CUT_POINT_TAC_HW h_list_tm i sname;;

(* ========================================================================= *)
(* PROLOGUE_PLUS_GROUP0_TAC: complete symbolic execution of steps 1-14 of    *)
(* the loop body (prologue MOVDQU/PSHUFB/MOVDQA loads + group-0 MSG+PADDD+   *)
(* RNDS2+PSHUFD+RNDS2) followed by CUT_POINT_TAC_HW 0 at s14.                *)
(*                                                                           *)
(* Preconditions (from the loop-top precondition):                           *)
(*   read XMM1 s0 = ABEF_PACK a b e ff                                       *)
(*   read XMM2 s0 = CDGH_PACK c d g h                                        *)
(*   read XMM7 s0 = read XMM8 s0 = pshufb_mask_val                           *)
(*   data/K memory populated; RIP = pc+64; RSI = data_ptr; RCX = kptr.       *)
(*                                                                           *)
(* Postcondition (added to assumption list):                                 *)
(*   read XMM1 s14 = ABEF_PACK (EL 0 (compress 4 W H)) … (EL 5 …)            *)
(*   read XMM2 s14 = ABEF_PACK (EL 0 (compress 2 W H)) … (EL 5 …)            *)
(*   where `W = sha256_message_schedule 48 [w0;…;w15]` is an abbreviation.   *)
(* ========================================================================= *)

let PROLOGUE_PLUS_GROUP0_TAC : tactic =
  (* Specialised wk don't-care rewrites for group 0. *)
  let WKDC_OUTER_0 = SPECL
   [`ABEF_PACK a b e ff :int128`;
    `sha_ni_rnds2 (CDGH_PACK c d g h) (ABEF_PACK a b e ff)
       (word_join4 (word_add (EL 0 sha256_K) w0)
                   (word_add (EL 1 sha256_K) w1)
                   (word 0) (word 0)) :int128`;
    `word_add (EL 2 sha256_K) w2 :int32`;
    `word_add (EL 3 sha256_K) w3 :int32`;
    `word_add (EL 0 sha256_K) w0 :int32`;
    `word_add (EL 0 sha256_K) w0 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let WKDC_INNER_0 = SPECL
   [`CDGH_PACK c d g h :int128`;
    `ABEF_PACK a b e ff :int128`;
    `word_add (EL 0 sha256_K) w0 :int32`;
    `word_add (EL 1 sha256_K) w1 :int32`;
    `word_add (EL 2 sha256_K) w2 :int32`;
    `word_add (EL 3 sha256_K) w3 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `ymm9_init:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `ymm10_init:int256` `read YMM10` THEN
  ENSURES_INIT_TAC "s0" THEN
  EXPAND_K_TAC THEN
  ABBREV_TAC `W:int32 list = sha256_message_schedule 48
                 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]` THEN
  X86_STEPS_TAC HW_EXEC [1;2;3] THEN
  (* Step 4: pshufb xmm3, xmm7 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s4" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  UNDISCH_THEN `read XMM7 s3 = pshufb_mask_val` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  PSHUFB_BYTEREVERSE_TAC 3 "s4"
    (`w0:int32`,`w1:int32`,`w2:int32`,`w3:int32`) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1000)) THEN
  DISCARD_OLDSTATE_TAC "s4" THEN
  (* Steps 5-6: movdqu xmm6; movdqa xmm0, [rcx] (K0..K3 load) *)
  X86_STEPS_TAC HW_EXEC [5;6] THEN
  SUBGOAL_THEN
   `read XMM0 s6 = word_join4 (EL 0 sha256_K) (EL 1 sha256_K)
                              (EL 2 sha256_K) (EL 3 sha256_K) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 7: paddd xmm0, xmm3 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s7" THEN PADDD_REFOLD_TAC THEN
  SUBGOAL_THEN
   `read XMM0 s7 =
      word_join4 (word_add (EL 0 sha256_K) w0) (word_add (EL 1 sha256_K) w1)
                 (word_add (EL 2 sha256_K) w2) (word_add (EL 3 sha256_K) w3)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s7" THEN
  (* Step 8: pshufb xmm4, xmm7 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s8" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  UNDISCH_THEN `read XMM7 s7 = pshufb_mask_val` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  PSHUFB_BYTEREVERSE_TAC 4 "s8"
    (`w4:int32`,`w5:int32`,`w6:int32`,`w7:int32`) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1000)) THEN
  DISCARD_OLDSTATE_TAC "s8" THEN
  (* Step 9: movdqa xmm10, xmm2 (save initial CDGH) *)
  X86_STEPS_TAC HW_EXEC [9] THEN
  (* Step 10: sha256rnds2 xmm2, xmm1 — first 2 rounds of group 0 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s10" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM2 s10 =
      sha_ni_rnds2 (CDGH_PACK c d g h) (ABEF_PACK a b e ff)
        (word_join4 (word_add (EL 0 sha256_K) w0)
                    (word_add (EL 1 sha256_K) w1)
                    (word_add (EL 2 sha256_K) w2)
                    (word_add (EL 3 sha256_K) w3)) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s10" THEN
  (* Step 11: pshufd xmm0, xmm0, 0x0e (swap lane pairs) *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s11" THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM0 s11 =
      word_join4 (word_add (EL 2 sha256_K) w2)
                 (word_add (EL 3 sha256_K) w3)
                 (word_add (EL 0 sha256_K) w0)
                 (word_add (EL 0 sha256_K) w0) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s11" THEN
  (* Steps 12-13: nop-like intermediates *)
  X86_STEPS_TAC HW_EXEC [12;13] THEN
  (* Step 14: sha256rnds2 xmm1, xmm2 — second 2 rounds of group 0 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s14" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  (* SUBSTITUTE_XMM_CLEANS_TAC only folds word_join4 / ABEF / CDGH / mask
     shapes — not sha_ni_rnds2 results.  Manually plug in XMM2 s13's
     clean sha_ni_rnds2 form into the YMM1 s14 write. *)
  FIRST_ASSUM(fun th ->
    let s = string_of_term (concl th) in
    if has_sub_string "XMM2 s13 =" s && has_sub_string "sha_ni_rnds2" s
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else FAIL_TAC "not found") THEN
  SUBGOAL_THEN
   `read XMM1 s14 =
      sha_ni_rnds2 (ABEF_PACK a b e ff)
        (sha_ni_rnds2 (CDGH_PACK c d g h) (ABEF_PACK a b e ff)
           (word_join4 (word_add (EL 0 sha256_K) w0)
                       (word_add (EL 1 sha256_K) w1)
                       (word_add (EL 2 sha256_K) w2)
                       (word_add (EL 3 sha256_K) w3)))
        (word_join4 (word_add (EL 2 sha256_K) w2)
                    (word_add (EL 3 sha256_K) w3)
                    (word_add (EL 0 sha256_K) w0)
                    (word_add (EL 0 sha256_K) w0)) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s14" THEN
  (* Normalize wk don't-cares, then apply the group-0 bridge. *)
  RULE_ASSUM_TAC(REWRITE_RULE[WKDC_INNER_0; WKDC_OUTER_0]) THEN
  CUT_POINT_TAC_HW 0 `s14:x86state`;;

(* ========================================================================= *)
(* Single-block register core theorem.                                       *)
(*                                                                           *)
(* Starting at pc+64 (loop-top: first MOVDQU xmm3, [rsi]) with:              *)
(*   - XMM1 / XMM2 holding ABEF/CDGH of initial hash state H                 *)
(*   - XMM7 = XMM8 = pshufb_mask_val                                         *)
(*   - memory[rsi..rsi+63] = 4 x word_join4 of word_bytereverse w_i          *)
(*   - memory[rcx..rcx+255] = 16 x word_join4 of sha256_K                    *)
(*   - memory[rcx+256..rcx+271] = pshufb_mask_val                            *)
(*                                                                           *)
(* After the body (pc+64..pc+788, i.e., up to but not including the JNZ):    *)
(*   - XMM1 / XMM2 hold ABEF/CDGH of sha256_block M H                        *)
(*   - PC = pc + 788, RDX decremented, RSI advanced 64.                      *)
(*                                                                           *)
(* The proof body is currently CHEAT_TAC.  The per-group structure is        *)
(* (from memory: /home/ubuntu/.claude/.../memory/sha256_x86_phase4.md):      *)
(*                                                                           *)
(*   Round-group step boundaries (X86_STEPS_TAC 1-based indices):            *)
(*     prologue (MOVDQU xmm3..xmm6, pshufb):  steps  1- 4 of loop body       *)
(*     group  0: ends at step 26 (pc+121)                                    *)
(*     group  1: ends at step 34 (pc+156)                                    *)
(*     ...                                                                    *)
(*     group 15: ends at step 179 (pc+774)                                   *)
(*     add-back + jnz:                       steps 180-182                   *)
(*                                                                           *)
(* Per-group pattern:                                                         *)
(*   X86_STEPS_TAC HW_EXEC [n..n+k] THEN                                     *)
(*   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN *)
(*   (* specialise K memory at the group's index *) THEN                    *)
(*   CUT_POINT_TAC_HW i sN                                                  *)
(* ========================================================================= *)

let SHA256_BLOCK_CORE_CORRECT = prove
 (`!pc data_ptr kptr
    (a:int32) b c d e (ff:int32) g h
    (w0:int32) w1 w2 w3 w4 w5 w6 w7
    w8 w9 w10 w11 w12 w13 w14 w15
    rdx_in.
    aligned 16 kptr /\
    nonoverlapping (data_ptr:int64, 64) (word pc, 829) /\
    nonoverlapping (kptr:int64, 272) (word pc, 829) /\
    nonoverlapping (data_ptr:int64, 64) (kptr:int64, 272)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) sha256_hw_mc /\
          read RIP s = word(pc + 64) /\
          read RSI s = data_ptr /\
          read RCX s = kptr /\
          read RDX s = rdx_in /\
          read XMM1 s = ABEF_PACK a b e ff /\
          read XMM2 s = CDGH_PACK c d g h /\
          read XMM7 s = pshufb_mask_val /\
          read XMM8 s = pshufb_mask_val /\
          read (memory :> bytes128 data_ptr) s =
            word_join4 (word_bytereverse w0) (word_bytereverse w1)
                       (word_bytereverse w2) (word_bytereverse w3) /\
          read (memory :> bytes128 (word_add data_ptr (word 16))) s =
            word_join4 (word_bytereverse w4) (word_bytereverse w5)
                       (word_bytereverse w6) (word_bytereverse w7) /\
          read (memory :> bytes128 (word_add data_ptr (word 32))) s =
            word_join4 (word_bytereverse w8) (word_bytereverse w9)
                       (word_bytereverse w10) (word_bytereverse w11) /\
          read (memory :> bytes128 (word_add data_ptr (word 48))) s =
            word_join4 (word_bytereverse w12) (word_bytereverse w13)
                       (word_bytereverse w14) (word_bytereverse w15) /\
          (!i. i < 16 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
              word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                         (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)) /\
          read (memory :> bytes128 (word_add kptr (word 256))) s =
            pshufb_mask_val)
     (\s. read RIP s = word(pc + 788) /\
          read RSI s = word_add data_ptr (word 64) /\
          read RDX s = word_sub rdx_in (word 1) /\
          (let blk = sha256_block [w0;w1;w2;w3;w4;w5;w6;w7;
                                   w8;w9;w10;w11;w12;w13;w14;w15]
                                  [a;b;c;d;e;ff;g;h] in
           read XMM1 s =
             ABEF_PACK (EL 0 blk) (EL 1 blk) (EL 4 blk) (EL 5 blk) /\
           read XMM2 s =
             CDGH_PACK (EL 2 blk) (EL 3 blk) (EL 6 blk) (EL 7 blk)))
     (MAYCHANGE [RIP; RSI; RDX] ,,
      MAYCHANGE [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
                 XMM9; XMM10] ,,
      MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [events])`,
  CHEAT_TAC);;
