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

(* ------------------------------------------------------------------------- *)
(* State-shift lemmas: after 2 more compression rounds, positions 2,3,6,7   *)
(* of the state list equal positions 0,1,4,5 of the prior state — this is   *)
(* simply the "shift by 2 slots" structure of sha256_compress_round.         *)
(*                                                                           *)
(* Consequence: `ABEF_PACK (compress 2i W H) = CDGH_PACK (compress (2i+2) W  *)
(* H)` (via CDGH_EQ_ABEF), which lets us rewrite the physical x86 XMM2       *)
(* (carrying `ABEF_PACK (compress (4i+2))`) into the CDGH_PACK form that    *)
(* GROUP_BRIDGE_H.(i+1) expects as the inner sha_ni_rnds2's first operand.  *)
(* ------------------------------------------------------------------------- *)

(* SHA256_COMPRESS_ROUND_2_HW_FORM generalized from [a;…;h] to any length-8 *)
(* state list.  Since `sha256_compress_round` reads `EL i state` symbolically, *)
(* expanding with let_CONV + EL_CONV yields the shifted state for free.     *)
let SHA256_COMPRESS_ROUND_2_HW_LIST = prove
 (`!wk0 wk1 s:int32 list.
     LENGTH s = 8 ==>
     EL 2 (sha256_compress_round wk1 (word 0)
            (sha256_compress_round wk0 (word 0) s)) = EL 0 s /\
     EL 3 (sha256_compress_round wk1 (word 0)
            (sha256_compress_round wk0 (word 0) s)) = EL 1 s /\
     EL 6 (sha256_compress_round wk1 (word 0)
            (sha256_compress_round wk0 (word 0) s)) = EL 4 s /\
     EL 7 (sha256_compress_round wk1 (word 0)
            (sha256_compress_round wk0 (word 0) s)) = EL 5 s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha256_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REFL_TAC);;

(* General state-shift for sha256_compress: proved once for all n via the   *)
(* HW_LIST form plus PREADD_SYM (which normalizes the two rounds to have    *)
(* the (wk, word 0) shape that HW_LIST recognises).                          *)
let COMPRESS_EL_SHIFT_2 = prove
 (`!n W (H:int32 list). LENGTH H = 8 ==>
     EL 2 (sha256_compress (n+2) W H) = EL 0 (sha256_compress n W H) /\
     EL 3 (sha256_compress (n+2) W H) = EL 1 (sha256_compress n W H) /\
     EL 6 (sha256_compress (n+2) W H) = EL 4 (sha256_compress n W H) /\
     EL 7 (sha256_compress (n+2) W H) = EL 5 (sha256_compress n W H)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n + 2 = (n+1)+1`(fun th -> ONCE_REWRITE_TAC[th])
    THENL [ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[sha256_compress] THEN
  ONCE_REWRITE_TAC[sha256_compress] THEN
  ONCE_REWRITE_TAC[GSYM SHA256_COMPRESS_ROUND_PREADD_SYM] THEN
  SUBGOAL_THEN
   `sha256_compress_round (EL n sha256_K) (EL n W) (sha256_compress n W H) =
    sha256_compress_round (word_add (EL n W) (EL n sha256_K)) (word 0)
                          (sha256_compress n W H)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC SHA256_COMPRESS_ROUND_2_HW_LIST THEN
  MATCH_MP_TAC LENGTH_SHA256_COMPRESS THEN
  ASM_REWRITE_TAC[]);;

(* Group-i instance is obtained by:                                          *)
(*   let shift_i = CONV_RULE(DEPTH_CONV NUM_ADD_CONV)                        *)
(*     (MATCH_MP (SPECL [mk_small_numeral(4i+2); `W`; H_tm] COMPRESS_EL_SHIFT_2) *)
(*               length_H_thm) in …                                           *)

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

(* SHA256MSG1 analogue: fold the stepper's expanded msg1 output into the     *)
(* clean `sha_ni_msg1 (read XMMd s_prev) (read XMMs s_prev)` shape.         *)
let SHA_NI_MSG1_UNFOLDED =
  CONV_RULE(TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV NUM_EXP_CONV)
    sha_ni_msg1;;

let FOLD_SHA_NI_MSG1_TAC =
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_EXP_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM sha256_sigma0]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM SHA_NI_MSG1_UNFOLDED]);;

(* SHA256MSG2 analogue: fold the stepper's expanded msg2 output into the     *)
(* clean `sha_ni_msg2 (read XMMd s_prev) (read XMMs s_prev)` shape.         *)
let SHA_NI_MSG2_UNFOLDED =
  CONV_RULE(TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV NUM_EXP_CONV)
    sha_ni_msg2;;

let FOLD_SHA_NI_MSG2_TAC =
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_EXP_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM sha256_sigma1]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM SHA_NI_MSG2_UNFOLDED]);;

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

(* Check if a term is `read XMM_i s = rhs` where rhs is a clean form:        *)
(*   word_join4 …, ABEF_PACK …, CDGH_PACK …, pshufb_mask_val, or            *)
(*   sha_ni_msg1/msg2/rnds2 of clean args.  Uses structural term inspection *)
(*   instead of string matching (which breaks on multi-line pretty prints).  *)
let is_clean_xmm_read tm =
  try
    let l,r = dest_eq tm in
    let op,args = strip_comb l in
    if not (is_const op && fst(dest_const op) = "read") then false else
    (match args with
     | [reg; _] ->
        let rop,_ = strip_comb reg in
        is_const rop &&
        (let name = fst(dest_const rop) in
         String.length name >= 3 && String.sub name 0 3 = "XMM") &&
        (let rop2,_ = strip_comb r in
         is_const rop2 &&
         List.mem (fst(dest_const rop2))
           ["word_join4"; "ABEF_PACK"; "CDGH_PACK"; "pshufb_mask_val"])
     | _ -> false)
  with _ -> false;;

let SUBSTITUTE_XMM_CLEANS_TAC : tactic = fun g ->
  let (asl,_) = g in
  let clean_thms = List.filter_map (fun (_,th) ->
    if is_clean_xmm_read (concl th) then Some th else None) asl in
  (* Skip the clean assumptions themselves when rewriting — otherwise
     REWRITE_RULE on `read XMM_i s = C` rewrites its own LHS to RHS and the
     assumption collapses to `C = C` → T → dropped. *)
  RULE_ASSUM_TAC(fun th ->
    if is_clean_xmm_read (concl th)
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
(* GROUP1_TAC: symbolic execution of group 1 (steps 15-22) + CUT_POINT 1.    *)
(*                                                                           *)
(* Group 1 adds two novel pieces on top of group 0's pattern:                *)
(*   • SHA256MSG1 xmm3, xmm4 (step 21): first step of a schedule-extension  *)
(*     triple.  The clean XMM3 / XMM4 word_join4 forms (preserved across   *)
(*     group 0) feed in; the output is sha_ni_msg1 of the two, which by     *)
(*     SHA256MSG1_BRIDGE equals word_join4 (w_j + sigma0(w_{j+1})) … .      *)
(*   • LEA rsi, [rsi+64] (step 20): advances the data pointer by 64 bytes.  *)
(*                                                                           *)
(* The critical twist is that XMM2 carries `ABEF_PACK (compress (4i+2))`    *)
(* after CUT_POINT i.  For group (i+1)'s first sha_ni_rnds2, GROUP_BRIDGE   *)
(* expects `CDGH_PACK (compress (4i+4))` — which is the same 128-bit value  *)
(* by CDGH_EQ_ABEF + COMPRESS_EL_SHIFT.  We rewrite XMM2 accordingly before *)
(* step 18 so SUBSTITUTE_XMM_CLEANS_TAC can plug it in during the fold.    *)
(* ========================================================================= *)

let GROUP1_TAC : tactic =
  let WKDC_OUTER_1 = SPECL
   [`ABEF_PACK (EL 0 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])) :int128`;
    `sha_ni_rnds2
       (CDGH_PACK (EL 2 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                  (EL 3 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                  (EL 6 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                  (EL 7 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])))
       (ABEF_PACK (EL 0 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                  (EL 1 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                  (EL 4 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                  (EL 5 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])))
       (word_join4 (word_add (EL 4 sha256_K) w4)
                   (word_add (EL 5 sha256_K) w5)
                   (word 0) (word 0)) :int128`;
    `word_add (EL 6 sha256_K) w6 :int32`;
    `word_add (EL 7 sha256_K) w7 :int32`;
    `word_add (EL 4 sha256_K) w4 :int32`;
    `word_add (EL 4 sha256_K) w4 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let WKDC_INNER_1 = SPECL
   [`CDGH_PACK (EL 2 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 3 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 6 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 7 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])) :int128`;
    `ABEF_PACK (EL 0 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])) :int128`;
    `word_add (EL 4 sha256_K) w4 :int32`;
    `word_add (EL 5 sha256_K) w5 :int32`;
    `word_add (EL 6 sha256_K) w6 :int32`;
    `word_add (EL 7 sha256_K) w7 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let len_h_thm = prove
   (`LENGTH [a:int32;b;c;d;e;ff;g;h] = 8`,
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let compress_el_shift_0 =
    CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MATCH_MP
        (SPECL [`2`; `W:int32 list`; `[a:int32;b;c;d;e;ff;g;h]`]
               COMPRESS_EL_SHIFT_2)
        len_h_thm) in
  (* Step 15: movdqa xmm0, [rcx+16] (K4..K7 load) *)
  X86_STEPS_TAC HW_EXEC [15] THEN
  SUBGOAL_THEN
   `read XMM0 s15 = word_join4 (EL 4 sha256_K) (EL 5 sha256_K)
                              (EL 6 sha256_K) (EL 7 sha256_K) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 16: paddd xmm0, xmm4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s16" THEN PADDD_REFOLD_TAC THEN
  SUBGOAL_THEN
   `read XMM0 s16 =
      word_join4 (word_add (EL 4 sha256_K) w4) (word_add (EL 5 sha256_K) w5)
                 (word_add (EL 6 sha256_K) w6) (word_add (EL 7 sha256_K) w7)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s16" THEN
  (* Step 17: pshufb xmm5, xmm7 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s17" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  UNDISCH_THEN `read XMM7 s16 = pshufb_mask_val` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  PSHUFB_BYTEREVERSE_TAC 5 "s17"
    (`w8:int32`,`w9:int32`,`w10:int32`,`w11:int32`) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1000)) THEN
  DISCARD_OLDSTATE_TAC "s17" THEN
  (* Before step 18, re-shape XMM2 from `ABEF_PACK (compress 2)` to
     `CDGH_PACK (compress 4)`. *)
  SUBGOAL_THEN
   `read XMM2 s17 = CDGH_PACK
     (EL 2 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[CDGH_EQ_ABEF] THEN
    REWRITE_TAC[compress_el_shift_0]; ALL_TAC] THEN
  (* Drop the old ABEF form so SUBSTITUTE plugs the CDGH form. *)
  UNDISCH_TAC `read XMM2 s17 = ABEF_PACK
     (EL 0 (sha256_compress 2 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 2 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 2 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 2 W [a; b; c; d; e; ff; g; h]))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* Step 18: sha256rnds2 xmm2, xmm1 — first RNDS2 of group 1 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s18" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  (* SUBSTITUTE doesn't plug refs to XMM2 s17 / XMM1 s17 inside the YMM2
     write; do it manually. *)
  UNDISCH_THEN
   `read XMM2 s17 = CDGH_PACK
     (EL 2 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))`
   (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  UNDISCH_THEN
   `read XMM1 s17 = ABEF_PACK
     (EL 0 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))`
   (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM2 s18 =
      sha_ni_rnds2
        (CDGH_PACK (EL 2 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 3 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 6 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 7 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])))
        (ABEF_PACK (EL 0 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])))
        (word_join4 (word_add (EL 4 sha256_K) w4) (word_add (EL 5 sha256_K) w5)
                    (word_add (EL 6 sha256_K) w6) (word_add (EL 7 sha256_K) w7))
     :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s18" THEN
  (* Step 19: pshufd xmm0, xmm0, 0x0e *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s19" THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM0 s19 =
      word_join4 (word_add (EL 6 sha256_K) w6) (word_add (EL 7 sha256_K) w7)
                 (word_add (EL 4 sha256_K) w4) (word_add (EL 4 sha256_K) w4)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s19" THEN
  (* Step 20: lea rsi, [rsi+64] *)
  X86_STEPS_TAC HW_EXEC [20] THEN
  (* Step 21: sha256msg1 xmm3, xmm4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s21" THEN
  FOLD_SHA_NI_MSG1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM3 s21 =
      sha_ni_msg1 (word_join4 w0 w1 w2 w3) (word_join4 w4 w5 w6 w7)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM3; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s21" THEN
  (* Step 22: sha256rnds2 xmm1, xmm2 — second RNDS2 of group 1 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s22" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  FIRST_ASSUM(fun th ->
    let s = string_of_term (concl th) in
    if has_sub_string "XMM2 s21 =" s && has_sub_string "sha_ni_rnds2" s
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else FAIL_TAC "not found") THEN
  UNDISCH_THEN
   `read XMM1 s21 = ABEF_PACK
     (EL 0 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 4 W [a; b; c; d; e; ff; g; h]))`
   (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM1 s22 =
      sha_ni_rnds2
        (ABEF_PACK (EL 0 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])))
        (sha_ni_rnds2
           (CDGH_PACK (EL 2 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                      (EL 3 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                      (EL 6 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                      (EL 7 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])))
           (ABEF_PACK (EL 0 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                      (EL 1 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                      (EL 4 (sha256_compress 4 W [a;b;c;d;e;ff;g;h]))
                      (EL 5 (sha256_compress 4 W [a;b;c;d;e;ff;g;h])))
           (word_join4 (word_add (EL 4 sha256_K) w4)
                       (word_add (EL 5 sha256_K) w5)
                       (word_add (EL 6 sha256_K) w6)
                       (word_add (EL 7 sha256_K) w7)))
        (word_join4 (word_add (EL 6 sha256_K) w6)
                    (word_add (EL 7 sha256_K) w7)
                    (word_add (EL 4 sha256_K) w4)
                    (word_add (EL 4 sha256_K) w4)) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s22" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WKDC_INNER_1; WKDC_OUTER_1]) THEN
  CUT_POINT_TAC_HW 1 `s22:x86state`;;

(* ========================================================================= *)
(* GROUP2_TAC: symbolic execution of group 2 (steps 23-33) + CUT_POINT 2.    *)
(*                                                                           *)
(* Group 2 is the first group with the full schedule-extension machinery:    *)
(*   • Steps 28/29 `movdqa xmm7,xmm6` then `palignr xmm7,xmm5,0x4` give the  *)
(*     palignr intermediate word_join4 w9 w10 w11 w12.                        *)
(*   • Step 31 `paddd xmm3,xmm7` combines the prior group's msg1 output      *)
(*     (word_join4 (w_j+sigma0 w_{j+1})...) with the palignr word_join4.     *)
(*     XMM3 must first be SHA256MSG1_BRIDGE'd from its sha_ni_msg1 form into *)
(*     a word_join4 so PADDD_REFOLD_TAC can operate.                          *)
(*   • Step 32 `sha256msg1 xmm4,xmm5` starts the next schedule-extension     *)
(*     triple for w_{16..19} — uses FOLD_SHA_NI_MSG1_TAC.                     *)
(*                                                                           *)
(* Important gotcha at step 28: `movdqa xmm7,xmm6` stepper produces a YMM7   *)
(* s28 assumption that references `read YMM7 s27` and `read YMM6 s27` —     *)
(* neither of which is in asl (we only kept XMM clean forms).  Apply        *)
(* YMM_TO_XMM_SUBWORD to the assumption list BEFORE asserting the clean     *)
(* XMM7 s28 form.                                                            *)
(* ========================================================================= *)

let GROUP2_TAC : tactic =
  let WKDC_OUTER_2 = SPECL
   [`ABEF_PACK (EL 0 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])) :int128`;
    `sha_ni_rnds2
       (CDGH_PACK (EL 2 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                  (EL 3 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                  (EL 6 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                  (EL 7 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])))
       (ABEF_PACK (EL 0 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                  (EL 1 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                  (EL 4 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                  (EL 5 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])))
       (word_join4 (word_add (EL 8 sha256_K) w8)
                   (word_add (EL 9 sha256_K) w9)
                   (word 0) (word 0)) :int128`;
    `word_add (EL 10 sha256_K) w10 :int32`;
    `word_add (EL 11 sha256_K) w11 :int32`;
    `word_add (EL 8 sha256_K) w8 :int32`;
    `word_add (EL 8 sha256_K) w8 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let WKDC_INNER_2 = SPECL
   [`CDGH_PACK (EL 2 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 3 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 6 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 7 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])) :int128`;
    `ABEF_PACK (EL 0 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])) :int128`;
    `word_add (EL 8 sha256_K) w8 :int32`;
    `word_add (EL 9 sha256_K) w9 :int32`;
    `word_add (EL 10 sha256_K) w10 :int32`;
    `word_add (EL 11 sha256_K) w11 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let len_h_thm = prove
   (`LENGTH [a:int32;b;c;d;e;ff;g;h] = 8`,
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let compress_el_shift_1 =
    CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MATCH_MP
        (SPECL [`6`; `W:int32 list`; `[a:int32;b;c;d;e;ff;g;h]`]
               COMPRESS_EL_SHIFT_2)
        len_h_thm) in
  (* Step 23: movdqa xmm0, [rcx+32] (K8..K11) *)
  X86_STEPS_TAC HW_EXEC [23] THEN
  SUBGOAL_THEN
   `read XMM0 s23 = word_join4 (EL 8 sha256_K) (EL 9 sha256_K)
                              (EL 10 sha256_K) (EL 11 sha256_K) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 24: paddd xmm0, xmm5 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s24" THEN PADDD_REFOLD_TAC THEN
  SUBGOAL_THEN
   `read XMM0 s24 =
      word_join4 (word_add (EL 8 sha256_K) w8) (word_add (EL 9 sha256_K) w9)
                 (word_add (EL 10 sha256_K) w10) (word_add (EL 11 sha256_K) w11)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s24" THEN
  (* Step 25: pshufb xmm6, xmm7 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s25" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  UNDISCH_THEN `read XMM7 s24 = pshufb_mask_val` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  PSHUFB_BYTEREVERSE_TAC 6 "s25"
    (`w12:int32`,`w13:int32`,`w14:int32`,`w15:int32`) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1000)) THEN
  DISCARD_OLDSTATE_TAC "s25" THEN
  (* Shift XMM2 from ABEF_PACK (compress 6) to CDGH_PACK (compress 8) *)
  SUBGOAL_THEN
   `read XMM2 s25 = CDGH_PACK
     (EL 2 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[CDGH_EQ_ABEF] THEN
    REWRITE_TAC[compress_el_shift_1]; ALL_TAC] THEN
  UNDISCH_TAC `read XMM2 s25 = ABEF_PACK
     (EL 0 (sha256_compress 6 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 6 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 6 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 6 W [a; b; c; d; e; ff; g; h]))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* Step 26: sha256rnds2 xmm2, xmm1 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s26" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  UNDISCH_THEN
   `read XMM2 s25 = CDGH_PACK
     (EL 2 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  UNDISCH_THEN
   `read XMM1 s25 = ABEF_PACK
     (EL 0 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM2 s26 =
      sha_ni_rnds2
        (CDGH_PACK (EL 2 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 3 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 6 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 7 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])))
        (ABEF_PACK (EL 0 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])))
        (word_join4 (word_add (EL 8 sha256_K) w8) (word_add (EL 9 sha256_K) w9)
                    (word_add (EL 10 sha256_K) w10) (word_add (EL 11 sha256_K) w11))
     :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s26" THEN
  (* Step 27: pshufd xmm0, xmm0, 0x0e *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s27" THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM0 s27 =
      word_join4 (word_add (EL 10 sha256_K) w10) (word_add (EL 11 sha256_K) w11)
                 (word_add (EL 8 sha256_K) w8) (word_add (EL 8 sha256_K) w8)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 28: movdqa xmm7, xmm6 — need YMM_TO_XMM_SUBWORD to simplify the
     stepper's `word_subword (read YMM6 s_prev) (0,128)` down to XMM6 s_prev. *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s28" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBGOAL_THEN
   `read XMM7 s28 = word_join4 w12 w13 w14 w15 :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s28" THEN
  (* Step 29: palignr xmm7, xmm5, 0x4 — shifts (xmm7 || xmm5) right by 4 bytes *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s29" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PALIGNR_4_WORD_JOIN4]) THEN
  SUBGOAL_THEN
   `read XMM7 s29 = word_join4 w9 w10 w11 w12 :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s29" THEN
  (* Step 30: nop *)
  X86_STEPS_TAC HW_EXEC [30] THEN
  (* Expand XMM3 from sha_ni_msg1 to word_join4 via SHA256MSG1_BRIDGE so
     PADDD_REFOLD can consume it at step 31. *)
  SUBGOAL_THEN
   `read XMM3 s30 =
      word_join4 (word_add w0 (sha256_sigma0 w1))
                 (word_add w1 (sha256_sigma0 w2))
                 (word_add w2 (sha256_sigma0 w3))
                 (word_add w3 (sha256_sigma0 w4)) :int128`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SHA256MSG1_BRIDGE]; ALL_TAC] THEN
  UNDISCH_TAC
   `read XMM3 s30 = sha_ni_msg1 (word_join4 w0 w1 w2 w3) (word_join4 w4 w5 w6 w7)` THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* Step 31: paddd xmm3, xmm7 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s31" THEN PADDD_REFOLD_TAC THEN
  (* PADDD_REFOLD didn't collapse xmm3's word_subword lanes because the
     clean XMM3 s30 form has `word_add w_i (sigma0 w_{i+1})` lanes.  Manually
     substitute + simplify. *)
  UNDISCH_THEN
   `read XMM3 s30 =
      word_join4 (word_add w0 (sha256_sigma0 w1))
                 (word_add w1 (sha256_sigma0 w2))
                 (word_add w2 (sha256_sigma0 w3))
                 (word_add w3 (sha256_sigma0 w4))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM3 s31 =
      word_join4 (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                 (word_add (word_add w1 (sha256_sigma0 w2)) w10)
                 (word_add (word_add w2 (sha256_sigma0 w3)) w11)
                 (word_add (word_add w3 (sha256_sigma0 w4)) w12) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM3; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s31" THEN
  (* Step 32: sha256msg1 xmm4, xmm5 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s32" THEN
  FOLD_SHA_NI_MSG1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM4 s32 =
      sha_ni_msg1 (word_join4 w4 w5 w6 w7) (word_join4 w8 w9 w10 w11) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s32" THEN
  (* Step 33: sha256rnds2 xmm1, xmm2 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s33" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  FIRST_ASSUM(fun th ->
    let s = string_of_term (concl th) in
    if has_sub_string "XMM2 s32 =" s && has_sub_string "sha_ni_rnds2" s
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else FAIL_TAC "not found") THEN
  UNDISCH_THEN
   `read XMM1 s32 = ABEF_PACK
     (EL 0 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 8 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM1 s33 =
      sha_ni_rnds2
        (ABEF_PACK (EL 0 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])))
        (sha_ni_rnds2
           (CDGH_PACK (EL 2 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                      (EL 3 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                      (EL 6 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                      (EL 7 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])))
           (ABEF_PACK (EL 0 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                      (EL 1 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                      (EL 4 (sha256_compress 8 W [a;b;c;d;e;ff;g;h]))
                      (EL 5 (sha256_compress 8 W [a;b;c;d;e;ff;g;h])))
           (word_join4 (word_add (EL 8 sha256_K) w8)
                       (word_add (EL 9 sha256_K) w9)
                       (word_add (EL 10 sha256_K) w10)
                       (word_add (EL 11 sha256_K) w11)))
        (word_join4 (word_add (EL 10 sha256_K) w10)
                    (word_add (EL 11 sha256_K) w11)
                    (word_add (EL 8 sha256_K) w8)
                    (word_add (EL 8 sha256_K) w8)) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s33" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WKDC_INNER_2; WKDC_OUTER_2]) THEN
  CUT_POINT_TAC_HW 2 `s33:x86state`;;

(* ========================================================================= *)
(* GROUP3_TAC: symbolic execution of group 3 (steps 34-44) + CUT_POINT 3.    *)
(*                                                                           *)
(* Group 3 is the first group with SHA256MSG2 — the third and final piece   *)
(* of the schedule-extension triple started at group 1 (sha256msg1) and      *)
(* continued at group 2 (palignr + paddd).  Group 3 therefore produces      *)
(* w_{16..19} in XMM3 and kicks off the next triple (msg1 on XMM5).          *)
(*                                                                           *)
(* Instruction layout (same pattern used in groups 4-14):                    *)
(*   34: movdqa    xmm0, [rcx+48]  — K12..K15 load                          *)
(*   35: paddd     xmm0, xmm6      — K12..K15 + w12..w15                    *)
(*   36: sha256msg2 xmm3, xmm6     — completes w_{16..19} in XMM3           *)
(*   37: sha256rnds2 xmm2, xmm1                                              *)
(*   38: pshufd    xmm0, xmm0, 0x0e                                          *)
(*   39: movdqa    xmm7, xmm3                                                *)
(*   40: palignr   xmm7, xmm6, 4                                             *)
(*   41: nop                                                                 *)
(*   42: paddd     xmm4, xmm7      — schedule-extension add for next triple *)
(*   43: sha256msg1 xmm5, xmm6     — msg1 for the triple after that          *)
(*   44: sha256rnds2 xmm1, xmm2                                              *)
(* ========================================================================= *)

let GROUP3_TAC : tactic =
  let WKDC_OUTER_3 = SPECL
   [`ABEF_PACK (EL 0 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])) :int128`;
    `sha_ni_rnds2
       (CDGH_PACK (EL 2 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                  (EL 3 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                  (EL 6 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                  (EL 7 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])))
       (ABEF_PACK (EL 0 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                  (EL 1 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                  (EL 4 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                  (EL 5 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])))
       (word_join4 (word_add (EL 12 sha256_K) w12)
                   (word_add (EL 13 sha256_K) w13)
                   (word 0) (word 0)) :int128`;
    `word_add (EL 14 sha256_K) w14 :int32`;
    `word_add (EL 15 sha256_K) w15 :int32`;
    `word_add (EL 12 sha256_K) w12 :int32`;
    `word_add (EL 12 sha256_K) w12 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let WKDC_INNER_3 = SPECL
   [`CDGH_PACK (EL 2 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 3 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 6 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 7 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])) :int128`;
    `ABEF_PACK (EL 0 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])) :int128`;
    `word_add (EL 12 sha256_K) w12 :int32`;
    `word_add (EL 13 sha256_K) w13 :int32`;
    `word_add (EL 14 sha256_K) w14 :int32`;
    `word_add (EL 15 sha256_K) w15 :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let len_h_thm = prove
   (`LENGTH [a:int32;b;c;d;e;ff;g;h] = 8`,
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let compress_el_shift_2 =
    CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MATCH_MP
        (SPECL [`10`; `W:int32 list`; `[a:int32;b;c;d;e;ff;g;h]`]
               COMPRESS_EL_SHIFT_2)
        len_h_thm) in
  (* Step 34: movdqa xmm0, [rcx+48] (K12..K15) *)
  X86_STEPS_TAC HW_EXEC [34] THEN
  SUBGOAL_THEN
   `read XMM0 s34 = word_join4 (EL 12 sha256_K) (EL 13 sha256_K)
                              (EL 14 sha256_K) (EL 15 sha256_K) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 35: paddd xmm0, xmm6 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s35" THEN PADDD_REFOLD_TAC THEN
  SUBGOAL_THEN
   `read XMM0 s35 =
      word_join4 (word_add (EL 12 sha256_K) w12) (word_add (EL 13 sha256_K) w13)
                 (word_add (EL 14 sha256_K) w14) (word_add (EL 15 sha256_K) w15)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s35" THEN
  (* Step 36: sha256msg2 xmm3, xmm6 — completes w_{16..19} in XMM3 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s36" THEN
  FOLD_SHA_NI_MSG2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM3 s36 =
      sha_ni_msg2
        (word_join4 (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                    (word_add (word_add w1 (sha256_sigma0 w2)) w10)
                    (word_add (word_add w2 (sha256_sigma0 w3)) w11)
                    (word_add (word_add w3 (sha256_sigma0 w4)) w12))
        (word_join4 w12 w13 w14 w15)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM3; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Expand sha_ni_msg2 into word_join4 w16 w17 w18 w19 via SHA256MSG2_BRIDGE *)
  UNDISCH_THEN
   `read XMM3 s36 =
      sha_ni_msg2
        (word_join4 (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                    (word_add (word_add w1 (sha256_sigma0 w2)) w10)
                    (word_add (word_add w2 (sha256_sigma0 w3)) w11)
                    (word_add (word_add w3 (sha256_sigma0 w4)) w12))
        (word_join4 w12 w13 w14 w15)`
   (fun th ->
      ASSUME_TAC(REWRITE_RULE[SHA256MSG2_BRIDGE]
        (CONV_RULE(RAND_CONV(REWR_CONV SHA256MSG2_BRIDGE THENC
                              TOP_DEPTH_CONV let_CONV)) th))) THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 2000))) THEN
  DISCARD_OLDSTATE_TAC "s36" THEN
  (* Shift XMM2 from ABEF_PACK (compress 10) to CDGH_PACK (compress 12) *)
  SUBGOAL_THEN
   `read XMM2 s36 = CDGH_PACK
     (EL 2 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[CDGH_EQ_ABEF] THEN
    REWRITE_TAC[compress_el_shift_2]; ALL_TAC] THEN
  UNDISCH_TAC `read XMM2 s36 = ABEF_PACK
     (EL 0 (sha256_compress 10 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 10 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 10 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 10 W [a; b; c; d; e; ff; g; h]))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* Step 37: sha256rnds2 xmm2, xmm1 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s37" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  UNDISCH_THEN
   `read XMM2 s36 = CDGH_PACK
     (EL 2 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  UNDISCH_THEN
   `read XMM1 s36 = ABEF_PACK
     (EL 0 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM2 s37 =
      sha_ni_rnds2
        (CDGH_PACK (EL 2 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 3 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 6 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 7 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])))
        (ABEF_PACK (EL 0 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])))
        (word_join4 (word_add (EL 12 sha256_K) w12)
                    (word_add (EL 13 sha256_K) w13)
                    (word_add (EL 14 sha256_K) w14)
                    (word_add (EL 15 sha256_K) w15))
     :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s37" THEN
  (* Step 38: pshufd xmm0, xmm0, 0x0e *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s38" THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM0 s38 =
      word_join4 (word_add (EL 14 sha256_K) w14) (word_add (EL 15 sha256_K) w15)
                 (word_add (EL 12 sha256_K) w12) (word_add (EL 12 sha256_K) w12)
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 39: movdqa xmm7, xmm3 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s39" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBGOAL_THEN
   `read XMM7 s39 =
      word_join4 (word_add (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                           (sha256_sigma1 w14))
                 (word_add (word_add (word_add w1 (sha256_sigma0 w2)) w10)
                           (sha256_sigma1 w15))
                 (word_add (word_add (word_add w2 (sha256_sigma0 w3)) w11)
                           (sha256_sigma1
                              (word_add (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                                        (sha256_sigma1 w14))))
                 (word_add (word_add (word_add w3 (sha256_sigma0 w4)) w12)
                           (sha256_sigma1
                              (word_add (word_add (word_add w1 (sha256_sigma0 w2)) w10)
                                        (sha256_sigma1 w15))))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s39" THEN
  (* Step 40: palignr xmm7, xmm6, 0x4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s40" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PALIGNR_4_WORD_JOIN4]) THEN
  SUBGOAL_THEN
   `read XMM7 s40 =
      word_join4 w13 w14 w15
        (word_add (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                  (sha256_sigma1 w14)) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s40" THEN
  (* Step 41: nop *)
  X86_STEPS_TAC HW_EXEC [41] THEN
  (* Expand XMM4 from sha_ni_msg1 to word_join4 via SHA256MSG1_BRIDGE *)
  SUBGOAL_THEN
   `read XMM4 s41 =
      word_join4 (word_add w4 (sha256_sigma0 w5))
                 (word_add w5 (sha256_sigma0 w6))
                 (word_add w6 (sha256_sigma0 w7))
                 (word_add w7 (sha256_sigma0 w8)) :int128`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SHA256MSG1_BRIDGE]; ALL_TAC] THEN
  UNDISCH_TAC
   `read XMM4 s41 = sha_ni_msg1 (word_join4 w4 w5 w6 w7) (word_join4 w8 w9 w10 w11)` THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* Step 42: paddd xmm4, xmm7 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s42" THEN PADDD_REFOLD_TAC THEN
  (* XMM4 s41 and XMM7 s41 have multi-line word_join4 pretty-prints; the
     updated SUBSTITUTE_XMM_CLEANS_TAC (term-structure based) handles these.
     Manual lane simplification still needed for the nested word_adds. *)
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM4 s42 =
      word_join4 (word_add (word_add w4 (sha256_sigma0 w5)) w13)
                 (word_add (word_add w5 (sha256_sigma0 w6)) w14)
                 (word_add (word_add w6 (sha256_sigma0 w7)) w15)
                 (word_add (word_add w7 (sha256_sigma0 w8))
                           (word_add (word_add (word_add w0 (sha256_sigma0 w1)) w9)
                                     (sha256_sigma1 w14))) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s42" THEN
  (* Step 43: sha256msg1 xmm5, xmm6 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s43" THEN
  FOLD_SHA_NI_MSG1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM5 s43 =
      sha_ni_msg1 (word_join4 w8 w9 w10 w11) (word_join4 w12 w13 w14 w15) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM5; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s43" THEN
  (* Step 44: sha256rnds2 xmm1, xmm2 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s44" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  FIRST_ASSUM(fun th ->
    let s = string_of_term (concl th) in
    if has_sub_string "XMM2 s43 =" s && has_sub_string "sha_ni_rnds2" s
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else FAIL_TAC "not found") THEN
  UNDISCH_THEN
   `read XMM1 s43 = ABEF_PACK
     (EL 0 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 12 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM1 s44 =
      sha_ni_rnds2
        (ABEF_PACK (EL 0 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])))
        (sha_ni_rnds2
           (CDGH_PACK (EL 2 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                      (EL 3 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                      (EL 6 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                      (EL 7 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])))
           (ABEF_PACK (EL 0 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                      (EL 1 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                      (EL 4 (sha256_compress 12 W [a;b;c;d;e;ff;g;h]))
                      (EL 5 (sha256_compress 12 W [a;b;c;d;e;ff;g;h])))
           (word_join4 (word_add (EL 12 sha256_K) w12)
                       (word_add (EL 13 sha256_K) w13)
                       (word_add (EL 14 sha256_K) w14)
                       (word_add (EL 15 sha256_K) w15)))
        (word_join4 (word_add (EL 14 sha256_K) w14)
                    (word_add (EL 15 sha256_K) w15)
                    (word_add (EL 12 sha256_K) w12)
                    (word_add (EL 12 sha256_K) w12)) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s44" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WKDC_INNER_3; WKDC_OUTER_3]) THEN
  CUT_POINT_TAC_HW 3 `s44:x86state`;;

(* ========================================================================= *)
(* GROUP4_TAC: symbolic execution of group 4 (steps 45-55) + CUT_POINT 4.    *)
(*                                                                           *)
(* G4 is the first "steady state" middle group: cur register (XMM3) carries *)
(* the just-completed triple w_{16..19} but in post-SHA256MSG2 nested-sigma *)
(* form — lane i equals EL (16+i) W only modulo word_add AC.  Lanes 2,3 of *)
(* XMM3 s44 contain `sha256_sigma1 (nested_16/17)` which must be rewritten *)
(* before WORD_BLAST can close per-lane equalities.                          *)
(*                                                                           *)
(* Strategy — two-phase lane normalization (reused at step 47's MSG2       *)
(* output for XMM4):                                                         *)
(*   Phase 1: prove lane 0,1 equalities `nested = EL 16/17 W` and apply    *)
(*            them as rewrites so sigma1 arguments in lanes 2,3 collapse.  *)
(*   Phase 2: prove lane 2,3 equalities (now with canonical sigma1 args)   *)
(*            and apply them.                                                *)
(*                                                                           *)
(* Instruction layout (same as G3; the rotating register assignment for G_i *)
(* is cur = XMM_{3 + ((i-3) mod 4)}, for G4 this gives cur=XMM3,            *)
(* MSG2_dst=XMM4, ext_dst=XMM5, MSG1_dst=XMM6):                             *)
(*   45: movdqa     xmm0, [rcx+64]  — K16..K19 load                         *)
(*   46: paddd      xmm0, xmm3      — K16..K19 + w16..w19                   *)
(*   47: sha256msg2 xmm4, xmm3      — completes w_{20..23} in XMM4          *)
(*   48: sha256rnds2 xmm2, xmm1                                             *)
(*   49: pshufd     xmm0, xmm0, 0x0e                                        *)
(*   50: movdqa     xmm7, xmm4                                              *)
(*   51: palignr    xmm7, xmm3, 4                                           *)
(*   52: nop                                                                 *)
(*   53: paddd      xmm5, xmm7      — schedule extension                     *)
(*   54: sha256msg1 xmm6, xmm3      — starts triple w_{24..27}              *)
(*   55: sha256rnds2 xmm1, xmm2                                             *)
(* ========================================================================= *)

(* Helper: prove `nested_expr = EL n W` via EL_W_ALL_LIST + WORD_RULE. *)
let PROVE_LANE_EQ_TAC : tactic =
  REWRITE_TAC EL_W_ALL_LIST THEN CONV_TAC WORD_RULE;;

(* Helper: apply two lane equations as rewrites to all assumptions, then
   restore them (UNDISCH_THEN removes them; we want to keep them). *)
let APPLY_TWO_EQS_TAC eq_tm_a eq_tm_b : tactic =
  UNDISCH_THEN eq_tm_a (fun tha ->
    UNDISCH_THEN eq_tm_b (fun thb ->
      RULE_ASSUM_TAC(REWRITE_RULE[tha; thb]) THEN
      ASSUME_TAC tha THEN ASSUME_TAC thb));;

let GROUP4_TAC : tactic =
  let WKDC_OUTER_4 = SPECL
   [`ABEF_PACK (EL 0 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])) :int128`;
    `sha_ni_rnds2
       (CDGH_PACK (EL 2 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                  (EL 3 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                  (EL 6 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                  (EL 7 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])))
       (ABEF_PACK (EL 0 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                  (EL 1 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                  (EL 4 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                  (EL 5 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])))
       (word_join4 (word_add (EL 16 sha256_K) (EL 16 W))
                   (word_add (EL 17 sha256_K) (EL 17 W))
                   (word 0) (word 0)) :int128`;
    `word_add (EL 18 sha256_K) (EL 18 W) :int32`;
    `word_add (EL 19 sha256_K) (EL 19 W) :int32`;
    `word_add (EL 16 sha256_K) (EL 16 W) :int32`;
    `word_add (EL 16 sha256_K) (EL 16 W) :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let WKDC_INNER_4 = SPECL
   [`CDGH_PACK (EL 2 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 3 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 6 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 7 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])) :int128`;
    `ABEF_PACK (EL 0 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])) :int128`;
    `word_add (EL 16 sha256_K) (EL 16 W) :int32`;
    `word_add (EL 17 sha256_K) (EL 17 W) :int32`;
    `word_add (EL 18 sha256_K) (EL 18 W) :int32`;
    `word_add (EL 19 sha256_K) (EL 19 W) :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let len_h_thm = prove
   (`LENGTH [a:int32;b;c;d;e;ff;g;h] = 8`,
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let compress_el_shift_3 =
    CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MATCH_MP
        (SPECL [`14`; `W:int32 list`; `[a:int32;b;c;d;e;ff;g;h]`]
               COMPRESS_EL_SHIFT_2)
        len_h_thm) in
  (* Phase 1 — normalize sigma1 args in XMM3 s44 lanes 2,3 by collapsing
     lanes 0,1 nested forms to `EL 16/17 W`. *)
  SUBGOAL_THEN
   `word_add (word_add (word_add w0 (sha256_sigma0 w1)) w9)
             (sha256_sigma1 w14) :int32 = EL 16 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add w1 (sha256_sigma0 w2)) w10)
             (sha256_sigma1 w15) :int32 = EL 17 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  APPLY_TWO_EQS_TAC
   `word_add (word_add (word_add w0 (sha256_sigma0 w1)) w9)
             (sha256_sigma1 w14) :int32 = EL 16 W`
   `word_add (word_add (word_add w1 (sha256_sigma0 w2)) w10)
             (sha256_sigma1 w15) :int32 = EL 17 W` THEN
  (* Phase 2 — lanes 2,3 now have canonical sigma1 args; close to EL 18/19 W. *)
  SUBGOAL_THEN
   `word_add (word_add (word_add w2 (sha256_sigma0 w3)) w11)
             (sha256_sigma1 (EL 16 W)) :int32 = EL 18 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add w3 (sha256_sigma0 w4)) w12)
             (sha256_sigma1 (EL 17 W)) :int32 = EL 19 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  APPLY_TWO_EQS_TAC
   `word_add (word_add (word_add w2 (sha256_sigma0 w3)) w11)
             (sha256_sigma1 (EL 16 W)) :int32 = EL 18 W`
   `word_add (word_add (word_add w3 (sha256_sigma0 w4)) w12)
             (sha256_sigma1 (EL 17 W)) :int32 = EL 19 W` THEN
  (* XMM3 s44 is now word_join4 (EL 16 W) (EL 17 W) (EL 18 W) (EL 19 W).
     XMM4 s44 lane 3 is word_add (w7+sigma0 w8) (EL 16 W). *)
  (* Step 45: movdqa xmm0, [rcx+64] (K16..K19) *)
  X86_STEPS_TAC HW_EXEC [45] THEN
  SUBGOAL_THEN
   `read XMM0 s45 = word_join4 (EL 16 sha256_K) (EL 17 sha256_K)
                              (EL 18 sha256_K) (EL 19 sha256_K) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 46: paddd xmm0, xmm3 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s46" THEN PADDD_REFOLD_TAC THEN
  SUBGOAL_THEN
   `read XMM0 s46 =
      word_join4 (word_add (EL 16 sha256_K) (EL 16 W))
                 (word_add (EL 17 sha256_K) (EL 17 W))
                 (word_add (EL 18 sha256_K) (EL 18 W))
                 (word_add (EL 19 sha256_K) (EL 19 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s46" THEN
  (* Step 47: sha256msg2 xmm4, xmm3.  Assert the raw sha_ni_msg2 form, apply
     SHA256MSG2_BRIDGE, then two-phase lane normalization to EL 20..23 W. *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s47" THEN
  FOLD_SHA_NI_MSG2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM4 s47 =
      sha_ni_msg2
        (word_join4 (word_add (word_add w4 (sha256_sigma0 w5)) w13)
                    (word_add (word_add w5 (sha256_sigma0 w6)) w14)
                    (word_add (word_add w6 (sha256_sigma0 w7)) w15)
                    (word_add (word_add w7 (sha256_sigma0 w8)) (EL 16 W)))
        (word_join4 (EL 16 W) (EL 17 W) (EL 18 W) (EL 19 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  UNDISCH_THEN
   `read XMM4 s47 =
      sha_ni_msg2
        (word_join4 (word_add (word_add w4 (sha256_sigma0 w5)) w13)
                    (word_add (word_add w5 (sha256_sigma0 w6)) w14)
                    (word_add (word_add w6 (sha256_sigma0 w7)) w15)
                    (word_add (word_add w7 (sha256_sigma0 w8)) (EL 16 W)))
        (word_join4 (EL 16 W) (EL 17 W) (EL 18 W) (EL 19 W))`
   (fun th ->
      ASSUME_TAC(CONV_RULE(RAND_CONV(REWR_CONV SHA256MSG2_BRIDGE THENC
                                     TOP_DEPTH_CONV let_CONV)) th)) THEN
  (* MSG2 output lanes: phase 1 (lanes 0,1 → EL 20/21 W). *)
  SUBGOAL_THEN
   `word_add (word_add (word_add w4 (sha256_sigma0 w5)) w13)
             (sha256_sigma1 (EL 18 W)) :int32 = EL 20 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add w5 (sha256_sigma0 w6)) w14)
             (sha256_sigma1 (EL 19 W)) :int32 = EL 21 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  APPLY_TWO_EQS_TAC
   `word_add (word_add (word_add w4 (sha256_sigma0 w5)) w13)
             (sha256_sigma1 (EL 18 W)) :int32 = EL 20 W`
   `word_add (word_add (word_add w5 (sha256_sigma0 w6)) w14)
             (sha256_sigma1 (EL 19 W)) :int32 = EL 21 W` THEN
  (* Phase 2 (lanes 2,3 → EL 22/23 W). *)
  SUBGOAL_THEN
   `word_add (word_add (word_add w6 (sha256_sigma0 w7)) w15)
             (sha256_sigma1 (EL 20 W)) :int32 = EL 22 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add w7 (sha256_sigma0 w8)) (EL 16 W))
             (sha256_sigma1 (EL 21 W)) :int32 = EL 23 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  APPLY_TWO_EQS_TAC
   `word_add (word_add (word_add w6 (sha256_sigma0 w7)) w15)
             (sha256_sigma1 (EL 20 W)) :int32 = EL 22 W`
   `word_add (word_add (word_add w7 (sha256_sigma0 w8)) (EL 16 W))
             (sha256_sigma1 (EL 21 W)) :int32 = EL 23 W` THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 2000))) THEN
  DISCARD_OLDSTATE_TAC "s47" THEN
  (* Shift XMM2 from ABEF_PACK (compress 14) to CDGH_PACK (compress 16). *)
  SUBGOAL_THEN
   `read XMM2 s47 = CDGH_PACK
     (EL 2 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[CDGH_EQ_ABEF] THEN
    REWRITE_TAC[compress_el_shift_3]; ALL_TAC] THEN
  UNDISCH_TAC `read XMM2 s47 = ABEF_PACK
     (EL 0 (sha256_compress 14 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 14 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 14 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 14 W [a; b; c; d; e; ff; g; h]))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* Step 48: sha256rnds2 xmm2, xmm1 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s48" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  UNDISCH_THEN
   `read XMM2 s47 = CDGH_PACK
     (EL 2 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  UNDISCH_THEN
   `read XMM1 s47 = ABEF_PACK
     (EL 0 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM2 s48 =
      sha_ni_rnds2
        (CDGH_PACK (EL 2 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 3 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 6 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 7 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])))
        (ABEF_PACK (EL 0 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])))
        (word_join4 (word_add (EL 16 sha256_K) (EL 16 W))
                    (word_add (EL 17 sha256_K) (EL 17 W))
                    (word_add (EL 18 sha256_K) (EL 18 W))
                    (word_add (EL 19 sha256_K) (EL 19 W)))
     :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s48" THEN
  (* Step 49: pshufd xmm0, xmm0, 0x0e *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s49" THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM0 s49 =
      word_join4 (word_add (EL 18 sha256_K) (EL 18 W))
                 (word_add (EL 19 sha256_K) (EL 19 W))
                 (word_add (EL 16 sha256_K) (EL 16 W))
                 (word_add (EL 16 sha256_K) (EL 16 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 50: movdqa xmm7, xmm4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s50" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBGOAL_THEN
   `read XMM7 s50 = word_join4 (EL 20 W) (EL 21 W) (EL 22 W) (EL 23 W) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s50" THEN
  (* Step 51: palignr xmm7, xmm3, 0x4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s51" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PALIGNR_4_WORD_JOIN4]) THEN
  SUBGOAL_THEN
   `read XMM7 s51 =
      word_join4 (EL 17 W) (EL 18 W) (EL 19 W) (EL 20 W) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s51" THEN
  (* Step 52: nop *)
  X86_STEPS_TAC HW_EXEC [52] THEN
  (* Step 53: paddd xmm5, xmm7.  Pre-expand XMM5 s52 from sha_ni_msg1 to a
     raw word_join4 of `w_j + sigma0 w_{j+1}` (same trick G3 uses for XMM4
     at step 41-42) so PADDD_REFOLD_TAC can plug it in.  XMM7 s52 =
     word_join4 (EL 17..20 W).  After PADDD lane j = word_add (w_j+sigma0
     w_{j+1}) (EL (j+17) W). *)
  SUBGOAL_THEN
   `read XMM5 s52 =
      word_join4 (word_add w8 (sha256_sigma0 w9))
                 (word_add w9 (sha256_sigma0 w10))
                 (word_add w10 (sha256_sigma0 w11))
                 (word_add w11 (sha256_sigma0 w12)) :int128`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SHA256MSG1_BRIDGE]; ALL_TAC] THEN
  UNDISCH_TAC
   `read XMM5 s52 = sha_ni_msg1 (word_join4 w8 w9 w10 w11)
                                (word_join4 w12 w13 w14 w15)` THEN
  DISCH_THEN(K ALL_TAC) THEN
  X86_VERBOSE_STEP_TAC HW_EXEC "s53" THEN PADDD_REFOLD_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM5 s53 =
      word_join4 (word_add (word_add w8 (sha256_sigma0 w9)) (EL 17 W))
                 (word_add (word_add w9 (sha256_sigma0 w10)) (EL 18 W))
                 (word_add (word_add w10 (sha256_sigma0 w11)) (EL 19 W))
                 (word_add (word_add w11 (sha256_sigma0 w12)) (EL 20 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM5; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s53" THEN
  (* Step 54: sha256msg1 xmm6, xmm3 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s54" THEN
  FOLD_SHA_NI_MSG1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM6 s54 =
      sha_ni_msg1 (word_join4 w12 w13 w14 w15)
                  (word_join4 (EL 16 W) (EL 17 W) (EL 18 W) (EL 19 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM6; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s54" THEN
  (* Step 55: sha256rnds2 xmm1, xmm2 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s55" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  FIRST_ASSUM(fun th ->
    let s = string_of_term (concl th) in
    if has_sub_string "XMM2 s54 =" s && has_sub_string "sha_ni_rnds2" s
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else FAIL_TAC "not found") THEN
  UNDISCH_THEN
   `read XMM1 s54 = ABEF_PACK
     (EL 0 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 16 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM1 s55 =
      sha_ni_rnds2
        (ABEF_PACK (EL 0 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])))
        (sha_ni_rnds2
           (CDGH_PACK (EL 2 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                      (EL 3 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                      (EL 6 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                      (EL 7 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])))
           (ABEF_PACK (EL 0 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                      (EL 1 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                      (EL 4 (sha256_compress 16 W [a;b;c;d;e;ff;g;h]))
                      (EL 5 (sha256_compress 16 W [a;b;c;d;e;ff;g;h])))
           (word_join4 (word_add (EL 16 sha256_K) (EL 16 W))
                       (word_add (EL 17 sha256_K) (EL 17 W))
                       (word_add (EL 18 sha256_K) (EL 18 W))
                       (word_add (EL 19 sha256_K) (EL 19 W))))
        (word_join4 (word_add (EL 18 sha256_K) (EL 18 W))
                    (word_add (EL 19 sha256_K) (EL 19 W))
                    (word_add (EL 16 sha256_K) (EL 16 W))
                    (word_add (EL 16 sha256_K) (EL 16 W))) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s55" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WKDC_INNER_4; WKDC_OUTER_4]) THEN
  CUT_POINT_TAC_HW 4 `s55:x86state`;;

(* ========================================================================= *)
(* GROUP5_TAC: symbolic execution of group 5 (steps 56-66) + CUT_POINT 5.    *)
(*                                                                           *)
(* Structurally simpler than G4 because the CUT_POINT_TAC_HW 4 output leaves *)
(* XMM3 s55 and XMM4 s55 already as clean `word_join4 (EL k W)` forms, so    *)
(* the initial Phase 1/Phase 2 normalization that G4 applied to XMM3 is not *)
(* needed.  Only the MSG2 output (step 58) still needs two-phase lane       *)
(* normalization, and step 64's PADDD still needs SHA256MSG1_BRIDGE         *)
(* pre-expansion (XMM6 is sha_ni_msg1 form at s55).                          *)
(*                                                                           *)
(* Register rotation for G5: cur=XMM4, MSG2_dst=XMM5, ext_dst=XMM6,          *)
(* MSG1_dst=XMM3.                                                            *)
(*                                                                           *)
(* Instruction layout (pc+296..pc+341, steps 56-66):                         *)
(*   56: movdqa     xmm0, [rcx+80]  — K20..K23 load                          *)
(*   57: paddd      xmm0, xmm4      — K20..K23 + w20..w23                    *)
(*   58: sha256msg2 xmm5, xmm4      — completes w_{24..27} in XMM5           *)
(*   59: sha256rnds2 xmm2, xmm1                                              *)
(*   60: pshufd     xmm0, xmm0, 0x0e                                         *)
(*   61: movdqa     xmm7, xmm5                                               *)
(*   62: palignr    xmm7, xmm4, 4                                            *)
(*   63: nop                                                                  *)
(*   64: paddd      xmm6, xmm7      — schedule extension                      *)
(*   65: sha256msg1 xmm3, xmm4      — starts triple w_{28..31}               *)
(*   66: sha256rnds2 xmm1, xmm2                                              *)
(* ========================================================================= *)

let GROUP5_TAC : tactic =
  let WKDC_OUTER_5 = SPECL
   [`ABEF_PACK (EL 0 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])) :int128`;
    `sha_ni_rnds2
       (CDGH_PACK (EL 2 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                  (EL 3 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                  (EL 6 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                  (EL 7 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])))
       (ABEF_PACK (EL 0 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                  (EL 1 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                  (EL 4 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                  (EL 5 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])))
       (word_join4 (word_add (EL 20 sha256_K) (EL 20 W))
                   (word_add (EL 21 sha256_K) (EL 21 W))
                   (word 0) (word 0)) :int128`;
    `word_add (EL 22 sha256_K) (EL 22 W) :int32`;
    `word_add (EL 23 sha256_K) (EL 23 W) :int32`;
    `word_add (EL 20 sha256_K) (EL 20 W) :int32`;
    `word_add (EL 20 sha256_K) (EL 20 W) :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let WKDC_INNER_5 = SPECL
   [`CDGH_PACK (EL 2 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 3 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 6 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 7 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])) :int128`;
    `ABEF_PACK (EL 0 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 1 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 4 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
               (EL 5 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])) :int128`;
    `word_add (EL 20 sha256_K) (EL 20 W) :int32`;
    `word_add (EL 21 sha256_K) (EL 21 W) :int32`;
    `word_add (EL 22 sha256_K) (EL 22 W) :int32`;
    `word_add (EL 23 sha256_K) (EL 23 W) :int32`;
    `word 0:int32`; `word 0:int32`]
   SHA_NI_RNDS2_WK_DONTCARE in
  let len_h_thm = prove
   (`LENGTH [a:int32;b;c;d;e;ff;g;h] = 8`,
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let compress_el_shift_4 =
    CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MATCH_MP
        (SPECL [`18`; `W:int32 list`; `[a:int32;b;c;d;e;ff;g;h]`]
               COMPRESS_EL_SHIFT_2)
        len_h_thm) in
  (* Step 56: movdqa xmm0, [rcx+80] (K20..K23) *)
  X86_STEPS_TAC HW_EXEC [56] THEN
  SUBGOAL_THEN
   `read XMM0 s56 = word_join4 (EL 20 sha256_K) (EL 21 sha256_K)
                              (EL 22 sha256_K) (EL 23 sha256_K) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 57: paddd xmm0, xmm4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s57" THEN PADDD_REFOLD_TAC THEN
  SUBGOAL_THEN
   `read XMM0 s57 =
      word_join4 (word_add (EL 20 sha256_K) (EL 20 W))
                 (word_add (EL 21 sha256_K) (EL 21 W))
                 (word_add (EL 22 sha256_K) (EL 22 W))
                 (word_add (EL 23 sha256_K) (EL 23 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s57" THEN
  (* Step 58: sha256msg2 xmm5, xmm4.  Assert the raw sha_ni_msg2 form, apply
     SHA256MSG2_BRIDGE, then two-phase lane normalization to EL 24..27 W. *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s58" THEN
  FOLD_SHA_NI_MSG2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM5 s58 =
      sha_ni_msg2
        (word_join4 (word_add (word_add w8 (sha256_sigma0 w9)) (EL 17 W))
                    (word_add (word_add w9 (sha256_sigma0 w10)) (EL 18 W))
                    (word_add (word_add w10 (sha256_sigma0 w11)) (EL 19 W))
                    (word_add (word_add w11 (sha256_sigma0 w12)) (EL 20 W)))
        (word_join4 (EL 20 W) (EL 21 W) (EL 22 W) (EL 23 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM5; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  UNDISCH_THEN
   `read XMM5 s58 =
      sha_ni_msg2
        (word_join4 (word_add (word_add w8 (sha256_sigma0 w9)) (EL 17 W))
                    (word_add (word_add w9 (sha256_sigma0 w10)) (EL 18 W))
                    (word_add (word_add w10 (sha256_sigma0 w11)) (EL 19 W))
                    (word_add (word_add w11 (sha256_sigma0 w12)) (EL 20 W)))
        (word_join4 (EL 20 W) (EL 21 W) (EL 22 W) (EL 23 W))`
   (fun th ->
      ASSUME_TAC(CONV_RULE(RAND_CONV(REWR_CONV SHA256MSG2_BRIDGE THENC
                                     TOP_DEPTH_CONV let_CONV)) th)) THEN
  (* MSG2 output lanes: phase 1 (lanes 0,1 → EL 24/25 W). *)
  SUBGOAL_THEN
   `word_add (word_add (word_add w8 (sha256_sigma0 w9)) (EL 17 W))
             (sha256_sigma1 (EL 22 W)) :int32 = EL 24 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add w9 (sha256_sigma0 w10)) (EL 18 W))
             (sha256_sigma1 (EL 23 W)) :int32 = EL 25 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  APPLY_TWO_EQS_TAC
   `word_add (word_add (word_add w8 (sha256_sigma0 w9)) (EL 17 W))
             (sha256_sigma1 (EL 22 W)) :int32 = EL 24 W`
   `word_add (word_add (word_add w9 (sha256_sigma0 w10)) (EL 18 W))
             (sha256_sigma1 (EL 23 W)) :int32 = EL 25 W` THEN
  (* Phase 2 (lanes 2,3 → EL 26/27 W). *)
  SUBGOAL_THEN
   `word_add (word_add (word_add w10 (sha256_sigma0 w11)) (EL 19 W))
             (sha256_sigma1 (EL 24 W)) :int32 = EL 26 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add w11 (sha256_sigma0 w12)) (EL 20 W))
             (sha256_sigma1 (EL 25 W)) :int32 = EL 27 W`
   ASSUME_TAC THENL [PROVE_LANE_EQ_TAC; ALL_TAC] THEN
  APPLY_TWO_EQS_TAC
   `word_add (word_add (word_add w10 (sha256_sigma0 w11)) (EL 19 W))
             (sha256_sigma1 (EL 24 W)) :int32 = EL 26 W`
   `word_add (word_add (word_add w11 (sha256_sigma0 w12)) (EL 20 W))
             (sha256_sigma1 (EL 25 W)) :int32 = EL 27 W` THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 2000))) THEN
  DISCARD_OLDSTATE_TAC "s58" THEN
  (* Shift XMM2 from ABEF_PACK (compress 18) to CDGH_PACK (compress 20). *)
  SUBGOAL_THEN
   `read XMM2 s58 = CDGH_PACK
     (EL 2 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[CDGH_EQ_ABEF] THEN
    REWRITE_TAC[compress_el_shift_4]; ALL_TAC] THEN
  UNDISCH_TAC `read XMM2 s58 = ABEF_PACK
     (EL 0 (sha256_compress 18 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 18 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 18 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 18 W [a; b; c; d; e; ff; g; h]))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* Step 59: sha256rnds2 xmm2, xmm1 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s59" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  UNDISCH_THEN
   `read XMM2 s58 = CDGH_PACK
     (EL 2 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 3 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 6 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 7 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  UNDISCH_THEN
   `read XMM1 s58 = ABEF_PACK
     (EL 0 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM2 s59 =
      sha_ni_rnds2
        (CDGH_PACK (EL 2 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 3 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 6 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 7 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])))
        (ABEF_PACK (EL 0 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])))
        (word_join4 (word_add (EL 20 sha256_K) (EL 20 W))
                    (word_add (EL 21 sha256_K) (EL 21 W))
                    (word_add (EL 22 sha256_K) (EL 22 W))
                    (word_add (EL 23 sha256_K) (EL 23 W)))
     :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s59" THEN
  (* Step 60: pshufd xmm0, xmm0, 0x0e *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s60" THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM0 s60 =
      word_join4 (word_add (EL 22 sha256_K) (EL 22 W))
                 (word_add (EL 23 sha256_K) (EL 23 W))
                 (word_add (EL 20 sha256_K) (EL 20 W))
                 (word_add (EL 20 sha256_K) (EL 20 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 61: movdqa xmm7, xmm5 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s61" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBGOAL_THEN
   `read XMM7 s61 = word_join4 (EL 24 W) (EL 25 W) (EL 26 W) (EL 27 W) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s61" THEN
  (* Step 62: palignr xmm7, xmm4, 0x4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s62" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[YMM_TO_XMM_SUBWORD]) THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PALIGNR_4_WORD_JOIN4]) THEN
  SUBGOAL_THEN
   `read XMM7 s62 =
      word_join4 (EL 21 W) (EL 22 W) (EL 23 W) (EL 24 W) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s62" THEN
  (* Step 63: nop *)
  X86_STEPS_TAC HW_EXEC [63] THEN
  (* Step 64: paddd xmm6, xmm7.  Pre-expand XMM6 s63 from sha_ni_msg1 to raw
     word_join4 via SHA256MSG1_BRIDGE (analog of G4 step 53).  XMM6 s55 =
     sha_ni_msg1 (w12..w15) (EL 16..19 W); post-bridge lane j = w_{12+j} +
     σ0 w_{13+j} (lane 3 uses σ0 (EL 16 W)).  XMM7 s63 = word_join4 (EL 21..24 W).
     After PADDD lane j = (w_{12+j}+σ0 w_{13+j}) + EL (j+21) W. *)
  SUBGOAL_THEN
   `read XMM6 s63 =
      word_join4 (word_add w12 (sha256_sigma0 w13))
                 (word_add w13 (sha256_sigma0 w14))
                 (word_add w14 (sha256_sigma0 w15))
                 (word_add w15 (sha256_sigma0 (EL 16 W))) :int128`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SHA256MSG1_BRIDGE]; ALL_TAC] THEN
  UNDISCH_TAC
   `read XMM6 s63 = sha_ni_msg1 (word_join4 w12 w13 w14 w15)
                                (word_join4 (EL 16 W) (EL 17 W) (EL 18 W) (EL 19 W))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  X86_VERBOSE_STEP_TAC HW_EXEC "s64" THEN PADDD_REFOLD_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_JOIN4_BALANCED]) THEN
  SUBGOAL_THEN
   `read XMM6 s64 =
      word_join4 (word_add (word_add w12 (sha256_sigma0 w13)) (EL 21 W))
                 (word_add (word_add w13 (sha256_sigma0 w14)) (EL 22 W))
                 (word_add (word_add w14 (sha256_sigma0 w15)) (EL 23 W))
                 (word_add (word_add w15 (sha256_sigma0 (EL 16 W))) (EL 24 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM6; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s64" THEN
  (* Step 65: sha256msg1 xmm3, xmm4 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s65" THEN
  FOLD_SHA_NI_MSG1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM3 s65 =
      sha_ni_msg1 (word_join4 (EL 16 W) (EL 17 W) (EL 18 W) (EL 19 W))
                  (word_join4 (EL 20 W) (EL 21 W) (EL 22 W) (EL 23 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM3; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s65" THEN
  (* Step 66: sha256rnds2 xmm1, xmm2 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s66" THEN
  FOLD_SHA_NI_RNDS2_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  FIRST_ASSUM(fun th ->
    let s = string_of_term (concl th) in
    if has_sub_string "XMM2 s65 =" s && has_sub_string "sha_ni_rnds2" s
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else FAIL_TAC "not found") THEN
  UNDISCH_THEN
   `read XMM1 s65 = ABEF_PACK
     (EL 0 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 1 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 4 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))
     (EL 5 (sha256_compress 20 W [a; b; c; d; e; ff; g; h]))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `read XMM1 s66 =
      sha_ni_rnds2
        (ABEF_PACK (EL 0 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 1 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 4 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                   (EL 5 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])))
        (sha_ni_rnds2
           (CDGH_PACK (EL 2 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                      (EL 3 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                      (EL 6 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                      (EL 7 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])))
           (ABEF_PACK (EL 0 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                      (EL 1 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                      (EL 4 (sha256_compress 20 W [a;b;c;d;e;ff;g;h]))
                      (EL 5 (sha256_compress 20 W [a;b;c;d;e;ff;g;h])))
           (word_join4 (word_add (EL 20 sha256_K) (EL 20 W))
                       (word_add (EL 21 sha256_K) (EL 21 W))
                       (word_add (EL 22 sha256_K) (EL 22 W))
                       (word_add (EL 23 sha256_K) (EL 23 W))))
        (word_join4 (word_add (EL 22 sha256_K) (EL 22 W))
                    (word_add (EL 23 sha256_K) (EL 23 W))
                    (word_add (EL 20 sha256_K) (EL 20 W))
                    (word_add (EL 20 sha256_K) (EL 20 W))) :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length (string_of_term (concl th)) > 1500))) THEN
  DISCARD_OLDSTATE_TAC "s66" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WKDC_INNER_5; WKDC_OUTER_5]) THEN
  CUT_POINT_TAC_HW 5 `s66:x86state`;;

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
