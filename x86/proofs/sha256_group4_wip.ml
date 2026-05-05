(* ========================================================================= *)
(* GROUP4_TAC: symbolic execution of group 4 (steps 45-55) + CUT_POINT 4.    *)
(*                                                                           *)
(* Register rotation for G_i (i>=3): cur = XMM_{3 + (i mod 4)}.              *)
(* G4: cur=XMM3, MSG2_dst=XMM4, ext_dst=XMM5, MSG1_dst=XMM6.                *)
(*                                                                           *)
(* XMM3 s44 carries nested-sigma lane values equal (mod word_add AC) to      *)
(* EL 16..19 W.  Strategy: normalize in two phases.                          *)
(*                                                                           *)
(*   Phase 1: prove lane 0,1 eqns (w16_eq, w17_eq) and rewrite so sigma1    *)
(*            args in lanes 2,3 become canonical `sigma1 (EL 16/17 W)`.     *)
(*   Phase 2: prove lane 2,3 eqns (w18_eq, w19_eq) and rewrite so lanes     *)
(*            2,3 become EL 18/19 W.                                        *)
(*                                                                           *)
(* Step 47's SHA256MSG2 output requires a similar two-phase normalization   *)
(* on XMM4: first lanes 0,1 to EL 20/21 W (so sigma1 args in 2,3 collapse), *)
(* then lanes 2,3 to EL 22/23 W.                                            *)
(* ========================================================================= *)

(* Helper: prove `nested_expr = EL n W` via EL_W_ALL_LIST + WORD_RULE. *)
let PROVE_LANE_EQ_TAC : tactic =
  REWRITE_TAC EL_W_ALL_LIST THEN CONV_TAC WORD_RULE;;

(* Helper: apply two lane equations as rewrites to all assumptions. *)
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
  (* Phase 1 — normalize sigma1 args in XMM3 s44 lanes 2,3. *)
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
  (* Phase 2 — normalize outer word_add in XMM3 s44 lanes 2,3. *)
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
  (* Step 47: sha256msg2 xmm4, xmm3.  Assert the raw sha_ni_msg2 form, then
     apply MSG2_BRIDGE, then two-phase lane normalization to EL 20..23 W. *)
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
  (* Step 53: paddd xmm5, xmm7.  XMM5 s52 = MSG1(w8..w11)(w12..w15) = word_join4
     of (w_j + sigma0 w_{j+1}).  XMM7 s52 = word_join4 (EL 17 W)..(EL 20 W).
     After PADDD, lane j = word_add (w_j+sigma0 w_{j+1}) (EL (j+17) W).
     Assert first in raw form, then convert to clean shape. *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s53" THEN PADDD_REFOLD_TAC THEN
  UNDISCH_THEN
   `read XMM5 s52 =
      sha_ni_msg1 (word_join4 w8 w9 w10 w11) (word_join4 w12 w13 w14 w15)`
   (fun th ->
      ASSUME_TAC(REWRITE_RULE[SHA256MSG1_BRIDGE] th)) THEN
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
   [REWRITE_TAC[XMM5; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s53" THEN
  (* Step 54: sha256msg1 xmm6, xmm3 *)
  X86_VERBOSE_STEP_TAC HW_EXEC "s54" THEN
  FOLD_SHA_NI_MSG1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_BOTTOM]) THEN
  REFOLD_INIT_GHOSTS_TAC THEN
  SUBSTITUTE_XMM_CLEANS_TAC THEN
  SUBGOAL_THEN
   `read XMM6 s54 =
      sha_ni_msg1 (word_join4 (EL 12 W) (EL 13 W) (EL 14 W) (EL 15 W))
                  (word_join4 (EL 16 W) (EL 17 W) (EL 18 W) (EL 19 W))
      :int128`
   ASSUME_TAC THENL
   [REWRITE_TAC[XMM6; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC EL_W_ALL_LIST THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
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
