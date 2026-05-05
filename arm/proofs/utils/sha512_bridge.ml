(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas connecting SHA-512 algorithmic spec to ARM hardware        *)
(* instruction semantics.                                                    *)
(*                                                                           *)
(* Depends on:                                                               *)
(*   - arm/proofs/utils/sha512_spec.ml   (algorithmic spec)                  *)
(*   - arm/proofs/sha512.ml              (ARM instruction semantics)         *)
(* ========================================================================= *)

needs "arm/proofs/utils/sha512_spec.ml";;
needs "arm/proofs/sha512.ml";;

(* ========================================================================= *)
(* Phase 1: Basic LENGTH lemmas for spec constants and functions.            *)
(* ========================================================================= *)

let LENGTH_SHA512_K = prove
 (`LENGTH sha512_K = 80`,
  REWRITE_TAC[sha512_K; LENGTH] THEN ARITH_TAC);;

let LENGTH_SHA512_H0 = prove
 (`LENGTH sha512_H0 = 8`,
  REWRITE_TAC[sha512_H0; LENGTH] THEN ARITH_TAC);;

let LENGTH_SHA512_COMPRESS = prove
 (`!state W i. LENGTH state = 8 ==> LENGTH(sha512_compress i W state) = 8`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha512_compress; ADD1; sha512_compress_round] THEN
  REPEAT LET_TAC THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_SHA512_BLOCK = prove
 (`!M H. LENGTH H = 8 ==> LENGTH(sha512_block M H) = 8`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[sha512_block] THEN REPEAT LET_TAC THEN
  SUBGOAL_THEN `LENGTH (compressed:int64 list) = LENGTH (H:int64 list)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_SHA512_COMPRESS]; ASM_MESON_TAC[LENGTH_MAP2]]);;

let LENGTH_SHA512_HASH_BLOCKS = prove
 (`!n blocks H:int64 list. LENGTH H = 8
   ==> LENGTH(sha512_hash_blocks n blocks H) = 8`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha512_hash_blocks];
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha512_hash_blocks] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LENGTH_SHA512_BLOCK THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Phase 2: Packing helpers for 2-halves-per-Q convention.                   *)
(* ========================================================================= *)

(* SHA-512 packs two 64-bit state words per 128-bit Q register as            *)
(*   (word_join:int64->int64->int128) hi lo                                  *)
(* where hi lives in bits 64-127 and lo lives in bits 0-63.                  *)

let WORD_JOIN_64_HI_LO = prove
 (`!hi lo:int64.
     word_subword ((word_join:int64->int64->int128) hi lo) (0,64) = lo /\
     word_subword ((word_join:int64->int64->int128) hi lo) (64,64) = hi`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN_64_EQ = prove
 (`!(hi1:int64) (lo1:int64) (hi2:int64) (lo2:int64).
     (word_join:int64->int64->int128) hi1 lo1 =
     (word_join:int64->int64->int128) hi2 lo2 <=>
     hi1 = hi2 /\ lo1 = lo2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\x:int128. word_subword x (0,64) : int64` th) THEN
      MP_TAC(AP_TERM `\x:int128. word_subword x (64,64) : int64` th)) THEN
    REWRITE_TAC[WORD_JOIN_64_HI_LO] THEN SIMP_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Helpers to recognize the shift-by-7 / shift-by-6 patterns in sha512su0
   and sha512su1 (the ARM pseudocode uses "0:7 concat X<63:7>" style). *)

let SHA512SU0_SHIFT_LO = prove
 (`!hi lo:int64.
     (word_join:7 word->57 word->int64) (word 0)
       (word_subword ((word_join:int64->int64->int128) hi lo) (7, 57)) =
     word_ushr lo 7`,
  REPEAT GEN_TAC THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let SHA512SU0_SHIFT_HI = prove
 (`!hi lo:int64.
     (word_join:7 word->57 word->int64) (word 0)
       (word_subword ((word_join:int64->int64->int128) hi lo) (71, 57)) =
     word_ushr hi 7`,
  REPEAT GEN_TAC THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let SHA512SU1_SHIFT_LO = prove
 (`!hi lo:int64.
     (word_join:6 word->58 word->int64) (word 0)
       (word_subword ((word_join:int64->int64->int128) hi lo) (6, 58)) =
     word_ushr lo 6`,
  REPEAT GEN_TAC THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let SHA512SU1_SHIFT_HI = prove
 (`!hi lo:int64.
     (word_join:6 word->58 word->int64) (word 0)
       (word_subword ((word_join:int64->int64->int128) hi lo) (70, 58)) =
     word_ushr hi 6`,
  REPEAT GEN_TAC THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* Phase 3: Bridging lemma for SHA512H instruction (2 rounds of E/H update). *)
(*                                                                           *)
(* sha512h d n m computes the "T1" pair for two consecutive rounds of the   *)
(* SHA-512 compression function. The caller pre-adds K+W (via v += v + K+W) *)
(* and supplies it as d. n holds the packed {f,g} pair (hi=g, lo=f) and m   *)
(* holds the packed {d,e} pair (hi=e, lo=d) from the current state.         *)
(*                                                                           *)
(* Output: word_join T1_0 T1_1 where T1_0 is round-0's T1 (high half), and  *)
(* T1_1 is round-1's T1 (low half). The caller then uses these to build the *)
(* next {e', e''} pair via vector ADD v4 = v1 + output, and hands them to   *)
(* sha512h2 (bridged below) to compute the {a', a''} pair.                  *)
(* ========================================================================= *)

let SHA512H_BRIDGE = prove
 (`!a b c d e f g h kw0 kw1:int64.
    let T1_0 = word_add h
                 (word_add (sha512_Sigma1 e)
                           (word_add (sha512_Ch e f g) kw0)) in
    let e1 = word_add d T1_0 in
    let T1_1 = word_add g
                 (word_add (sha512_Sigma1 e1)
                           (word_add (sha512_Ch e1 e f) kw1)) in
    sha512h ((word_join:int64->int64->int128) (word_add h kw0) (word_add g kw1))
            ((word_join:int64->int64->int128) g f)
            ((word_join:int64->int64->int128) e d) =
    (word_join:int64->int64->int128) T1_0 T1_1`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha512h] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_JOIN_64_HI_LO; WORD_JOIN_64_EQ] THEN
  REWRITE_TAC[sha512_Ch; sha512_Sigma1] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_add (word_add (word_xor (word_and e f)
                                  (word_and (word_not e) g):int64)
                        (word_add (word_xor (word_ror e 14)
                                           (word_xor (word_ror e 18)
                                                     (word_ror e 41)))
                                  (word_add h kw0))) d =
     word_add d
      (word_add h
        (word_add (word_xor (word_ror e 14)
                           (word_xor (word_ror e 18) (word_ror e 41)))
                  (word_add (word_xor (word_and e f)
                                      (word_and (word_not e) g)) kw0)))`
    (fun th -> REWRITE_TAC[th])
  THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE]);;

(* ========================================================================= *)
(* Phase 4: Bridging lemma for SHA512H2 instruction (2 rounds of A update). *)
(*                                                                           *)
(* sha512h2 d n m computes the new {a', a''} pair for two consecutive       *)
(* rounds. d holds the output of sha512h (word_join T1_0 T1_1).             *)
(* n holds {b,c} pair (hi=c, lo=b ... wait see pseudocode convention).      *)
(*                                                                           *)
(* Exact input layout matches aws-lc's `sha512h2 v3, v1, v0` call:           *)
(*   d_arg = word_join T1_0 T1_1  (from preceding sha512h)                  *)
(*   n = word_join d c            (the old state's {c,d} Q register)        *)
(*   m = word_join b a            (the old state's {a,b} Q register)        *)
(*                                                                           *)
(* Output: word_join (T1_0 + T2_0) (T1_1 + T2_1) where T2_0, T2_1 are the   *)
(* Sigma0+Maj terms for rounds 0, 1 respectively. This is the new {b', a'}  *)
(* Q register layout after 2 rounds.                                         *)
(* ========================================================================= *)

let SHA512H2_BRIDGE = prove
 (`!a b c d:int64 T1_0 T1_1.
    let T2_0 = word_add (sha512_Sigma0 a) (sha512_Maj a b c) in
    let a2_0 = word_add T1_0 T2_0 in
    let T2_1 = word_add (sha512_Sigma0 a2_0) (sha512_Maj a2_0 a b) in
    let a2_1 = word_add T1_1 T2_1 in
    sha512h2 ((word_join:int64->int64->int128) T1_0 T1_1)
             ((word_join:int64->int64->int128) d c)
             ((word_join:int64->int64->int128) b a) =
    (word_join:int64->int64->int128) a2_0 a2_1`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha512h2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_JOIN_64_HI_LO; WORD_JOIN_64_EQ] THEN
  REWRITE_TAC[sha512_Maj; sha512_Sigma0] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
      `word_xor (word_and c b:int64)
                (word_xor (word_and c a) (word_and b a)) =
       word_xor (word_and a b)
                (word_xor (word_and a c) (word_and b c))`
      (fun th -> REWRITE_TAC[th])
    THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];
    SUBGOAL_THEN
      `word_add (word_xor (word_and c b:int64)
                          (word_xor (word_and c a) (word_and b a)))
                (word_add (word_xor (word_ror a 28)
                                    (word_xor (word_ror a 34) (word_ror a 39)))
                          T1_0) =
       word_add T1_0
        (word_add (word_xor (word_ror a 28)
                            (word_xor (word_ror a 34) (word_ror a 39)))
                  (word_xor (word_and a b)
                            (word_xor (word_and a c) (word_and b c))))`
      (fun th -> REWRITE_TAC[th])
    THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ONCE_REWRITE_TAC[WORD_RULE `(word_and b a:int64) = word_and a b`] THEN
    CONV_TAC WORD_RULE]);;

(* ========================================================================= *)
(* Phase 5: Bridging lemma for SHA512SU0 + SHA512SU1 (2 schedule words).    *)
(*                                                                           *)
(* Given packed schedule state:                                              *)
(*   {w0, w1}, {w2, w3}, ... {w14, w15} (16 words as 8 pairs)               *)
(*   and {w8, w9}, {w10, w11} for the wi+9, wi+10 reference                 *)
(* The sha512su0(v_01, v_23) followed by sha512su1(su0_result, v_14_15,     *)
(* v_9_10) produces the packed next-pair {w16, w17}.                         *)
(*                                                                           *)
(* w16 = sigma1(w14) + w9  + sigma0(w1) + w0                                 *)
(* w17 = sigma1(w15) + w10 + sigma0(w2) + w1                                 *)
(* ========================================================================= *)

let SHA512SU_BRIDGE = prove
 (`!w0 w1 w2 w3 w9 w10 w14 w15:int64.
    let w16 = word_add (sha512_sigma1 w14)
                (word_add w9 (word_add (sha512_sigma0 w1) w0)) in
    let w17 = word_add (sha512_sigma1 w15)
                (word_add w10 (word_add (sha512_sigma0 w2) w1)) in
    sha512su1 (sha512su0 ((word_join:int64->int64->int128) w1 w0)
                         ((word_join:int64->int64->int128) w3 w2))
              ((word_join:int64->int64->int128) w15 w14)
              ((word_join:int64->int64->int128) w10 w9) =
    (word_join:int64->int64->int128) w17 w16`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha512su0; sha512su1] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_JOIN_64_HI_LO; WORD_JOIN_64_EQ] THEN
  REWRITE_TAC[SHA512SU0_SHIFT_LO; SHA512SU0_SHIFT_HI;
              SHA512SU1_SHIFT_LO; SHA512SU1_SHIFT_HI] THEN
  REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
  CONJ_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* Helper: flatten the let bindings to expose the sha512_compress_round      *)
(* form for use as a rewrite rule in proofs.                                 *)
(* ========================================================================= *)

let SHA512H_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA512H_BRIDGE;;
let SHA512H2_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA512H2_BRIDGE;;
let SHA512SU_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA512SU_BRIDGE;;

(* ========================================================================= *)
(* Commutativity of word_add for pre-add reordering.                         *)
(* The hardware computes ADD V.2D which produces one order of K+W, but the  *)
(* spec's sha512_compress_round takes K_t, W_t separately. These let us     *)
(* rewrite between forms.                                                    *)
(* ========================================================================= *)

let SHA512_COMPRESS_ROUND_PREADD = prove
 (`!(K_t:int64) (W_t:int64) state.
     sha512_compress_round (word_add K_t W_t) (word 0) state =
     sha512_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha512_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REFL_TAC);;

let SHA512_COMPRESS_ROUND_KW_SYM = prove
 (`!(K_t:int64) (W_t:int64) state.
     sha512_compress_round K_t W_t state =
     sha512_compress_round W_t K_t state`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha512_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `word_add (W_t:int64) K_t = word_add K_t W_t`
    SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; REFL_TAC]);;

let SHA512_COMPRESS_ROUND_PREADD_SYM = prove
 (`!(W_t:int64) (K_t:int64) state.
     sha512_compress_round (word_add W_t K_t) (word 0) state =
     sha512_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int64) K = word_add K W`] THEN
  REWRITE_TAC[SHA512_COMPRESS_ROUND_PREADD]);;

(* ========================================================================= *)
(* Phase 6: Helper for the EXT #8 lane-rearrangement pattern used by the     *)
(* SHA-512 hw core. Given a 128+128 concatenation of two word_join packs,   *)
(* extracting bits [64..192] yields the "middle two" 64-bit halves.         *)
(* ========================================================================= *)

let WORD_JOIN_MID64 = prove
 (`!(hi:int64) (mid1:int64) (mid2:int64) (lo:int64).
     word_subword ((word_join:int128->int128->256 word)
                    ((word_join:int64->int64->int128) hi mid1)
                    ((word_join:int64->int64->int128) mid2 lo))
                  (64,128) : int128 =
     (word_join:int64->int64->int128) mid1 mid2`,
  REPEAT GEN_TAC THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* Phase 7: Schedule preservation/monotonicity/extension and block-EL       *)
(* lemmas; exact SHA-256 analogues with :int32 -> :int64 and 48 -> 64.       *)
(* ========================================================================= *)

let LENGTH_SHA512_MESSAGE_SCHEDULE = prove
 (`!n M:int64 list. LENGTH(sha512_message_schedule n M) = LENGTH M + n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha512_message_schedule; ADD_CLAUSES];
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha512_message_schedule;
      sha512_extend_schedule; LENGTH_APPEND; LENGTH] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let SHA512_SCHEDULE_PREFIX = prove
 (`!n M:int64 list. !k. k < LENGTH M ==>
    EL k (sha512_message_schedule n M) = EL k M`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha512_message_schedule];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha512_message_schedule;
      sha512_extend_schedule; EL_APPEND] THEN
    SUBGOAL_THEN `k < LENGTH(sha512_message_schedule n (M:int64 list))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_SHA512_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let SHA512_SCHEDULE_MONO = prove
 (`!n1 n2 M:int64 list. !k. k < LENGTH M + n1 /\ n1 <= n2 ==>
    EL k (sha512_message_schedule n2 M) = EL k (sha512_message_schedule n1 M)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `n1 <= n2:num` THENL
     [REWRITE_TAC[ARITH_RULE `SUC n2 = n2 + 1`; sha512_message_schedule;
        sha512_extend_schedule; EL_APPEND] THEN
      SUBGOAL_THEN `k < LENGTH(sha512_message_schedule n2 (M:int64 list))`
        ASSUME_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_SHA512_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `n1 = SUC n2` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; REFL_TAC]]]);;

let EL_APPEND_LENGTH = prove
 (`!l:A list. !x. EL (LENGTH l) (APPEND l [x]) = x`,
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

let SHA512_SCHEDULE_NEWEST = prove
 (`!n M:int64 list. LENGTH M = 16 ==>
    EL (n + 16) (sha512_message_schedule (n + 1) M) =
    (let W = sha512_message_schedule n M in
     word_add (sha512_sigma1 (EL (n + 14) W))
       (word_add (EL (n + 9) W)
         (word_add (sha512_sigma0 (EL (n + 1) W)) (EL n W))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha512_message_schedule; sha512_extend_schedule] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `n + 16 = LENGTH(sha512_message_schedule n (M:int64 list))`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SHA512_MESSAGE_SCHEDULE] THEN ARITH_TAC;
    REWRITE_TAC[EL_APPEND_LENGTH]]);;

let SHA512_W_EXTEND = prove
 (`!n M:int64 list. LENGTH M = 16 /\ n < 64 ==>
    EL (n + 16) (sha512_message_schedule 64 M) =
    (let W = sha512_message_schedule n M in
     word_add (sha512_sigma1 (EL (n + 14) W))
       (word_add (EL (n + 9) W)
         (word_add (sha512_sigma0 (EL (n + 1) W)) (EL n W))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL (n + 16) (sha512_message_schedule 64 (M:int64 list)) =
                EL (n + 16) (sha512_message_schedule (n + 1) M)` SUBST1_TAC THENL
   [MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SHA512_SCHEDULE_NEWEST THEN ASM_REWRITE_TAC[]]);;

let SHA512_BLOCK_EL = prove
 (`!M H:int64 list. LENGTH H = 8 ==>
    !k. k < 8 ==> EL k (sha512_block M H) =
      word_add (EL k (sha512_compress 80 (sha512_message_schedule 64 M) H))
               (EL k H)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha512_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EL_MAP2 THEN
  SUBGOAL_THEN
    `LENGTH (sha512_compress 80 (sha512_message_schedule 64 (M:int64 list))
             (H:int64 list)) = 8` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_SHA512_COMPRESS THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;
