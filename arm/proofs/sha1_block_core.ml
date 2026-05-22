(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-1 proof infrastructure: bridge lemma arrays, schedule extraction,     *)
(* cut-point tactics, and postcondition tactics.                             *)
(*                                                                           *)
(* This file provides reusable infrastructure for proving correctness of     *)
(* any ARM64 SHA-1 implementation that uses SHA1C/SHA1P/SHA1M/SHA1H/         *)
(* SHA1SU0/SHA1SU1 hardware instructions in the standard 4-round-group       *)
(* pattern across 80 rounds. Models on the SHA-256 HW pilot's analogous      *)
(* sha256_block_core.ml infrastructure, adapted for SHA-1's:                 *)
(*   - 5-element [a;b;c;d;e] state                                           *)
(*   - 4 ft bands (Choose/Parity/Maj/Parity, rounds 0..19/20..39/40..59/     *)
(*     60..79) keyed via sha1_compress_round_pre's ft selector               *)
(*   - 80 rounds (vs SHA-256's 64)                                           *)
(*   - sha1_block_compress with the hash spec at full schedule length        *)
(*                                                                           *)
(* Key exports:                                                              *)
(*   GROUP_BRIDGE_C.(i)     -- per-group bridge for SHA1C band (rg 0..4)     *)
(*   GROUP_BRIDGE_P_LO.(i)  -- per-group bridge for SHA1P band (rg 5..9)     *)
(*   GROUP_BRIDGE_M.(i)     -- per-group bridge for SHA1M band (rg 10..14)   *)
(*   GROUP_BRIDGE_P_HI.(i)  -- per-group bridge for SHA1P band (rg 15..19)   *)
(*   SHA1_COMPRESS_UNROLL_CONV -- unroll sha1_compress n into n round steps  *)
(*   LENGTH_SHA1_MESSAGE_SCHEDULE / SHA1_SCHEDULE_PREFIX /                   *)
(*     SHA1_SCHEDULE_MONO / SHA1_W_EXTEND -- schedule reasoning              *)
(*   LENGTH_SHA1_COMPRESS / SHA1_BLOCK_COMPRESS_EL -- block-level reasoning  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha1_bridge.ml";;

(* ========================================================================= *)
(* Helper lemmas.                                                            *)
(* ========================================================================= *)

(* Pre-flatten the bridges so let-bindings don't get in our way later. *)

let SHA1H_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA1H_BRIDGE;;
let SHA1C_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA1C_BRIDGE;;
let SHA1P_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA1P_BRIDGE;;
let SHA1M_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA1M_BRIDGE;;
let SHA1SU_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA1SU_BRIDGE;;

(* Lane-0 normalisation: SHA1{C,P,M} only inspect lane 0 of their `n`         *)
(* operand, and SHA1H only inspects lane 0 of its input. These rewrites       *)
(* canonicalise the n/d operand into `word_join4 (lane0) 0 0 0` form, which   *)
(* is what GROUP_BRIDGE_* expect. They MUST be applied with ONCE_REWRITE      *)
(* (the LHS pattern matches the inner sha1c on the RHS).                      *)

let SHA1C_LANE0_NORM = prove
 (`!d (n:int128) m. sha1c d n m =
     sha1c d (word_join4 (word_subword n (0,32):int32)
                         (word 0) (word 0) (word 0)) m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha1c; WORD_JOIN4_SUBWORD]);;

let SHA1P_LANE0_NORM = prove
 (`!d (n:int128) m. sha1p d n m =
     sha1p d (word_join4 (word_subword n (0,32):int32)
                         (word 0) (word 0) (word 0)) m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha1p; WORD_JOIN4_SUBWORD]);;

let SHA1M_LANE0_NORM = prove
 (`!d (n:int128) m. sha1m d n m =
     sha1m d (word_join4 (word_subword n (0,32):int32)
                         (word 0) (word 0) (word 0)) m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha1m; WORD_JOIN4_SUBWORD]);;

let SHA1H_LANE0_NORM = prove
 (`!(d:int128). sha1h d =
     sha1h (word_join4 (word_subword d (0,32):int32)
                       (word 0) (word 0) (word 0))`,
  GEN_TAC THEN REWRITE_TAC[sha1h; WORD_JOIN4_SUBWORD]);;

(* Pre-add-form (kw = sha1_K t + W_t) but written in the order the hardware  *)
(* produces: word_add W_t (sha1_K t) instead of word_add (sha1_K t) W_t.     *)
(* Mirrors SHA-256 pilot's SHA256_COMPRESS_ROUND_PREADD_SYM.                  *)

let SHA1_COMPRESS_ROUND_PRE_EQ_LO_SYM = prove(
  `!t (W_t:int32) state.
     t < 20
     ==> sha1_compress_round_pre 0 (word_add W_t (sha1_K t)) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  MATCH_MP_TAC SHA1_COMPRESS_ROUND_PRE_EQ_LO THEN ASM_REWRITE_TAC[]);;

let SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_LO_SYM = prove(
  `!t (W_t:int32) state.
     20 <= t /\ t < 40
     ==> sha1_compress_round_pre 1 (word_add W_t (sha1_K t)) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  MATCH_MP_TAC SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_LO THEN ASM_REWRITE_TAC[]);;

let SHA1_COMPRESS_ROUND_PRE_EQ_MAJ_SYM = prove(
  `!t (W_t:int32) state.
     40 <= t /\ t < 60
     ==> sha1_compress_round_pre 2 (word_add W_t (sha1_K t)) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  MATCH_MP_TAC SHA1_COMPRESS_ROUND_PRE_EQ_MAJ THEN ASM_REWRITE_TAC[]);;

let SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_HI_SYM = prove(
  `!t (W_t:int32) state.
     60 <= t /\ t < 80
     ==> sha1_compress_round_pre 1 (word_add W_t (sha1_K t)) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  MATCH_MP_TAC SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_HI THEN ASM_REWRITE_TAC[]);;

(* Reconstruction lemmas: given a 5-element [a;b;c;d;e] state, EL k of the   *)
(* expanded list [EL 0 s; ...; EL 4 s] is just EL k s.                       *)

let EL_RECONSTRUCT_5 = end_itlist CONJ (List.map (fun n ->
  prove(subst[mk_small_numeral n, `n:num`]
    `!s:int32 list. EL n [EL 0 s; EL 1 s; EL 2 s; EL 3 s; EL 4 s] = EL n s`,
    GEN_TAC THEN CONV_TAC(LAND_CONV EL_CONV) THEN REFL_TAC)) (0--4));;

let SHA1_COMPRESS_ROUND_EL_LIST = prove(
 `!t W (s:int32 list).
   sha1_compress_round t W [EL 0 s; EL 1 s; EL 2 s; EL 3 s; EL 4 s] =
   sha1_compress_round t W s`,
 REPEAT GEN_TAC THEN REWRITE_TAC[sha1_compress_round] THEN
 CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[EL_RECONSTRUCT_5]);;

(* After 4 more rounds (one round group), the e-lane (EL 4) is ROL_30 of the *)
(* a-lane (EL 0) of the pre-state. This is the abstract spec-level form of   *)
(* the SHA1H instruction's effect across a round group, and is used in the   *)
(* cut-point tactic to fold the SHA1H result into the canonical e-invariant. *)

let SHA1_COMPRESS_4MORE_E_EQ = prove(
  `!W (H:int32 list) k.
     EL 4 (sha1_compress (k + 4) W H) =
     word_rol (EL 0 (sha1_compress k W H)) 30`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `s0:int32 list = sha1_compress k W H` THEN
  REWRITE_TAC[ARITH_RULE
    `k + 4 = (((k + 1) + 1) + 1) + 1`] THEN
  REWRITE_TAC[sha1_compress] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[sha1_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REFL_TAC);;

(* SHA1_COMPRESS_UNROLL_CONV: given `sha1_compress n W state`, unroll into   *)
(* n nested sha1_compress_round applications via the recurrence              *)
(*    sha1_compress (k+1) W state =                                          *)
(*      sha1_compress_round k (EL k W) (sha1_compress k W state)             *)
(*    sha1_compress 0 W state = state.                                       *)

let rec SHA1_COMPRESS_UNROLL_CONV tm =
  let n_tm = rand(rator(rator tm)) in
  if n_tm = `0` then REWRITE_CONV[sha1_compress] tm
  else
    let n = dest_small_numeral n_tm in
    let arith_th = ARITH_RULE
      (mk_eq(n_tm, mk_comb(mk_comb(`(+)`, mk_small_numeral(n-1)), `1`))) in
    let step1 = ONCE_REWRITE_CONV[arith_th] tm in
    let step2 = CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[sha1_compress])) step1 in
    CONV_RULE(RAND_CONV(RAND_CONV SHA1_COMPRESS_UNROLL_CONV)) step2;;

(* ========================================================================= *)
(* Schedule lemmas.                                                          *)
(* ========================================================================= *)

let LENGTH_SHA1_MESSAGE_SCHEDULE = prove(
  `!n M:int32 list. LENGTH(sha1_message_schedule n M) = LENGTH M + n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha1_message_schedule; ADD_CLAUSES];
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha1_message_schedule;
      sha1_extend_schedule; LENGTH_APPEND; LENGTH] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let SHA1_SCHEDULE_PREFIX = prove(
  `!n M:int32 list. !k. k < LENGTH M ==>
    EL k (sha1_message_schedule n M) = EL k M`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha1_message_schedule];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha1_message_schedule;
      sha1_extend_schedule; EL_APPEND] THEN
    SUBGOAL_THEN `k < LENGTH(sha1_message_schedule n (M:int32 list))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_SHA1_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let SHA1_SCHEDULE_MONO = prove(
  `!n1 n2 M:int32 list. !k. k < LENGTH M + n1 /\ n1 <= n2 ==>
    EL k (sha1_message_schedule n2 M) = EL k (sha1_message_schedule n1 M)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `n1 <= n2:num` THENL
     [REWRITE_TAC[ARITH_RULE `SUC n2 = n2 + 1`; sha1_message_schedule;
        sha1_extend_schedule; EL_APPEND] THEN
      SUBGOAL_THEN `k < LENGTH(sha1_message_schedule n2 (M:int32 list))`
        ASSUME_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_SHA1_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `n1 = SUC n2` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; REFL_TAC]]]);;

let EL_APPEND_LENGTH = prove(
  `!l:A list. !x. EL (LENGTH l) (APPEND l [x]) = x`,
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

(* Recurrence: W_{16+n} = ROL_1 (W_{n+13} XOR W_{n+8} XOR W_{n+2} XOR W_n).  *)
let SHA1_SCHEDULE_NEWEST = prove(
  `!n M:int32 list. LENGTH M = 16 ==>
    EL (n + 16) (sha1_message_schedule (n + 1) M) =
    (let W = sha1_message_schedule n M in
     word_rol
       (word_xor (EL (n + 13) W)
          (word_xor (EL (n + 8) W)
             (word_xor (EL (n + 2) W) (EL n W))))
       1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha1_message_schedule; sha1_extend_schedule] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `n + 16 = LENGTH(sha1_message_schedule n (M:int32 list))`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SHA1_MESSAGE_SCHEDULE] THEN ARITH_TAC;
    REWRITE_TAC[EL_APPEND_LENGTH]]);;

let SHA1_W_EXTEND = prove(
  `!n M:int32 list. LENGTH M = 16 /\ n < 64 ==>
    EL (n + 16) (sha1_message_schedule 64 M) =
    (let W = sha1_message_schedule n M in
     word_rol
       (word_xor (EL (n + 13) W)
          (word_xor (EL (n + 8) W)
             (word_xor (EL (n + 2) W) (EL n W))))
       1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL (n + 16) (sha1_message_schedule 64 (M:int32 list)) =
                EL (n + 16) (sha1_message_schedule (n + 1) M)` SUBST1_TAC THENL
   [MATCH_MP_TAC SHA1_SCHEDULE_MONO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SHA1_SCHEDULE_NEWEST THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Block-level lemmas.                                                       *)
(* ========================================================================= *)

let LENGTH_SHA1_COMPRESS_ROUND = prove(
  `!t W (s:int32 list). LENGTH s >= 5 ==>
    LENGTH (sha1_compress_round t W s) = 5`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha1_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let LENGTH_SHA1_COMPRESS = prove(
  `!n W (s:int32 list). LENGTH s = 5 ==>
    LENGTH (sha1_compress n W s) = 5`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha1_compress];
    REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha1_compress] THEN
    DISCH_TAC THEN MATCH_MP_TAC LENGTH_SHA1_COMPRESS_ROUND THEN
    SUBGOAL_THEN `LENGTH (sha1_compress n W (s:int32 list)) = 5` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC]]);;

let SHA1_BLOCK_COMPRESS_EL = prove(
  `!M H:int32 list. LENGTH H = 5 ==>
    !k. k < 5 ==> EL k (sha1_block_compress M H) =
      word_add (EL k (sha1_compress 80 (sha1_message_schedule 64 M) H))
               (EL k H)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha1_block_compress; sha1_block_message_schedule] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EL_MAP2 THEN
  SUBGOAL_THEN
    `LENGTH (sha1_compress 80 (sha1_message_schedule 64 (M:int32 list))
             (H:int32 list)) = 5` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_SHA1_COMPRESS THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Per-round-group bridge lemmas (20 total: one per round group, four bands).*)
(*                                                                           *)
(* Each lemma asserts that, given a hash state H and message schedule W,     *)
(* the post-group-i first 4 lanes (= word_join4 of EL 0..3 of                *)
(* sha1_compress (4(i+1)) W H) equal the HW operator's output:               *)
(*    sha1{c,p,m} (word_join4 a₀..a₃)                                        *)
(*                (word_join4 e_lane 0 0 0)                                  *)
(*                (word_join4 (W_{4i}+K) ... (W_{4i+3}+K))                   *)
(* where (a₀..a₃) = first 4 lanes of sha1_compress (4i) W H and              *)
(* e_lane = EL 4 of sha1_compress (4i) W H.                                  *)
(* ========================================================================= *)

let mk_group_bridge_c i =
  let base_s = mk_small_numeral(4 * i) and
      target_s = mk_small_numeral(4 * (i + 1)) in
  let pre_eq_concrete = List.init 4 (fun k ->
    let t = 4*i + k in
    let th = SPECL [mk_small_numeral t; `EL_t:int32`; `state:int32 list`]
                   SHA1_COMPRESS_ROUND_PRE_EQ_LO_SYM in
    MP th (EQT_ELIM(REWRITE_CONV[ARITH] (lhand(concl th))))) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i),   `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha1_compress b W H in let st = sha1_compress t W H in
      word_join4 (EL 0 st) (EL 1 st) (EL 2 st) (EL 3 st) =
      sha1c (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
            (word_join4 (EL 4 sb) (word 0:int32) (word 0) (word 0))
            (word_join4 (word_add (sha1_K i0) (EL i0 W))
                        (word_add (sha1_K i1) (EL i1 W))
                        (word_add (sha1_K i2) (EL i2 W))
                        (word_add (sha1_K i3) (EL i3 W)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1C_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
    ONCE_REWRITE_TAC[WORD_RULE
      `word_add (K:int32) W = word_add W K`] THEN
    REWRITE_TAC pre_eq_concrete THEN
    REWRITE_TAC[SHA1_COMPRESS_ROUND_EL_LIST] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    REFL_TAC);;

let mk_group_bridge_p_lo i =
  let base_s = mk_small_numeral(4 * i) and
      target_s = mk_small_numeral(4 * (i + 1)) in
  let pre_eq_concrete = List.init 4 (fun k ->
    let t = 4*i + k in
    let th = SPECL [mk_small_numeral t; `EL_t:int32`; `state:int32 list`]
                   SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_LO_SYM in
    MP th (EQT_ELIM(REWRITE_CONV[ARITH] (lhand(concl th))))) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i),   `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha1_compress b W H in let st = sha1_compress t W H in
      word_join4 (EL 0 st) (EL 1 st) (EL 2 st) (EL 3 st) =
      sha1p (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
            (word_join4 (EL 4 sb) (word 0:int32) (word 0) (word 0))
            (word_join4 (word_add (sha1_K i0) (EL i0 W))
                        (word_add (sha1_K i1) (EL i1 W))
                        (word_add (sha1_K i2) (EL i2 W))
                        (word_add (sha1_K i3) (EL i3 W)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1P_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
    ONCE_REWRITE_TAC[WORD_RULE
      `word_add (K:int32) W = word_add W K`] THEN
    REWRITE_TAC pre_eq_concrete THEN
    REWRITE_TAC[SHA1_COMPRESS_ROUND_EL_LIST] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    REFL_TAC);;

let mk_group_bridge_m i =
  let base_s = mk_small_numeral(4 * i) and
      target_s = mk_small_numeral(4 * (i + 1)) in
  let pre_eq_concrete = List.init 4 (fun k ->
    let t = 4*i + k in
    let th = SPECL [mk_small_numeral t; `EL_t:int32`; `state:int32 list`]
                   SHA1_COMPRESS_ROUND_PRE_EQ_MAJ_SYM in
    MP th (EQT_ELIM(REWRITE_CONV[ARITH] (lhand(concl th))))) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i),   `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha1_compress b W H in let st = sha1_compress t W H in
      word_join4 (EL 0 st) (EL 1 st) (EL 2 st) (EL 3 st) =
      sha1m (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
            (word_join4 (EL 4 sb) (word 0:int32) (word 0) (word 0))
            (word_join4 (word_add (sha1_K i0) (EL i0 W))
                        (word_add (sha1_K i1) (EL i1 W))
                        (word_add (sha1_K i2) (EL i2 W))
                        (word_add (sha1_K i3) (EL i3 W)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1M_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
    ONCE_REWRITE_TAC[WORD_RULE
      `word_add (K:int32) W = word_add W K`] THEN
    REWRITE_TAC pre_eq_concrete THEN
    REWRITE_TAC[SHA1_COMPRESS_ROUND_EL_LIST] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    REFL_TAC);;

let mk_group_bridge_p_hi i =
  let base_s = mk_small_numeral(4 * i) and
      target_s = mk_small_numeral(4 * (i + 1)) in
  let pre_eq_concrete = List.init 4 (fun k ->
    let t = 4*i + k in
    let th = SPECL [mk_small_numeral t; `EL_t:int32`; `state:int32 list`]
                   SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_HI_SYM in
    MP th (EQT_ELIM(REWRITE_CONV[ARITH] (lhand(concl th))))) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i),   `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha1_compress b W H in let st = sha1_compress t W H in
      word_join4 (EL 0 st) (EL 1 st) (EL 2 st) (EL 3 st) =
      sha1p (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
            (word_join4 (EL 4 sb) (word 0:int32) (word 0) (word 0))
            (word_join4 (word_add (sha1_K i0) (EL i0 W))
                        (word_add (sha1_K i1) (EL i1 W))
                        (word_add (sha1_K i2) (EL i2 W))
                        (word_add (sha1_K i3) (EL i3 W)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1P_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
    ONCE_REWRITE_TAC[WORD_RULE
      `word_add (K:int32) W = word_add W K`] THEN
    REWRITE_TAC pre_eq_concrete THEN
    REWRITE_TAC[SHA1_COMPRESS_ROUND_EL_LIST] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA1_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha1_compress n W (state:int32 list)`))))) THEN
    REFL_TAC);;

(* The 20 round groups, by band:                                             *)
(*   rg 0..4   (rounds  0..19): SHA1C   (ft = 0, Choose)                     *)
(*   rg 5..9   (rounds 20..39): SHA1P   (ft = 1, Parity)                     *)
(*   rg 10..14 (rounds 40..59): SHA1M   (ft = 2, Maj)                        *)
(*   rg 15..19 (rounds 60..79): SHA1P   (ft = 1, Parity)                     *)

let GROUP_BRIDGE_C    = Array.init 5 mk_group_bridge_c;;
let GROUP_BRIDGE_P_LO = Array.init 5 (fun i -> mk_group_bridge_p_lo (5 + i));;
let GROUP_BRIDGE_M    = Array.init 5 (fun i -> mk_group_bridge_m (10 + i));;
let GROUP_BRIDGE_P_HI = Array.init 5 (fun i -> mk_group_bridge_p_hi (15 + i));;

(* ========================================================================= *)
(* EL n W lemmas: EL n (sha1_message_schedule 64 M) = expression.            *)
(*                                                                           *)
(* For n < 16:  RHS = w_n.                                                   *)
(* For 16 <= n < 80: RHS = ROL_1(...XOR-tree of w0..w15...), fully inlined. *)
(*                                                                           *)
(* These are conditional on the assumption                                   *)
(*   sha1_message_schedule 64 [w0;...;w15] = W                              *)
(* (the `w_abbrev` ASSUME below). They form a closed rewrite set: applying  *)
(* `REWRITE_TAC EL_W_ALL_LIST` to a goal containing `EL k W` for k in 0..79 *)
(* gives a closed expression in w0..w15.                                    *)
(* ========================================================================= *)

let w_abbrev = ASSUME
  `sha1_message_schedule 64
   [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W`;;

let m_list =
  `[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]`;;

let len_m = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, m_list), `16`),
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let EL_W_ALL_LIST =
  let el_w_acc = ref (List.map (fun k ->
    let th = SPECL [`64`; m_list; mk_small_numeral k] SHA1_SCHEDULE_PREFIX in
    let th1 = MP th (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl th)))) in
    let th2 = CONV_RULE(RAND_CONV EL_CONV) th1 in
    CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th2) (0--15)) in
  for n = 0 to 63 do
    let th = SPECL [mk_small_numeral n; m_list] SHA1_W_EXTEND in
    let cond_thm = prove(lhand(concl th), REWRITE_TAC[len_m] THEN ARITH_TAC) in
    let th2 = MP th cond_thm in
    let th3 = CONV_RULE(RAND_CONV(TOP_DEPTH_CONV let_CONV)) th2 in
    let th4 = CONV_RULE(RAND_CONV(DEPTH_CONV NUM_ADD_CONV)) th3 in
    let prefix_rules = List.init 16 (fun k ->
      let sth = SPECL [mk_small_numeral n; m_list; mk_small_numeral k]
        SHA1_SCHEDULE_PREFIX in
      try MP sth (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl sth))))
      with _ -> TRUTH) in
    let th5 = REWRITE_RULE prefix_rules th4 in
    let th6 = CONV_RULE(RAND_CONV(DEPTH_CONV EL_CONV)) th5 in
    let mono_rules = List.init (min n 64) (fun i ->
      let k = i + 16 in
      if k < n + 16 then
        let sth = SPECL [mk_small_numeral n; `64`; m_list; mk_small_numeral k]
          SHA1_SCHEDULE_MONO in
        try let cond_thm = prove(lhand(concl sth),
              REWRITE_TAC[len_m] THEN ARITH_TAC) in
            CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV w_abbrev)))
              (GSYM(MP sth cond_thm))
        with _ -> TRUTH
      else TRUTH) in
    let th7 = REWRITE_RULE mono_rules th6 in
    let th8 = REWRITE_RULE !el_w_acc th7 in
    let th9 = CONV_RULE(LAND_CONV(REWRITE_CONV[ARITH])) th8 in
    let th10 = CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th9 in
    el_w_acc := !el_w_acc @ [th10]
  done;
  !el_w_acc;;

(* ========================================================================= *)
(* GEN_CUT_POINT_TAC: at a round-group boundary (after rg i, i = 0..19),     *)
(* assert the canonical cut-point invariant:                                 *)
(*   read Q0 sname = word_join4 (EL 0 sb_t) (EL 1 sb_t)                      *)
(*                              (EL 2 sb_t) (EL 3 sb_t)                      *)
(*   read Q? sname = word_join4 (EL 4 sb_t) (word 0) (word 0) (word 0)       *)
(* where sb_t = sha1_compress (4(i+1)) W H, and Q? = Q3 if i even, Q2 if i   *)
(* odd (the SHA1H output register written during round group i).             *)
(*                                                                           *)
(* The Q0 cut is proved using the appropriate per-group bridge from          *)
(* GROUP_BRIDGE_{C,P_LO,M,P_HI}. The Q? cut uses SHA1H_BRIDGE_FLAT plus      *)
(* SHA1_COMPRESS_4MORE_E_EQ to fold ROL_30 of the previous a-lane into the   *)
(* next state's e-lane.                                                      *)
(*                                                                           *)
(* After establishing the cut form, all sha1{h,c,p,m} assumptions are        *)
(* discarded (subsumed), schedule registers carrying sha1su1 results are     *)
(* unfolded via SHA1SU_BRIDGE_FLAT, and the temporary K+W registers Q20/Q21  *)
(* are dropped.                                                              *)
(* ========================================================================= *)

(* Active e register (post round group i): Q3 if i even, Q2 if i odd. *)
let q_e_after_rg i =
  if i mod 2 = 0 then `Q3:(armstate,int128)component`
  else `Q2:(armstate,int128)component`;;

(* Pick the right per-group bridge for round group i (0..19). *)
let group_bridge_for_rg i =
  if i < 5  then GROUP_BRIDGE_C.(i)
  else if i < 10 then GROUP_BRIDGE_P_LO.(i - 5)
  else if i < 15 then GROUP_BRIDGE_M.(i - 10)
                 else GROUP_BRIDGE_P_HI.(i - 15);;

let GEN_CUT_POINT_TAC h_tm i sname =
  let target = mk_small_numeral(4 * (i + 1)) in
  let bridge = group_bridge_for_rg i in
  let bridge_inst = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int32 list`; h_tm] bridge) in
  let q_e_reg = q_e_after_rg i in
  let sb = subst [target, `t:num`; h_tm, `H:int32 list`]
            `sha1_compress t W (H:int32 list)` in
  let el k = mk_comb(mk_comb(`EL:num->int32 list->int32`,
                             mk_small_numeral k), sb) in
  let read_q0 = mk_comb(mk_comb(
    `read:(armstate,int128)component->armstate->int128`,
    `Q0:(armstate,int128)component`), sname) in
  let q0_rhs = list_mk_comb(
    `word_join4:int32->int32->int32->int32->int128`,
    [el 0; el 1; el 2; el 3]) in
  let q0_tm = mk_eq(read_q0, q0_rhs) in
  let read_q_e = mk_comb(mk_comb(
    `read:(armstate,int128)component->armstate->int128`,
    q_e_reg), sname) in
  let q_e_rhs = list_mk_comb(
    `word_join4:int32->int32->int32->int32->int128`,
    [el 4; `word 0:int32`; `word 0:int32`; `word 0:int32`]) in
  let q_e_tm = mk_eq(read_q_e, q_e_rhs) in
  let four_more_inst =
    let k = mk_small_numeral(4 * i) in
    let kn_th = ARITH_RULE(mk_eq(
      mk_comb(mk_comb(`(+):num->num->num`, k), `4`), target)) in
    REWRITE_RULE[kn_th]
      (SPECL [`W:int32 list`; h_tm; k] SHA1_COMPRESS_4MORE_E_EQ) in
  let CUT_Q0_TAC =
    ASM_REWRITE_TAC[bridge_inst] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha1_compress)))) THEN
    TRY(CONV_TAC(DEPTH_CONV EL_CONV)) THEN
    REWRITE_TAC EL_W_ALL_LIST THEN
    REWRITE_TAC[sha1_K] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REFL_TAC in
  let CUT_QE_TAC =
    ASM_REWRITE_TAC[SHA1H_BRIDGE_FLAT] THEN
    REWRITE_TAC[four_more_inst] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha1_compress)))) THEN
    TRY(CONV_TAC(DEPTH_CONV EL_CONV)) THEN
    REWRITE_TAC EL_W_ALL_LIST THEN
    REWRITE_TAC[sha1_K] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REFL_TAC in
  SUBGOAL_THEN q0_tm ASSUME_TAC THENL
   [CUT_Q0_TAC; ALL_TAC] THEN
  SUBGOAL_THEN q_e_tm ASSUME_TAC THENL
   [CUT_QE_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let nm = fst(dest_const t) in
          nm = "sha1c" || nm = "sha1p" || nm = "sha1m" || nm = "sha1h"
      with _ -> false)) (concl th)))) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t ->
        try fst(dest_const t) = "sha1su1" with _ -> false)) (concl th)
    then REWRITE_RULE[SHA1SU_BRIDGE_FLAT] th
    else th) THEN
  DISCARD_MATCHING_ASSUMPTIONS
    [`read Q20 s = x:int128`;
     `read Q21 s = x:int128`];;

(* ========================================================================= *)
(* GEN_POSTCOND_TAC: at the end of a block, fold the per-lane add-back form  *)
(*    word_add (EL k (sha1_compress 80 W H)) (EL k H)                        *)
(* into the spec form                                                        *)
(*    EL k (sha1_block_compress M H)                                         *)
(* using SHA1_BLOCK_COMPRESS_EL.                                             *)
(*                                                                           *)
(* h_tm is the term for the input hash state (e.g. `[a;b;c;d;e]`); the       *)
(* tactic discharges 5 EL k (sha1_block_compress M H) reductions.            *)
(* Caller must have established the symbolic-final state's word_add lanes    *)
(* via ASM_REWRITE_TAC just before invocation.                               *)
(* ========================================================================= *)

let GEN_POSTCOND_TAC h_tm =
  let len_h = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, h_tm), `5`),
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let m = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;
            w8;w9;w10;w11;w12;w13;w14;w15]` in
  let hw_w_abbrev = ASSUME
    `sha1_message_schedule 64
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W` in
  let inst = MP (SPECL [m; h_tm] SHA1_BLOCK_COMPRESS_EL) len_h in
  let block_el = List.map (fun k ->
    let th = SPEC (mk_small_numeral k) inst in
    let th2 = MP th (prove(lhand(concl th), ARITH_TAC)) in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2 in
    REWRITE_RULE[hw_w_abbrev] th3) (0--4) in
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC block_el THEN
  REFL_TAC;;

(* GEN_POSTCOND_TAC2: like GEN_POSTCOND_TAC but takes an external LENGTH    *)
(* proof, needed for opaque h_tm (e.g. sha1_hash_blocks output) where      *)
(* LENGTH cannot be computed by REWRITE_TAC[LENGTH] THEN ARITH_TAC.        *)

let GEN_POSTCOND_TAC2 h_tm len_h =
  let m = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;
            w8;w9;w10;w11;w12;w13;w14;w15]` in
  let hw_w_abbrev = ASSUME
    `sha1_message_schedule 64
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W` in
  let inst = MP (SPECL [m; h_tm] SHA1_BLOCK_COMPRESS_EL) len_h in
  let block_el = List.map (fun k ->
    let th = SPEC (mk_small_numeral k) inst in
    let th2 = MP th (prove(lhand(concl th), ARITH_TAC)) in
    let th3 = try CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2
              with _ -> th2 in
    REWRITE_RULE[hw_w_abbrev] th3) (0--4) in
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC block_el THEN
  REFL_TAC;;

(* Single-block convenience: h_tm = [a;b;c;d;e]. *)
let POSTCOND_TAC_HW = GEN_POSTCOND_TAC `[a:int32;b;c;d;e]`;;

(* ========================================================================= *)
(* Multi-block helper lemmas.                                                *)
(*                                                                           *)
(* These mirror sha256_block_data_order_hw_ref.ml's helper layer (Section    *)
(* "Helper lemmas for multi-block body proof"), adapted for SHA-1's          *)
(* 5-element state.                                                          *)
(* ========================================================================= *)

(* Length of iterated hash output is preserved across blocks. *)

let LENGTH_SHA1_HASH_BLOCKS = prove
 (`!n blocks H:int32 list. LENGTH H = 5
   ==> LENGTH(sha1_hash_blocks n blocks H) = 5`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha1_hash_blocks];
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha1_hash_blocks] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[sha1_block_compress; sha1_block_message_schedule] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `LENGTH (sha1_hash_blocks n blocks (H:int32 list)) = 5`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (sha1_compress 80
        (sha1_message_schedule 64 (EL n blocks:int32 list))
        (sha1_hash_blocks n blocks H:int32 list)) = 5` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_SHA1_COMPRESS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[LENGTH_MAP2]]);;

(* Common arithmetic facts used in the loop invariant. *)

let WORD_SUB_SUC = prove
 (`!n. word_sub (word(SUC n):int64) (word 1) = word n`,
  GEN_TAC THEN REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE);;

let WORD_ADVANCE_64 = WORD_RULE
 `word_add (word_add d (word(64 * ii):int64)) (word 64) =
  word_add d (word(64 * (ii + 1)))`;;

(* A list of length 16 is necessarily a 16-element CONS chain. *)

let LENGTH_16_CONS = prove
 (`!L:A list. LENGTH L = 16
   ==> ?a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15.
       L = [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15]`,
  let suc16 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC
      (SUC(SUC(SUC(SUC 0)))))))))))))))` in
  REWRITE_TAC[GSYM suc16; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_16_EL = prove
 (`!L:A list. LENGTH L = 16 ==>
    L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L; EL 4 L; EL 5 L; EL 6 L; EL 7 L;
         EL 8 L; EL 9 L; EL 10 L; EL 11 L; EL 12 L; EL 13 L; EL 14 L;
         EL 15 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_16_CONS) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* RECONSTRUCT_BLOCK_TAC: with `ALL (\bl. LENGTH bl = 16) blocks` and        *)
(* w0..w15 abbreviations in scope, derive `EL ii blocks = [w0;...;w15]`.    *)

let RECONSTRUCT_BLOCK_TAC =
  SUBGOAL_THEN
    `EL ii blocks = [w0:int32;w1;w2;w3;w4;w5;w6;w7;
                     w8;w9;w10;w11;w12;w13;w14;w15]`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC
      ["w0";"w1";"w2";"w3";"w4";"w5";"w6";"w7";
       "w8";"w9";"w10";"w11";"w12";"w13";"w14";"w15"] THEN
    MATCH_MP_TAC LIST_16_EL THEN
    UNDISCH_TAC `ALL (\bl:int32 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC];;

(* EXPAND_K_TAC: from the universal K-table assumption (j < 4 ==> ...),     *)
(* materialise four concrete K-band assumptions on Q16/Q17/Q18/Q19.        *)

let EXPAND_K_TAC =
  FIRST_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "sha1_K" with _ -> false)) (concl th)
    then
      MAP_EVERY (fun i ->
        let spec = SPEC (mk_small_numeral i) th in
        let mp = MP spec (prove(lhand(concl spec), ARITH_TAC)) in
        ASSUME_TAC(CONV_RULE
          (DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) mp))
        (0--3)
    else FAIL_TAC "");;

(* EXPAND_DATA_TAC: specialise the quantified data-memory assumption at     *)
(* j = ii. Mirrors SHA-256's, but matches on word_bytereverse.              *)

let EXPAND_DATA_TAC =
  FIRST_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl th)
    then
      MP_TAC(SPEC `ii:num` th) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]
    else FAIL_TAC "");;

(* REV32_BITBLAST_TAC: after REV32 fires on Q4/Q5/Q6/Q7, replace its         *)
(* assumption with the canonical word_join4(EL k blocks_word) form via       *)
(* bitblast (double byte-reversal cancels). Same shape as SHA-256.          *)

let REV32_BITBLAST_TAC qpat qtm =
  let is_wj4_rhs th =
    try fst(dest_const(fst(strip_comb(rand(concl th))))) = "word_join4"
    with _ -> false in
  SUBGOAL_THEN qtm
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] qpat) (concl asm) && not(is_wj4_rhs asm)
      then th else asm))
  THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN
    BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC];;
