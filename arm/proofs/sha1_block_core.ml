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
            (word_join4 (word_add (EL i0 W) (sha1_K i0))
                        (word_add (EL i1 W) (sha1_K i1))
                        (word_add (EL i2 W) (sha1_K i2))
                        (word_add (EL i3 W) (sha1_K i3)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1C_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
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
            (word_join4 (word_add (EL i0 W) (sha1_K i0))
                        (word_add (EL i1 W) (sha1_K i1))
                        (word_add (EL i2 W) (sha1_K i2))
                        (word_add (EL i3 W) (sha1_K i3)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1P_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
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
            (word_join4 (word_add (EL i0 W) (sha1_K i0))
                        (word_add (EL i1 W) (sha1_K i1))
                        (word_add (EL i2 W) (sha1_K i2))
                        (word_add (EL i3 W) (sha1_K i3)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1M_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
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
            (word_join4 (word_add (EL i0 W) (sha1_K i0))
                        (word_add (EL i1 W) (sha1_K i1))
                        (word_add (EL i2 W) (sha1_K i2))
                        (word_add (EL i3 W) (sha1_K i3)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA1P_BRIDGE_FLAT] THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
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
