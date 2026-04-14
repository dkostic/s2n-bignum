(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 single-block compression core: 64 rounds + state add-back.        *)
(*                                                                           *)
(* Proves correctness of a straight-line ARM64 implementation that uses       *)
(* SHA256H/SHA256H2/SHA256SU0/SHA256SU1 hardware instructions for 16 round   *)
(* groups (4 rounds each = 64 total), with final state add-back.             *)
(*                                                                           *)
(* Inputs (all in registers, no memory loads for state/data):                *)
(*   Q0 = ABCD state, Q1 = EFGH state                                       *)
(*   Q4 = M[0..3], Q5 = M[4..7], Q6 = M[8..11], Q7 = M[12..15]            *)
(*         (message words, already byte-swapped to big-endian)               *)
(*   x1 = pointer to K constant table (64 x int32 = 256 bytes)              *)
(*                                                                           *)
(* Output (in registers):                                                    *)
(*   Q0 = new ABCD = compressed ABCD + initial ABCD                         *)
(*   Q1 = new EFGH = compressed EFGH + initial EFGH                         *)
(*                                                                           *)
(* The postcondition connects to sha256_block from sha256_spec.ml.           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ========================================================================= *)
(* Machine code and execution rule.                                          *)
(* ========================================================================= *)

let sha256_block_core_mc = define_from_elf "sha256_block_core_mc"
  (file_on_path !load_path "arm/sha2/sha256_block_core.o");;

let EXEC = ARM_MK_EXEC_RULE sha256_block_core_mc;;

(* ========================================================================= *)
(* Helper lemmas.                                                            *)
(* ========================================================================= *)

let ADD_SIMP_RULE = REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32];;

let SHA256_COMPRESS_ROUND_PREADD_SYM = prove(
  `!W_t K_t state. sha256_compress_round (word_add W_t K_t) (word 0:int32) state =
                   sha256_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD]);;

let SHA256H_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;;
let SHA256H2_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE;;
let SHA256SU_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256SU_BRIDGE;;

let EL_RECONSTRUCT = end_itlist CONJ (List.map (fun n ->
  prove(subst[mk_small_numeral n, `n:num`]
    `!s:int32 list. EL n [EL 0 s; EL 1 s; EL 2 s; EL 3 s;
      EL 4 s; EL 5 s; EL 6 s; EL 7 s] = EL n s`,
    GEN_TAC THEN CONV_TAC(LAND_CONV EL_CONV) THEN REFL_TAC)) (0--7));;

let SHA256_COMPRESS_ROUND_EL_LIST = prove(
 `!K W s:int32 list.
   sha256_compress_round K W [EL 0 s; EL 1 s; EL 2 s; EL 3 s;
     EL 4 s; EL 5 s; EL 6 s; EL 7 s] = sha256_compress_round K W s`,
 REPEAT GEN_TAC THEN REWRITE_TAC[sha256_compress_round] THEN
 CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[EL_RECONSTRUCT]);;

let rec SHA256_COMPRESS_UNROLL_CONV tm =
  let n_tm = rand(rator(rator tm)) in
  if n_tm = `0` then REWRITE_CONV[sha256_compress] tm
  else
    let n = dest_small_numeral n_tm in
    let arith_th = ARITH_RULE
      (mk_eq(n_tm, mk_comb(mk_comb(`(+)`, mk_small_numeral(n-1)), `1`))) in
    let step1 = ONCE_REWRITE_CONV[arith_th] tm in
    let step2 = CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[sha256_compress])) step1 in
    CONV_RULE(RAND_CONV(RAND_CONV SHA256_COMPRESS_UNROLL_CONV)) step2;;

(* ========================================================================= *)
(* Schedule lemmas.                                                          *)
(* ========================================================================= *)

let LENGTH_SHA256_MESSAGE_SCHEDULE = prove(
  `!n M:int32 list. LENGTH(sha256_message_schedule n M) = LENGTH M + n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha256_message_schedule; ADD_CLAUSES];
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha256_message_schedule;
      sha256_extend_schedule; LENGTH_APPEND; LENGTH] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let SHA256_SCHEDULE_PREFIX = prove(
  `!n M:int32 list. !k. k < LENGTH M ==>
    EL k (sha256_message_schedule n M) = EL k M`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha256_message_schedule];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha256_message_schedule;
      sha256_extend_schedule; EL_APPEND] THEN
    SUBGOAL_THEN `k < LENGTH(sha256_message_schedule n (M:int32 list))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_SHA256_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let SHA256_SCHEDULE_MONO = prove(
  `!n1 n2 M:int32 list. !k. k < LENGTH M + n1 /\ n1 <= n2 ==>
    EL k (sha256_message_schedule n2 M) = EL k (sha256_message_schedule n1 M)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `n1 <= n2:num` THENL
     [REWRITE_TAC[ARITH_RULE `SUC n2 = n2 + 1`; sha256_message_schedule;
        sha256_extend_schedule; EL_APPEND] THEN
      SUBGOAL_THEN `k < LENGTH(sha256_message_schedule n2 (M:int32 list))`
        ASSUME_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_SHA256_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `n1 = SUC n2` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; REFL_TAC]]]);;

let EL_APPEND_LENGTH = prove(
  `!l:A list. !x. EL (LENGTH l) (APPEND l [x]) = x`,
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

let SHA256_SCHEDULE_NEWEST = prove(
  `!n M:int32 list. LENGTH M = 16 ==>
    EL (n + 16) (sha256_message_schedule (n + 1) M) =
    (let W = sha256_message_schedule n M in
     word_add (sha256_sigma1 (EL (n + 14) W))
       (word_add (EL (n + 9) W)
         (word_add (sha256_sigma0 (EL (n + 1) W)) (EL n W))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha256_message_schedule; sha256_extend_schedule] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `n + 16 = LENGTH(sha256_message_schedule n (M:int32 list))`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SHA256_MESSAGE_SCHEDULE] THEN ARITH_TAC;
    REWRITE_TAC[EL_APPEND_LENGTH]]);;

let SHA256_W_EXTEND = prove(
  `!n M:int32 list. LENGTH M = 16 /\ n < 48 ==>
    EL (n + 16) (sha256_message_schedule 48 M) =
    (let W = sha256_message_schedule n M in
     word_add (sha256_sigma1 (EL (n + 14) W))
       (word_add (EL (n + 9) W)
         (word_add (sha256_sigma0 (EL (n + 1) W)) (EL n W))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL (n + 16) (sha256_message_schedule 48 (M:int32 list)) =
                EL (n + 16) (sha256_message_schedule (n + 1) M)` SUBST1_TAC THENL
   [MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SHA256_SCHEDULE_NEWEST THEN ASM_REWRITE_TAC[]]);;

let SHA256_BLOCK_EL = prove(
  `!M H:int32 list. LENGTH H = 8 ==>
    !k. k < 8 ==> EL k (sha256_block M H) =
      word_add (EL k (sha256_compress 64 (sha256_message_schedule 48 M) H))
               (EL k H)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha256_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EL_MAP2 THEN
  SUBGOAL_THEN
    `LENGTH (sha256_compress 64 (sha256_message_schedule 48 (M:int32 list))
             (H:int32 list)) = 8` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_SHA256_COMPRESS THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Per-round-group bridge lemmas (32 total: 16 SHA256H + 16 SHA256H2).       *)
(* ========================================================================= *)

let mk_group_bridge_h i =
  let base_s = mk_small_numeral(4 * i) and
      target_s = mk_small_numeral(4 * (i + 1)) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i), `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha256_compress b W H in let st = sha256_compress t W H in
      word_join4 (EL 0 st) (EL 1 st) (EL 2 st) (EL 3 st) =
      sha256h (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
              (word_join4 (EL 4 sb) (EL 5 sb) (EL 6 sb) (EL 7 sb))
              (word_join4 (word_add (EL i0 W) (EL i0 sha256_K))
                          (word_add (EL i1 W) (EL i1 sha256_K))
                          (word_add (EL i2 W) (EL i2 sha256_K))
                          (word_add (EL i3 W) (EL i3 sha256_K)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA256H_BRIDGE_FLAT] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM; EL_RECONSTRUCT] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN REFL_TAC);;

let mk_group_bridge_h2 i =
  let base_s = mk_small_numeral(4 * i) and
      target_s = mk_small_numeral(4 * (i + 1)) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i), `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha256_compress b W H in let st = sha256_compress t W H in
      word_join4 (EL 4 st) (EL 5 st) (EL 6 st) (EL 7 st) =
      sha256h2 (word_join4 (EL 4 sb) (EL 5 sb) (EL 6 sb) (EL 7 sb))
               (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
               (word_join4 (word_add (EL i0 W) (EL i0 sha256_K))
                           (word_add (EL i1 W) (EL i1 sha256_K))
                           (word_add (EL i2 W) (EL i2 sha256_K))
                           (word_add (EL i3 W) (EL i3 sha256_K)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA256H2_BRIDGE_FLAT] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM; EL_RECONSTRUCT] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN REFL_TAC);;

let GROUP_BRIDGE_H = Array.init 16 mk_group_bridge_h;;
let GROUP_BRIDGE_H2 = Array.init 16 mk_group_bridge_h2;;

(* ========================================================================= *)
(* EL n W lemmas: EL n (sha256_message_schedule 48 M) = expression.          *)
(* For n < 16: = w_n. For n >= 16: = sigma expression over w0..w15.          *)
(* ========================================================================= *)

let w_abbrev = ASSUME
  `sha256_message_schedule 48
   [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W`;;

let m_list =
  `[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]`;;

let len_m = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, m_list), `16`),
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* Build incrementally: 0..15 from prefix, 16..63 from recursive extension *)
let EL_W_ALL_LIST =
  let el_w_acc = ref (List.map (fun k ->
    let th = SPECL [`48`; m_list; mk_small_numeral k] SHA256_SCHEDULE_PREFIX in
    let th1 = MP th (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl th)))) in
    let th2 = CONV_RULE(RAND_CONV EL_CONV) th1 in
    CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th2) (0--15)) in
  for n = 0 to 47 do
    let th = SPECL [mk_small_numeral n; m_list] SHA256_W_EXTEND in
    let cond_thm = prove(lhand(concl th), REWRITE_TAC[len_m] THEN ARITH_TAC) in
    let th2 = MP th cond_thm in
    let th3 = CONV_RULE(RAND_CONV(TOP_DEPTH_CONV let_CONV)) th2 in
    let th4 = CONV_RULE(RAND_CONV(DEPTH_CONV NUM_ADD_CONV)) th3 in
    let prefix_rules = List.init 16 (fun k ->
      let sth = SPECL [mk_small_numeral n; m_list; mk_small_numeral k]
        SHA256_SCHEDULE_PREFIX in
      try MP sth (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl sth))))
      with _ -> TRUTH) in
    let th5 = REWRITE_RULE prefix_rules th4 in
    let th6 = CONV_RULE(RAND_CONV(DEPTH_CONV EL_CONV)) th5 in
    let mono_rules = List.init (min n 48) (fun i ->
      let k = i + 16 in
      if k < n + 16 then
        let sth = SPECL [mk_small_numeral n; `48`; m_list; mk_small_numeral k]
          SHA256_SCHEDULE_MONO in
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
(* Cut-point tactic: after each round group, replace Q0/Q1 with              *)
(* sha256_compress form and apply SU bridge to schedule registers.           *)
(* ========================================================================= *)

let CUT_POINT_TAC i sname =
  let target = mk_small_numeral(4 * (i + 1)) in
  let bridge_h = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int32 list`; `[a:int32;b;c;d;e;f;g;h]`] GROUP_BRIDGE_H.(i)) in
  let bridge_h2 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int32 list`; `[a:int32;b;c;d;e;f;g;h]`] GROUP_BRIDGE_H2.(i)) in
  let q0_tm = subst [sname, `s:armstate`; target, `t:num`]
    `read Q0 s = word_join4
      (EL 0 (sha256_compress t W [a;b;c;d;e;f;g;h]:int32 list))
      (EL 1 (sha256_compress t W [a;b;c;d;e;f;g;h]))
      (EL 2 (sha256_compress t W [a;b;c;d;e;f;g;h]))
      (EL 3 (sha256_compress t W [a;b;c;d;e;f;g;h]))` in
  let q1_tm = subst [sname, `s:armstate`; target, `t:num`]
    `read Q1 s = word_join4
      (EL 4 (sha256_compress t W [a;b;c;d;e;f;g;h]:int32 list))
      (EL 5 (sha256_compress t W [a;b;c;d;e;f;g;h]))
      (EL 6 (sha256_compress t W [a;b;c;d;e;f;g;h]))
      (EL 7 (sha256_compress t W [a;b;c;d;e;f;g;h]))` in
  let CUT_SUBGOAL_TAC bridge =
    ASM_REWRITE_TAC[bridge] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress)))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
    REWRITE_TAC EL_W_ALL_LIST THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN
    REFL_TAC in
  SUBGOAL_THEN q0_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h; ALL_TAC] THEN
  SUBGOAL_THEN q1_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h2; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let n = fst(dest_const t) in n = "sha256h" || n = "sha256h2"
      with _ -> false)) (concl th)))) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t ->
        try fst(dest_const t) = "sha256su1" with _ -> false)) (concl th)
    then REWRITE_RULE[SHA256SU_BRIDGE_FLAT] th
    else th);;

(* ========================================================================= *)
(* Postcondition tactic: connect sha256_compress 64 to sha256_block.         *)
(* ========================================================================= *)

let POSTCOND_TAC =
  let len_h = prove(`LENGTH [a:int32;b;c;d;e;f;g;h] = 8`,
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let m = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;
            w8;w9;w10;w11;w12;w13;w14;w15]` in
  let h = `[a:int32;b;c;d;e;f;g;h]` in
  let inst = MP (SPECL [m; h] SHA256_BLOCK_EL) len_h in
  let block_el = List.map (fun k ->
    let th = SPEC (mk_small_numeral k) inst in
    let th2 = MP th (prove(lhand(concl th), ARITH_TAC)) in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2 in
    REWRITE_RULE[w_abbrev] th3) (0--7) in
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC block_el THEN
  REFL_TAC;;

(* ========================================================================= *)
(* Correctness theorem.                                                      *)
(* ========================================================================= *)

let SHA256_BLOCK_CORE_CORRECT = prove(
 `!(a:int32) b c d (e:int32) f g h
   (w0:int32) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
   kptr pc ret_pc.
   nonoverlapping (kptr, 256) (word pc, 436)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_block_core_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X1 s = kptr /\
         read Q0 s = word_join4 a b c d /\
         read Q1 s = word_join4 e f g h /\
         read Q4 s = word_join4 w0 w1 w2 w3 /\
         read Q5 s = word_join4 w4 w5 w6 w7 /\
         read Q6 s = word_join4 w8 w9 w10 w11 /\
         read Q7 s = word_join4 w12 w13 w14 w15 /\
         (!i. i < 16 ==>
           read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
           word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                      (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)))
    (\s. read PC s = word ret_pc /\
         (let M = [w0;w1;w2;w3;w4;w5;w6;w7;
                   w8;w9;w10;w11;w12;w13;w14;w15] in
          let H = [a;b;c;d;e;f;g;h] in
          let result = sha256_block M H in
          read Q0 s = word_join4 (EL 0 result) (EL 1 result)
                                 (EL 2 result) (EL 3 result) /\
          read Q1 s = word_join4 (EL 4 result) (EL 5 result)
                                 (EL 6 result) (EL 7 result)))
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q18; Q19] ,,
     MAYCHANGE [events])`,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* Expand the K constant quantifier into 16 individual assumptions *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN

  (* Abbreviate the full message schedule *)
  ABBREV_TAC `W = sha256_message_schedule 48
    [w0:int32;w1;w2;w3;w4;w5;w6;w7;
     w8;w9;w10;w11;w12;w13;w14;w15]` THEN

  (* Steps 1-2: Save initial state *)
  ARM_STEPS_TAC EXEC (1--2) THEN

  (* ---- Round groups 0-11 (with schedule update, 7 steps each) ---- *)
  ARM_STEPS_TAC EXEC (3--9) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 0 `s9:armstate` THEN

  ARM_STEPS_TAC EXEC (10--16) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 1 `s16:armstate` THEN

  ARM_STEPS_TAC EXEC (17--23) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 2 `s23:armstate` THEN

  ARM_STEPS_TAC EXEC (24--30) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 3 `s30:armstate` THEN

  ARM_STEPS_TAC EXEC (31--37) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 4 `s37:armstate` THEN

  ARM_STEPS_TAC EXEC (38--44) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 5 `s44:armstate` THEN

  ARM_STEPS_TAC EXEC (45--51) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 6 `s51:armstate` THEN

  ARM_STEPS_TAC EXEC (52--58) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 7 `s58:armstate` THEN

  ARM_STEPS_TAC EXEC (59--65) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 8 `s65:armstate` THEN

  ARM_STEPS_TAC EXEC (66--72) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 9 `s72:armstate` THEN

  ARM_STEPS_TAC EXEC (73--79) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 10 `s79:armstate` THEN

  ARM_STEPS_TAC EXEC (80--86) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 11 `s86:armstate` THEN

  (* ---- Round groups 12-15 (no schedule update, 5 steps each) ---- *)
  ARM_STEPS_TAC EXEC (87--91) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 12 `s91:armstate` THEN

  ARM_STEPS_TAC EXEC (92--96) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 13 `s96:armstate` THEN

  ARM_STEPS_TAC EXEC (97--101) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 14 `s101:armstate` THEN

  ARM_STEPS_TAC EXEC (102--106) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 15 `s106:armstate` THEN

  (* ---- Steps 107-109: ADD state add-back + RET ---- *)
  ARM_STEPS_TAC EXEC (107--109) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* ---- Postcondition: sha256_compress 64 + add-back = sha256_block ---- *)
  POSTCOND_TAC);;
