(* Test: Execute and cut-point groups 0-3 (rounds 0-15) *)
(* All W words are original message words (EL n W = w_n for n < 16) *)

(* W_EL_LEMMAS: EL n (schedule 48 M) = w_n for n < 16 *)
let W_EL_LEMMAS =
  let m_list = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]` in
  let len_m = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, m_list), `16`),
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  List.map (fun k ->
    let th = SPECL [`48`; m_list; mk_small_numeral k] SHA256_SCHEDULE_PREFIX in
    let th1 = MP th (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl th)))) in
    CONV_RULE(RAND_CONV EL_CONV) th1) (0--15);;

(* Tactic to close cut-point subgoals for groups 0-3 *)
(* Handles: sha256_compress base case, EL_CONV, W abbreviation, W_EL_LEMMAS *)
let W_MATCH_TAC_FIRST4 =
  (* Try to reduce sha256_compress 0 = H if present *)
  TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress)))) THEN
  CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
  (* Expand W abbreviation to schedule 48 M, apply W_EL_LEMMAS *)
  UNDISCH_THEN
    `sha256_message_schedule 48
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [GSYM th] THEN
               ASSUME_TAC th) THEN
  REWRITE_TAC W_EL_LEMMAS THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN
  REFL_TAC;;

(* Per-group cut-point tactic *)
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
  (* Q0 cut-point *)
  SUBGOAL_THEN q0_tm ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bridge_h] THEN W_MATCH_TAC_FIRST4; ALL_TAC] THEN
  (* Q1 cut-point *)
  SUBGOAL_THEN q1_tm ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bridge_h2] THEN W_MATCH_TAC_FIRST4; ALL_TAC] THEN
  (* Discard old sha256h/sha256h2 assumptions *)
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t ->
         try let n = fst(dest_const t) in n = "sha256h" || n = "sha256h2"
         with _ -> false)) (concl th)
    then K ALL_TAC th else NO_TAC));;

(* Run groups 0-3 *)
e(ARM_STEPS_TAC EXEC (1--9) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 0 `s9:armstate`);;

let () = Printf.printf "Group 0 cut-point done!\n%!";;

e(ARM_STEPS_TAC EXEC (10--16) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 1 `s16:armstate`);;

let () = Printf.printf "Group 1 cut-point done!\n%!";;

e(ARM_STEPS_TAC EXEC (17--23) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 2 `s23:armstate`);;

let () = Printf.printf "Group 2 cut-point done!\n%!";;

e(ARM_STEPS_TAC EXEC (24--30) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC 3 `s30:armstate`);;

let () = Printf.printf "Group 3 cut-point done!\n%!";;
