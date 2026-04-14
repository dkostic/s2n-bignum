(* Groups 2-4: test schedule bridge for group 4 *)

let w_abbrev = ASSUME `sha256_message_schedule 48 [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W`;;
let EL_W_LEMMAS_W = List.map (fun k ->
  CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) (List.nth W_EL_LEMMAS k)) (0--15);;

let SHA256SU_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256SU_BRIDGE;;

let CUT_AND_SU_TAC i sname =
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
   [ASM_REWRITE_TAC[bridge_h] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress)))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
    REWRITE_TAC EL_W_LEMMAS_W THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN
    REFL_TAC; ALL_TAC] THEN
  (* Q1 cut-point *)
  SUBGOAL_THEN q1_tm ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bridge_h2] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress)))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
    REWRITE_TAC EL_W_LEMMAS_W THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN
    REFL_TAC; ALL_TAC] THEN
  (* Discard old sha256h/sha256h2 assumptions *)
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let n = fst(dest_const t) in n = "sha256h" || n = "sha256h2"
      with _ -> false)) (concl th)))) THEN
  (* Apply SU bridge to schedule registers *)
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t ->
        try fst(dest_const t) = "sha256su1" with _ -> false)) (concl th)
    then REWRITE_RULE[SHA256SU_BRIDGE_FLAT] th
    else th);;

(* Group 2 *)
e(ARM_STEPS_TAC EXEC (17--23) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_AND_SU_TAC 2 `s23:armstate`);;
let () = Printf.printf "Group 2 done!\n%!";;

(* Group 3 *)
e(ARM_STEPS_TAC EXEC (24--30) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_AND_SU_TAC 3 `s30:armstate`);;
let () = Printf.printf "Group 3 done!\n%!";;

(* Group 4 - first group needing schedule extension! *)
e(ARM_STEPS_TAC EXEC (31--37) THEN RULE_ASSUM_TAC ADD_SIMP_RULE);;
let () = Printf.printf "Group 4 steps done, attempting cut-point...\n%!";;
e(CUT_AND_SU_TAC 4 `s37:armstate`);;
let () = Printf.printf "Group 4 DONE!\n%!";;
