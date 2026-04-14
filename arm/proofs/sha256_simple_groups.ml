(* Round groups for sha256_block_simple: same as sha256_groups_0_3.ml
   but using SIMPLE_EXEC and step offset +11 *)

(* Redefine CUT_POINT_TAC for the simple version *)
let SIMPLE_CUT_POINT_TAC i sname =
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

(* All 16 round groups with offset step numbers *)
(* Core steps 3-9 = simple steps 14-20, etc. Offset = +11 *)
e(ARM_STEPS_TAC SIMPLE_EXEC (14--20) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 0 `s20:armstate`);;
let () = Printf.printf "Group 0 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (21--27) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 1 `s27:armstate`);;
let () = Printf.printf "Group 1 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (28--34) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 2 `s34:armstate`);;
let () = Printf.printf "Group 2 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (35--41) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 3 `s41:armstate`);;
let () = Printf.printf "Group 3 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (42--48) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 4 `s48:armstate`);;
let () = Printf.printf "Group 4 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (49--55) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 5 `s55:armstate`);;
let () = Printf.printf "Group 5 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (56--62) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 6 `s62:armstate`);;
let () = Printf.printf "Group 6 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (63--69) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 7 `s69:armstate`);;
let () = Printf.printf "Group 7 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (70--76) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 8 `s76:armstate`);;
let () = Printf.printf "Group 8 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (77--83) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 9 `s83:armstate`);;
let () = Printf.printf "Group 9 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (84--90) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 10 `s90:armstate`);;
let () = Printf.printf "Group 10 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (91--97) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 11 `s97:armstate`);;
let () = Printf.printf "Group 11 done!\n%!";;

(* Groups 12-15: no schedule update, 5 steps each *)
e(ARM_STEPS_TAC SIMPLE_EXEC (98--102) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 12 `s102:armstate`);;
let () = Printf.printf "Group 12 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (103--107) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 13 `s107:armstate`);;
let () = Printf.printf "Group 13 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (108--112) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 14 `s112:armstate`);;
let () = Printf.printf "Group 14 done!\n%!";;

e(ARM_STEPS_TAC SIMPLE_EXEC (113--117) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SIMPLE_CUT_POINT_TAC 15 `s117:armstate`);;
let () = Printf.printf "Group 15 done!\n%!";;

(* Add-back + stores + RET: steps 118-122 *)
e(ARM_STEPS_TAC SIMPLE_EXEC (118--122) THEN RULE_ASSUM_TAC ADD_SIMP_RULE);;
let () = Printf.printf "Add-back + stores + RET done!\n%!";;

(* ENSURES_FINAL_STATE_TAC *)
e(ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
let () = Printf.printf "ENSURES_FINAL_STATE_TAC done!\n%!";;

(* Postcondition matching *)
e(POSTCOND_TAC);;
let () = Printf.printf "*** sha256_block_simple PROOF COMPLETE! ***\n%!";;
