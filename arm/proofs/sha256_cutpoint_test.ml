(* Test the cut-point approach for round group 0 *)
(* Assumes the proof state is at s9 after round group 0 *)

(* Replace sha256h/sha256h2 assumptions with sha256_compress form *)
let SHA256_CUT_POINT_TAC =
  let has_sha th =
    can (find_term (fun t ->
      try let n = fst(dest_const t) in
          n = "sha256h" || n = "sha256h2"
      with _ -> false)) (concl th) in
  fun th_q0 th_q1 ->
    RULE_ASSUM_TAC(fun asm ->
      if has_sha asm then
        if can (term_match [] `read Q0 s = x:int128`) (concl asm) then th_q0
        else if can (term_match [] `read Q1 s = x:int128`) (concl asm) then th_q1
        else asm
      else asm);;

e(SUBGOAL_THEN
  `read Q0 s9 = word_join4 (EL 0 (sha256_compress 4 W [a;b;c;d;e;f;g;h]:int32 list))
                            (EL 1 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
                            (EL 2 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
                            (EL 3 (sha256_compress 4 W [a;b;c;d;e;f;g;h])) /\
   read Q1 s9 = word_join4 (EL 4 (sha256_compress 4 W [a;b;c;d;e;f;g;h]:int32 list))
                            (EL 5 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
                            (EL 6 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
                            (EL 7 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))`
  (fun th ->
    let q0,q1 = CONJ_PAIR th in
    SHA256_CUT_POINT_TAC q0 q1 THEN ASSUME_TAC q0 THEN ASSUME_TAC q1)
THENL
 [(* Prove the cut-point assertion *)
  CONJ_TAC THENL
   [(* Q0 = sha256_compress 4 ABCD half *)
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV `sha256_compress 4 W (state:int32 list)`)))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
    GEN_REWRITE_TAC LAND_CONV
      [CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM] THEN
    REFL_TAC;
    (* Q1 = sha256_compress 4 EFGH half *)
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV `sha256_compress 4 W (state:int32 list)`)))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
    GEN_REWRITE_TAC LAND_CONV
      [CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM] THEN
    REFL_TAC];
  (* Continue with the proof *)
  ALL_TAC]);;
