(* Q1 cut-point for round group 0 *)

(* Tactic to close the W-matching subgoal *)
let W_MATCH_TAC =
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress))) THEN
  CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
  UNDISCH_THEN
    `sha256_message_schedule 48
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [GSYM th] THEN
               ASSUME_TAC th) THEN
  REWRITE_TAC W_EL_LEMMAS THEN REFL_TAC;;

(* Replace Q1 sha256h2 assumption with sha256_compress form *)
e(SUBGOAL_THEN
  `read Q1 s9 = word_join4
    (EL 4 (sha256_compress 4 W [a;b;c;d;e;f;g;h]:int32 list))
    (EL 5 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
    (EL 6 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
    (EL 7 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))`
  (fun th -> RULE_ASSUM_TAC(fun asm ->
    if can (find_term (fun t ->
         try fst(dest_const t) = "sha256h2" with _ -> false)) (concl asm)
    then th else asm)) THENL
 [ASM_REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int32 list`; `[a:int32;b;c;d;e;f;g;h]`] GROUP_BRIDGE_H2.(0))] THEN
  W_MATCH_TAC;
  ALL_TAC]);;
