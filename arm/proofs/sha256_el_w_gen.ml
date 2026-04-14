(* Generate EL n W = sigma expression for n = 16..63 *)
(* These match the sha256su bridge outputs *)

let m_list = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]`;;
let len_m = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, m_list), `16`),
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* Accumulate EL lemmas: start with 0..15, extend one at a time *)
(* For n >= 16: EL n W = sigma1(EL(n-2) W) + EL(n-7) W + sigma0(EL(n-15) W) + EL(n-16) W *)
(* We compute this using SHA256_W_EXTEND + previous EL_W lemmas *)

let EL_W_ALL = ref (List.map (fun k ->
  let th = SPECL [`48`; m_list; mk_small_numeral k] SHA256_SCHEDULE_PREFIX in
  let th1 = MP th (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl th)))) in
  let th2 = CONV_RULE(RAND_CONV EL_CONV) th1 in
  CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th2) (0--15));;

let () =
  for n = 0 to 47 do
    let th = SPECL [mk_small_numeral n; m_list] SHA256_W_EXTEND in
    let cond_thm = prove(lhand(concl th), REWRITE_TAC[len_m] THEN ARITH_TAC) in
    let th2 = MP th cond_thm in
    let th3 = CONV_RULE(RAND_CONV(TOP_DEPTH_CONV let_CONV)) th2 in
    (* Reduce sha256_message_schedule n M: use schedule prefix to get EL k M = w_k,
       and schedule mono + earlier EL_W lemmas to get EL k (schedule n M) = EL k W *)
    let th4 = CONV_RULE(RAND_CONV(DEPTH_CONV NUM_ADD_CONV)) th3 in
    (* Replace EL k (sha256_message_schedule n M) with w_k or sigma expression *)
    (* For k < 16: SHA256_SCHEDULE_PREFIX gives EL k (schedule n M) = EL k M *)
    let schedule_prefix_rules = List.map (fun k ->
      let sth = SPECL [mk_small_numeral n; m_list; mk_small_numeral k] SHA256_SCHEDULE_PREFIX in
      try MP sth (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl sth))))
      with _ -> TRUTH) (0--15) in
    let th5 = REWRITE_RULE schedule_prefix_rules th4 in
    let th6 = CONV_RULE(RAND_CONV(DEPTH_CONV EL_CONV)) th5 in
    (* For k >= 16: use schedule mono to relate to schedule 48 M *)
    let schedule_mono_rules = List.map (fun k ->
      if k >= 16 && k < n + 16 then
        let sth = SPECL [mk_small_numeral(k-16+1); `48`; m_list; mk_small_numeral k] SHA256_SCHEDULE_MONO in
        try
          let cond = lhand(concl sth) in
          let cond_thm = prove(cond, REWRITE_TAC[len_m] THEN ARITH_TAC) in
          MP sth cond_thm
        with _ -> TRUTH
      else TRUTH) (16--(n+15)) in
    let th7 = REWRITE_RULE schedule_mono_rules th6 in
    (* Now EL k (schedule 48 M) refs remain - convert to EL k W *)
    let th8 = REWRITE_RULE (List.map (fun el_w ->
      try CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV(GSYM w_abbrev)))) el_w
      with _ -> TRUTH) !EL_W_ALL) th7 in
    let th9 = CONV_RULE(LAND_CONV(REWRITE_CONV[ARITH])) th8 in
    let th10 = CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th9 in
    EL_W_ALL := !EL_W_ALL @ [th10];
    if n mod 4 = 3 then Printf.printf "EL %d..%d W computed\n%!" (n+13) (n+16)
  done;;

let EL_W_ALL_LIST = !EL_W_ALL;;
let () = Printf.printf "Total EL_W lemmas: %d\n%!" (List.length EL_W_ALL_LIST);;
