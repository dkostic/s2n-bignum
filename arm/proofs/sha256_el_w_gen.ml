(* Generate EL n W = sigma expression for n = 0..63 *)
(* Fully reduced: all references are to w0..w15 and sha256_sigma0/sigma1 *)

let w_abbrev = ASSUME `sha256_message_schedule 48 [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W`;;
let m_list = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]`;;
let len_m = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, m_list), `16`),
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* Start with EL 0..15 W = w0..w15 *)
let el_w_acc = ref (List.map (fun k ->
  let th = SPECL [`48`; m_list; mk_small_numeral k] SHA256_SCHEDULE_PREFIX in
  let th1 = MP th (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl th)))) in
  let th2 = CONV_RULE(RAND_CONV EL_CONV) th1 in
  CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th2) (0--15));;

(* For each n = 0..47, compute EL (n+16) W *)
let () =
  for n = 0 to 47 do
    (* Step 1: EL (n+16) (schedule 48 M) = sigma formula with EL refs to schedule n M *)
    let th = SPECL [mk_small_numeral n; m_list] SHA256_W_EXTEND in
    let cond_thm = prove(lhand(concl th), REWRITE_TAC[len_m] THEN ARITH_TAC) in
    let th2 = MP th cond_thm in
    let th3 = CONV_RULE(RAND_CONV(TOP_DEPTH_CONV let_CONV)) th2 in
    let th4 = CONV_RULE(RAND_CONV(DEPTH_CONV NUM_ADD_CONV)) th3 in

    (* Step 2: For EL k (schedule n M) where k < 16: use SHA256_SCHEDULE_PREFIX *)
    let prefix_rules = List.init 16 (fun k ->
      let sth = SPECL [mk_small_numeral n; m_list; mk_small_numeral k]
        SHA256_SCHEDULE_PREFIX in
      try MP sth (EQT_ELIM(REWRITE_CONV[len_m; ARITH] (lhand(concl sth))))
      with _ -> TRUTH) in
    let th5 = REWRITE_RULE prefix_rules th4 in
    let th6 = CONV_RULE(RAND_CONV(DEPTH_CONV EL_CONV)) th5 in

    (* Step 3: For EL k (schedule n M) where k >= 16: use SHA256_SCHEDULE_MONO
       to convert to EL k (schedule 48 M), then w_abbrev to get EL k W,
       then substitute with already-computed EL_W lemma *)
    let mono_rules = List.init (min n 48) (fun i ->
      let k = i + 16 in
      if k < n + 16 then
        let sth = SPECL [mk_small_numeral n; `48`; m_list; mk_small_numeral k]
          SHA256_SCHEDULE_MONO in
        try
          let cond_thm = prove(lhand(concl sth), REWRITE_TAC[len_m] THEN ARITH_TAC) in
          let mono_th = MP sth cond_thm in
          (* mono_th: EL k (schedule 48 M) = EL k (schedule n M) *)
          (* We want the REVERSE: EL k (schedule n M) = EL k (schedule 48 M) *)
          let mono_gsym = GSYM mono_th in
          (* Now rewrite schedule 48 M -> W *)
          CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) mono_gsym
        with _ -> TRUTH
      else TRUTH) in
    let th7 = REWRITE_RULE mono_rules th6 in

    (* Step 4: Substitute EL k W for k >= 16 using already-computed lemmas *)
    let th8 = REWRITE_RULE !el_w_acc th7 in

    (* Step 5: Convert LHS from EL (n+16) (schedule 48 M) to EL (n+16) W *)
    let th9 = CONV_RULE(LAND_CONV(REWRITE_CONV[ARITH])) th8 in
    let th10 = CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th9 in

    el_w_acc := !el_w_acc @ [th10];
    if n mod 8 = 7 then
      Printf.printf "EL %d..%d W computed\n%!" (n+9) (n+16)
  done;;

let EL_W_ALL_LIST = !el_w_acc;;
let () = Printf.printf "Total EL_W lemmas: %d\n%!" (List.length EL_W_ALL_LIST);;

(* Verify: check that EL 19 W is fully reduced *)
let () =
  let t = string_of_term(rand(concl(List.nth EL_W_ALL_LIST 19))) in
  if String.length t < 200 then
    Printf.printf "EL 19 W = %s\n%!" t
  else
    Printf.printf "EL 19 W length: %d (may have unreduced refs)\n%!" (String.length t);;
