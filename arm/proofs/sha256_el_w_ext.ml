(* Build EL n W lemmas for n = 16..63 (schedule extension words) *)

let m_list = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]`;;
let len_m = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, m_list), `16`),
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* Compute EL (n+16) (sha256_message_schedule 48 M) for each n *)
(* Step 1: Apply SHA256_W_EXTEND to get sigma formula with EL refs to schedule n M *)
(* Step 2: Reduce EL refs within schedule n M using prefix lemma + EL_CONV *)
(* Step 3: For EL refs to extended words (>= 16), use schedule monotonicity *)

(* Simple version: just prove EL 16 W = sigma expression for n=0 first *)
let EL_16_W_thm =
  let th = SPECL [`0`; m_list] SHA256_W_EXTEND in
  let cond = lhand(concl th) in
  let cond_thm = prove(cond, REWRITE_TAC[len_m] THEN ARITH_TAC) in
  let th2 = MP th cond_thm in
  let th3 = CONV_RULE(RAND_CONV(TOP_DEPTH_CONV let_CONV)) th2 in
  (* Now reduce: sha256_message_schedule 0 M = M, then EL k M = w_k *)
  let th4 = REWRITE_RULE[sha256_message_schedule] th3 in
  let th5 = CONV_RULE(RAND_CONV(DEPTH_CONV EL_CONV)) th4 in
  let th6 = CONV_RULE(LAND_CONV(REWRITE_CONV[ARITH])) th5 in
  (* Convert from schedule 48 M to W using abbreviation *)
  CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev))) th6;;

let () = Printf.printf "EL 16 W = %s\n%!"
  (String.sub (string_of_term(rand(concl EL_16_W_thm))) 0
    (min 100 (String.length(string_of_term(rand(concl EL_16_W_thm))))));;
