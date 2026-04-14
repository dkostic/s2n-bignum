(* Cut-point 0: Replace Q0/Q1 with sha256_compress 4 W H *)

(* Get: EL n (sha256_message_schedule 48 M) = w_n for each n < 16 *)
let sha256_w_el n =
  let m_list = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]` in
  let th = SPECL [`48`; m_list; mk_small_numeral n] SHA256_SCHEDULE_PREFIX in
  let cond = lhand(concl th) in
  let cond_true = EQT_ELIM(REWRITE_CONV[LENGTH; ARITH] cond) in
  let th2 = MP th cond_true in
  CONV_RULE(RAND_CONV EL_CONV) th2;;

(* Now we can prove Q0 = sha256_compress 4 form.
   The key: sha256h(wj4 a b c d, wj4 e f g h, wj4(word_add w0 K0)...)
   = wj4(EL 0..3 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
   by GROUP_BRIDGE_H.(0) instantiated with W and H = [a;..;h]
   plus the fact that EL n W = w_n for n < 16 *)

(* Bridge for group 0: wj4(EL 0..3 (sha256_compress 4 W H)) = sha256h(...) *)
(* Instantiate with W and H, rewrite EL n W -> w_n *)
let W_EL_LEMMAS = List.map sha256_w_el (0--15);;

let GROUP_0_BRIDGE_INST =
  let th = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int32 list`; `[a:int32;b;c;d;e;f;g;h]`] GROUP_BRIDGE_H.(0)) in
  REWRITE_RULE W_EL_LEMMAS th;;

let () = Printf.printf "Bridge inst: %s\n%!" (String.sub (string_of_thm GROUP_0_BRIDGE_INST) 0 100);;

(* Now prove the cut-point: Q0 = wj4(EL 0..3 (sha256_compress 4 W H)) *)
e(SUBGOAL_THEN
  `read Q0 s9 = word_join4 (EL 0 (sha256_compress 4 W [a;b;c;d;e;f;g;h]:int32 list))
                            (EL 1 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
                            (EL 2 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))
                            (EL 3 (sha256_compress 4 W [a;b;c;d;e;f;g;h]))`
  ASSUME_TAC THENL
 [ASM_REWRITE_TAC[GROUP_0_BRIDGE_INST]; ALL_TAC]);;
