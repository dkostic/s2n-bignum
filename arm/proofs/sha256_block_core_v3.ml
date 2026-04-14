(* SHA-256 block core v3: full proof with postcondition via reverse bridge. *)
(* Strategy: run symbolic execution without bridging (fast), then at the    *)
(* end convert the spec side (sha256_block) into sha256h/su form to match. *)

needs "arm/proofs/sha256_block_core_setup.ml";;

(* ========================================================================= *)
(* Key lemma: word_join4 of EL 0..3 of sha256_compress 4*(i+1) equals       *)
(* sha256h applied to word_join4 of sha256_compress 4*i result.             *)
(* Proved for each round group i=0..15.                                     *)
(*                                                                          *)
(* This converts the spec (sha256_compress) into hardware form (sha256h).   *)
(* ========================================================================= *)

(* For round group 0: sha256_compress 4 W H (ABCD half) = sha256h(...) *)
let SHA256_COMPRESS_AS_SHA256H_0 = prove(
 `!a b c d e f g h (w0:int32) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15.
  let W = [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] in
  let s4 = sha256_compress 4 W [a;b;c;d;e;f;g;h] in
  word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4) =
  sha256h (word_join4 a b c d) (word_join4 e f g h)
    (word_join4 (word_add w0 (EL 0 sha256_K)) (word_add w1 (EL 1 sha256_K))
                (word_add w2 (EL 2 sha256_K)) (word_add w3 (EL 3 sha256_K)))`,
 REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
 GEN_REWRITE_TAC RAND_CONV [CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE] THEN
 REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM] THEN
 CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
   (SHA256_COMPRESS_UNROLL_CONV `sha256_compress 4 W (state:int32 list)`)))) THEN
 CONV_TAC(LAND_CONV(DEPTH_CONV EL_CONV)) THEN
 REFL_TAC);;

(* Print timing *)
let () = Printf.printf "SHA256_COMPRESS_AS_SHA256H_0 proved\n%!";;
