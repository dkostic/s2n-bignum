(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas connecting SHA-256 algorithmic spec to ARM hardware        *)
(* instruction semantics.                                                    *)
(*                                                                           *)
(* Depends on:                                                               *)
(*   - arm/proofs/utils/sha256_spec.ml   (algorithmic spec)                  *)
(*   - arm/proofs/sha256.ml              (ARM instruction semantics)         *)
(* ========================================================================= *)

needs "arm/proofs/utils/sha256_spec.ml";;
needs "arm/proofs/sha256.ml";;

(* ========================================================================= *)
(* Phase 1: Basic properties and equivalence lemmas.                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* LENGTH lemmas for spec constants and functions.                           *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA256_K = prove
 (`LENGTH sha256_K = 64`,
  REWRITE_TAC[sha256_K; LENGTH] THEN ARITH_TAC);;

let LENGTH_SHA256_H0 = prove
 (`LENGTH sha256_H0 = 8`,
  REWRITE_TAC[sha256_H0; LENGTH] THEN ARITH_TAC);;

let LENGTH_SHA256_COMPRESS = prove
 (`!state W i. LENGTH state = 8 ==> LENGTH(sha256_compress i W state) = 8`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha256_compress; ADD1; sha256_compress_round] THEN
  REPEAT LET_TAC THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_SHA256_BLOCK = prove
 (`!M H. LENGTH H = 8 ==> LENGTH(sha256_block M H) = 8`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[sha256_block] THEN REPEAT LET_TAC THEN
  SUBGOAL_THEN `LENGTH (compressed:int32 list) = LENGTH (H:int32 list)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_SHA256_COMPRESS]; ASM_MESON_TAC[LENGTH_MAP2]]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence of spec logical functions with instruction-level definitions. *)
(* ------------------------------------------------------------------------- *)

let SHA256_CH_EQ_CHOOSE = prove
 (`!x y z. sha256_Ch x y z = sha_choose x y z`,
  REWRITE_TAC[sha256_Ch; sha_choose] THEN CONV_TAC WORD_RULE);;

let SHA256_MAJ_EQ_MAJ = prove
 (`!x y z. sha256_Maj x y z = sha_maj x y z`,
  REWRITE_TAC[sha256_Maj; sha_maj] THEN CONV_TAC WORD_RULE);;

let SHA256_SIGMA0_EQ = prove
 (`!x. sha256_Sigma0 x = sha_hash_sigma_0 x`,
  REWRITE_TAC[sha256_Sigma0; sha_hash_sigma_0]);;

let SHA256_SIGMA1_EQ = prove
 (`!x. sha256_Sigma1 x = sha_hash_sigma_1 x`,
  REWRITE_TAC[sha256_Sigma1; sha_hash_sigma_1]);;

(* ========================================================================= *)
(* Phase 2: Bridging lemmas for SHA256H instruction.                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Packing helper: pack four 32-bit words into one 128-bit word.             *)
(* word_join4 a b c d packs a at bits 0-31, b at 32-63, c at 64-95,         *)
(* d at 96-127.                                                              *)
(* ------------------------------------------------------------------------- *)

let word_join4 = new_definition
 `word_join4 (a:int32) (b:int32) (c:int32) (d:int32) : int128 =
    (word_join:int32->96 word->int128) d
      ((word_join:int32->64 word->96 word) c
        ((word_join:int32->int32->64 word) b a))`;;

(* ------------------------------------------------------------------------- *)
(* Packing/unpacking lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN4_SUBWORD = prove
 (`!a b c d:int32.
     word_subword (word_join4 a b c d : int128) (0,32) = a /\
     word_subword (word_join4 a b c d : int128) (32,32) = b /\
     word_subword (word_join4 a b c d : int128) (64,32) = c /\
     word_subword (word_join4 a b c d : int128) (96,32) = d`,
  REWRITE_TAC[word_join4] THEN REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN4_SUBWORD_ALT = REWRITE_RULE[word_join4] WORD_JOIN4_SUBWORD;;

let WORD_JOIN4_EQ = prove
 (`!a1 b1 c1 d1 a2 b2 c2 d2:int32.
     word_join4 a1 b1 c1 d1 = word_join4 a2 b2 c2 d2 <=>
     a1 = a2 /\ b1 = b2 /\ c1 = c2 /\ d1 = d2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\x:int128. word_subword x (0,32) : int32` th) THEN
      MP_TAC(AP_TERM `\x:int128. word_subword x (32,32) : int32` th) THEN
      MP_TAC(AP_TERM `\x:int128. word_subword x (64,32) : int32` th) THEN
      MP_TAC(AP_TERM `\x:int128. word_subword x (96,32) : int32` th)) THEN
    REWRITE_TAC[WORD_JOIN4_SUBWORD_ALT] THEN SIMP_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for cross-width word operations in SHA256 hash loop.        *)
(* These eliminate word_subword/word_rol on 256/128/96-bit intermediates.    *)
(* ------------------------------------------------------------------------- *)

let SHA256_ROT_HIGH = prove
 (`!x y:int128.
     word_subword (word_rol ((word_join:int128->int128->256 word) x y) 32
                   : 256 word) (128, 128)
     = (word_join:96 word->int32->int128)
         (word_subword x (0, 96)) (word_subword y (96, 32))`,
  REPEAT GEN_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let SHA256_ROT_LOW = prove
 (`!x y:int128.
     word_subword (word_rol ((word_join:int128->int128->256 word) x y) 32
                   : 256 word) (0, 128)
     = (word_join:96 word->int32->int128)
         (word_subword y (0, 96)) (word_subword x (96, 32))`,
  REPEAT GEN_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN_SUBWORD_32_96 = prove
 (`!(h:int32) (l:96 word).
     word_subword ((word_join:int32->96 word->int128) h l) (96,32) = h /\
     word_subword ((word_join:int32->96 word->int128) h l) (0,96) = l`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN_96_32_SUBWORDS = prove
 (`!(h:96 word) (l:int32).
     word_subword ((word_join:96 word->int32->int128) h l) (0,32) = l /\
     word_subword ((word_join:96 word->int32->int128) h l) (32,32)
       = (word_subword h (0,32) : int32) /\
     word_subword ((word_join:96 word->int32->int128) h l) (64,32)
       = (word_subword h (32,32) : int32) /\
     word_subword ((word_join:96 word->int32->int128) h l) (96,32)
       = (word_subword h (64,32) : int32)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN_96_SUBWORDS = prove
 (`!(c:int32) (b:int32) (a:int32).
     word_subword ((word_join:int32->64 word->96 word) c
       ((word_join:int32->int32->64 word) b a)) (0,32) = a /\
     word_subword ((word_join:int32->64 word->96 word) c
       ((word_join:int32->int32->64 word) b a)) (32,32) = b /\
     word_subword ((word_join:int32->64 word->96 word) c
       ((word_join:int32->int32->64 word) b a)) (64,32) = c`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN_REASSOC = prove
 (`!a b c t:int32.
     (word_join:96 word->int32->int128)
       ((word_join:int32->64 word->96 word) c
         ((word_join:int32->int32->64 word) b a)) t =
     (word_join:int32->96 word->int128) c
       ((word_join:int32->64 word->96 word) b
         ((word_join:int32->int32->64 word) a t))`,
  REPEAT GEN_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Single-round step lemmas: extracting 128-bit halves from one iteration    *)
(* of sha256hash_loop gives word_join4 of the expected new state.            *)
(*                                                                           *)
(* One lemma per loop index (0-3), differing only in which element of the    *)
(* packed round-key vector is used.                                          *)
(* ------------------------------------------------------------------------- *)

let SHA256_HASH_LOOP_STEP_TAC =
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256hash_loop; elem; word_join4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[WORD_JOIN4_SUBWORD_ALT] THEN
  REWRITE_TAC[WORD_JOIN_SUBWORD_32_96] THEN
  REWRITE_TAC[SHA256_ROT_HIGH; SHA256_ROT_LOW] THEN
  ONCE_REWRITE_TAC[WORD_JOIN_SUBWORD_32_96] THEN
  REWRITE_TAC[WORD_JOIN_REASSOC] THEN
  REPEAT(AP_TERM_TAC ORELSE (CONJ_TAC THENL [REFL_TAC; ALL_TAC])) THEN
  CONV_TAC WORD_RULE;;

let SHA256_HASH_LOOP_STEP0 = prove
 (`!a b c d e f g h kw0 kw1 kw2 kw3:int32.
    let T1 = word_add h (word_add (sha_hash_sigma_1 e)
               (word_add (sha_choose e f g) kw0)) in
    let T2 = word_add (sha_hash_sigma_0 a) (sha_maj a b c) in
    word_subword (sha256hash_loop 0
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (128,128)
      = (word_join4 (word_add T1 T2) a b c : int128) /\
    word_subword (sha256hash_loop 0
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (0,128)
      = (word_join4 (word_add d T1) e f g : int128)`,
  SHA256_HASH_LOOP_STEP_TAC);;

let SHA256_HASH_LOOP_STEP1 = prove
 (`!a b c d e f g h kw0 kw1 kw2 kw3:int32.
    let T1 = word_add h (word_add (sha_hash_sigma_1 e)
               (word_add (sha_choose e f g) kw1)) in
    let T2 = word_add (sha_hash_sigma_0 a) (sha_maj a b c) in
    word_subword (sha256hash_loop 1
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (128,128)
      = (word_join4 (word_add T1 T2) a b c : int128) /\
    word_subword (sha256hash_loop 1
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (0,128)
      = (word_join4 (word_add d T1) e f g : int128)`,
  SHA256_HASH_LOOP_STEP_TAC);;

let SHA256_HASH_LOOP_STEP2 = prove
 (`!a b c d e f g h kw0 kw1 kw2 kw3:int32.
    let T1 = word_add h (word_add (sha_hash_sigma_1 e)
               (word_add (sha_choose e f g) kw2)) in
    let T2 = word_add (sha_hash_sigma_0 a) (sha_maj a b c) in
    word_subword (sha256hash_loop 2
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (128,128)
      = (word_join4 (word_add T1 T2) a b c : int128) /\
    word_subword (sha256hash_loop 2
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (0,128)
      = (word_join4 (word_add d T1) e f g : int128)`,
  SHA256_HASH_LOOP_STEP_TAC);;

let SHA256_HASH_LOOP_STEP3 = prove
 (`!a b c d e f g h kw0 kw1 kw2 kw3:int32.
    let T1 = word_add h (word_add (sha_hash_sigma_1 e)
               (word_add (sha_choose e f g) kw3)) in
    let T2 = word_add (sha_hash_sigma_0 a) (sha_maj a b c) in
    word_subword (sha256hash_loop 3
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (128,128)
      = (word_join4 (word_add T1 T2) a b c : int128) /\
    word_subword (sha256hash_loop 3
      (word_join4 a b c d) (word_join4 e f g h)
      (word_join4 kw0 kw1 kw2 kw3) : 256 word) (0,128)
      = (word_join4 (word_add d T1) e f g : int128)`,
  SHA256_HASH_LOOP_STEP_TAC);;

(* Flattened versions with let bindings inlined, for use as rewrite rules *)
let SHA256_STEP0_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (REWRITE_RULE[word_join4] SHA256_HASH_LOOP_STEP0);;
let SHA256_STEP1_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (REWRITE_RULE[word_join4] SHA256_HASH_LOOP_STEP1);;
let SHA256_STEP2_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (REWRITE_RULE[word_join4] SHA256_HASH_LOOP_STEP2);;
let SHA256_STEP3_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (REWRITE_RULE[word_join4] SHA256_HASH_LOOP_STEP3);;

(* ------------------------------------------------------------------------- *)
(* SHA256H bridging lemma: the ARM SHA256H instruction (sha256h) on packed   *)
(* state correctly implements 4 rounds of sha256_compress_round.             *)
(*                                                                           *)
(* Given state [a;b;c;d;e;f;g;h] packed into:                               *)
(*   v0 = word_join4 a b c d    (bits 0-31 = a, ..., 96-127 = d)            *)
(*   v1 = word_join4 e f g h                                                *)
(* And pre-added round keys kw0..kw3 packed into:                            *)
(*   m  = word_join4 kw0 kw1 kw2 kw3                                        *)
(*                                                                           *)
(* Then sha256h v0 v1 m = word_join4 of the first 4 elements of the state    *)
(* after 4 rounds of sha256_compress_round with keys kw0..kw3.              *)
(* ------------------------------------------------------------------------- *)

let SHA256H_BRIDGE = prove
 (`!a b c d e f g h kw0 kw1 kw2 kw3:int32.
    let s0 = [a;b;c;d;e;f;g;h] in
    let s1 = sha256_compress_round kw0 (word 0) s0 in
    let s2 = sha256_compress_round kw1 (word 0) s1 in
    let s3 = sha256_compress_round kw2 (word 0) s2 in
    let s4 = sha256_compress_round kw3 (word 0) s3 in
    sha256h (word_join4 a b c d) (word_join4 e f g h)
            (word_join4 kw0 kw1 kw2 kw3) =
    word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256h; sha256hash; word_join4] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [COND_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256_STEP0_FLAT; SHA256_STEP1_FLAT;
              SHA256_STEP2_FLAT; SHA256_STEP3_FLAT] THEN
  REWRITE_TAC[sha256_compress_round;
              SHA256_CH_EQ_CHOOSE; SHA256_MAJ_EQ_MAJ;
              SHA256_SIGMA0_EQ; SHA256_SIGMA1_EQ] THEN
  CONV_TAC(DEPTH_CONV(let_CONV ORELSEC EL_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* SHA256H2 bridging lemma: the ARM SHA256H2 instruction (sha256h2) on       *)
(* packed state correctly implements the EFGH half (elements 4-7) of 4       *)
(* rounds of sha256_compress_round.                                          *)
(*                                                                           *)
(* Note: sha256h2 d n m = sha256hash n d m F (arguments swapped, returns Y). *)
(* In assembly: sha256h2(EFGH, saved_ABCD, KW) computes the same 4 rounds   *)
(* as sha256h but returns the low (EFGH) half.                               *)
(* ------------------------------------------------------------------------- *)

let SHA256H2_BRIDGE = prove
 (`!a b c d e f g h kw0 kw1 kw2 kw3:int32.
    let s0 = [a;b;c;d;e;f;g;h] in
    let s1 = sha256_compress_round kw0 (word 0) s0 in
    let s2 = sha256_compress_round kw1 (word 0) s1 in
    let s3 = sha256_compress_round kw2 (word 0) s2 in
    let s4 = sha256_compress_round kw3 (word 0) s3 in
    sha256h2 (word_join4 e f g h) (word_join4 a b c d)
             (word_join4 kw0 kw1 kw2 kw3) =
    word_join4 (EL 4 s4) (EL 5 s4) (EL 6 s4) (EL 7 s4)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256h2] THEN ONCE_REWRITE_TAC[sha256hash] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[word_join4] THEN
  REWRITE_TAC[SHA256_STEP0_FLAT; SHA256_STEP1_FLAT;
              SHA256_STEP2_FLAT; SHA256_STEP3_FLAT] THEN
  REWRITE_TAC[sha256_compress_round;
              SHA256_CH_EQ_CHOOSE; SHA256_MAJ_EQ_MAJ;
              SHA256_SIGMA0_EQ; SHA256_SIGMA1_EQ] THEN
  CONV_TAC(DEPTH_CONV(let_CONV ORELSEC EL_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REFL_TAC);;

(* ========================================================================= *)
(* Bridging lemmas for SHA256SU0/SU1 message schedule instructions.          *)
(* ========================================================================= *)

let WORD_JOIN_64_SUBWORDS = prove
 (`!(b:int32) (a:int32).
     word_subword ((word_join:int32->int32->64 word) b a) (0,32) = a /\
     word_subword ((word_join:int32->int32->64 word) b a) (32,32) = b`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN4_SUBWORD_32_96 = prove
 (`!(a:int32) (b:int32) (c:int32) (d:int32).
     word_subword ((word_join:int32->96 word->int128) d
       ((word_join:int32->64 word->96 word) c
         ((word_join:int32->int32->64 word) b a))) (32, 96) =
     (word_join:int32->64 word->96 word) d
       ((word_join:int32->int32->64 word) c b)`,
  REPEAT GEN_TAC THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN4_SUBWORD_64_64 = prove
 (`!a b c d:int32.
     word_subword (word_join4 a b c d : int128) (64,64) =
     (word_join:int32->int32->64 word) d c`,
  REWRITE_TAC[word_join4] THEN REPEAT GEN_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let WORD_JOIN4_SUBWORD_64_64_ALT =
  REWRITE_RULE[word_join4] WORD_JOIN4_SUBWORD_64_64;;

let WORD_ADD_COMM_ASSOC =
  WORD_RULE `word_add (word_add (x:N word) y) z = word_add z (word_add x y)`;;

(* SHA256SU0 + SHA256SU1 combined: computes 4 new message schedule words.   *)
(* The proof expands sha256su0 and sha256su1 step by step, eliminating all   *)
(* cross-width word_subword operations via extraction lemmas, then uses      *)
(* WORD_ADD_COMM_ASSOC to normalize word_add ordering differences between    *)
(* the hardware computation order and the spec order.                        *)
let SHA256SU_BRIDGE = prove
 (`!w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
    let w16 = word_add (sha256_sigma1 w14)
                (word_add w9 (word_add (sha256_sigma0 w1) w0)) in
    let w17 = word_add (sha256_sigma1 w15)
                (word_add w10 (word_add (sha256_sigma0 w2) w1)) in
    let w18 = word_add (sha256_sigma1 w16)
                (word_add w11 (word_add (sha256_sigma0 w3) w2)) in
    let w19 = word_add (sha256_sigma1 w17)
                (word_add w12 (word_add (sha256_sigma0 w4) w3)) in
    sha256su1 (sha256su0 (word_join4 w0 w1 w2 w3) (word_join4 w4 w5 w6 w7))
              (word_join4 w8 w9 w10 w11) (word_join4 w12 w13 w14 w15) =
    word_join4 w16 w17 w18 w19`,
  let EXTRACT_TAC =
    ONCE_REWRITE_TAC[WORD_JOIN4_SUBWORD_ALT; WORD_JOIN4_SUBWORD_32_96;
                      WORD_JOIN4_SUBWORD_64_64_ALT;
                      WORD_JOIN_96_SUBWORDS; WORD_JOIN_64_SUBWORDS;
                      WORD_JOIN_SUBWORD_32_96] in
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[sha256su0] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[sha256su0_loop] THEN
  REWRITE_TAC[elem; word_join4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[WORD_JOIN_SUBWORD_32_96; WORD_JOIN4_SUBWORD_ALT;
              WORD_JOIN4_SUBWORD_32_96] THEN
  ONCE_REWRITE_TAC[sha256su1] THEN
  REWRITE_TAC[sha256su1_loop0; sha256su1_loop1; elem] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  EXTRACT_TAC THEN EXTRACT_TAC THEN EXTRACT_TAC THEN
  REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
  ONCE_REWRITE_TAC[WORD_ADD_COMM_ASSOC] THEN
  REFL_TAC);;

(* ========================================================================= *)
(* Helper lemmas for ADD V.4S pre-addition in assembly proofs.               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Re-nesting: ADD V.4S produces word_join of two 64-bit halves, but         *)
(* word_join4 nests as word_join 32 (word_join 32 (word_join 32 32)).         *)
(* These are equal but syntactically different.                              *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_4x32 = prove
 (`!(a:int32) (b:int32) (c:int32) (d:int32).
     (word_join:64 word->64 word->int128)
       ((word_join:int32->int32->64 word) d c)
       ((word_join:int32->int32->64 word) b a) =
     word_join4 a b c d`,
  REWRITE_TAC[word_join4] THEN REPEAT GEN_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Pre-addition equivalence: the hardware pre-adds K[t]+W[t] before          *)
(* SHA256H, so the bridging lemma uses sha256_compress_round kw (word 0).    *)
(* This lemma lets us convert to the standard spec form with separate K, W.  *)
(*                                                                           *)
(* IMPORTANT: Apply bridging lemmas BEFORE this lemma (forward direction).   *)
(* Using GSYM loops because word_add K W always matches the K argument.      *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_ROUND_PREADD = prove
 (`!(K_t:int32) (W_t:int32) state.
     sha256_compress_round (word_add K_t W_t) (word 0) state =
     sha256_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* K/W argument commutativity: sha256_compress_round only uses               *)
(* word_add K_t W_t, which is commutative, so swapping K and W is safe.      *)
(* Needed because ADD V.4S may produce word_add W K instead of word_add K W. *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_ROUND_KW_SYM = prove
 (`!(K_t:int32) (W_t:int32) state.
     sha256_compress_round K_t W_t state =
     sha256_compress_round W_t K_t state`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `word_add (W_t:int32) K_t = word_add K_t W_t`
    SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; REFL_TAC]);;
