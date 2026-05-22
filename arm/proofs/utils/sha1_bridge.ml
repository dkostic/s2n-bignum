(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas connecting the SHA-1 FIPS-spec primitives in              *)
(* arm/proofs/utils/sha1_spec.ml to the ARM HW operator semantics in         *)
(* arm/proofs/sha1.ml.                                                       *)
(*                                                                           *)
(* This file is the only explicitly-permitted coupling site between the      *)
(* two: it loads both, and proves the equivalences a downstream `ensures`    *)
(* proof needs to translate one execution-step worth of SHA1{C,P,M,H,SU0,    *)
(* SU1} into the corresponding FIPS-spec rounds / schedule extension.        *)
(*                                                                           *)
(* The exported bridge theorems are:                                         *)
(*                                                                           *)
(*   SHA1H_BRIDGE  : sha1h on a 4-lane state isolates ROL_30 of the bottom   *)
(*                   lane (zeroing the upper 96 bits).                       *)
(*                                                                           *)
(*   SHA1C/P/M_BRIDGE : sha1{c,p,m} on (state, e, kw) equals four rounds of  *)
(*                   the helper sha1_compress_round_pre with f-selector     *)
(*                   ft = 0/1/2 (Choose / Parity / Maj) and the four         *)
(*                   pre-added kw lanes.                                     *)
(*                                                                           *)
(*   SHA1SU_BRIDGE : sha1su1 (sha1su0 ...) on consecutive 4-lane W-blocks    *)
(*                   yields the next four W's per the FIPS message-schedule  *)
(*                   recurrence  W_t = ROL_1 (W_{t-3} XOR W_{t-8} XOR        *)
(*                   W_{t-14} XOR W_{t-16}).                                 *)
(*                                                                           *)
(* The compression-round bridges are stated against a helper                 *)
(* `sha1_compress_round_pre ft kw state` rather than directly against        *)
(* `sha1_compress_round t W_t state`. The helper takes a one-byte selector  *)
(* `ft \in {0,1,2}` and a pre-summed `kw = sha1_K t + W_t`, decoupling the  *)
(* HW shape (which sees kw and ft) from the FIPS shape (which threads the   *)
(* round number t and re-derives K_t / f_t inside `sha1_compress_round`).   *)
(* The four `SHA1_COMPRESS_ROUND_PRE_EQ_*` lemmas connect them for the       *)
(* round ranges 0..19, 20..39, 40..59, 60..79.                              *)
(* ========================================================================= *)

needs "arm/proofs/sha1.ml";;
needs "arm/proofs/utils/sha1_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* sha1_Ch / sha1_Maj / sha1_Parity (textbook FIPS form, used in the spec)   *)
(* coincide with sha1_choose / sha1_majority / sha1_parity (Choose-encoded   *)
(* form, used in the HW operator semantics).                                 *)
(* ------------------------------------------------------------------------- *)

let SHA1_CH_EQ_CHOOSE = prove
 (`!x y z. sha1_Ch x y z = sha1_choose x y z`,
  REWRITE_TAC[sha1_Ch; sha1_choose] THEN CONV_TAC WORD_RULE);;

let SHA1_MAJ_EQ_MAJORITY = prove
 (`!x y z. sha1_Maj x y z = sha1_majority x y z`,
  REWRITE_TAC[sha1_Maj; sha1_majority] THEN CONV_TAC WORD_RULE);;

let SHA1_PARITY_EQ = prove
 (`!x y z. sha1_Parity x y z = sha1_parity x y z`,
  REWRITE_TAC[sha1_Parity; sha1_parity] THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Packing helper: pack four 32-bit words into one 128-bit word, with        *)
(*   a at lanes 0 (bits 0-31), b at lane 1, c at lane 2, d at lane 3.        *)
(* This matches the lane order used in arm/proofs/sha1.ml's `sha1hash_loop`  *)
(* (and in the SHA-256 pilot's bridge file).                                 *)
(* ------------------------------------------------------------------------- *)

let word_join4 = new_definition
 `word_join4 (a:int32) (b:int32) (c:int32) (d:int32) : int128 =
    (word_join:int32->96 word->int128) d
      ((word_join:int32->64 word->96 word) c
        ((word_join:int32->int32->64 word) b a))`;;

let WORD_JOIN4_SUBWORD = prove
 (`!a b c d:int32.
     word_subword (word_join4 a b c d : int128) (0,32) = a /\
     word_subword (word_join4 a b c d : int128) (32,32) = b /\
     word_subword (word_join4 a b c d : int128) (64,32) = c /\
     word_subword (word_join4 a b c d : int128) (96,32) = d /\
     word_subword (word_join4 a b c d : int128) (0,64) =
       (word_join:int32->int32->64 word) b a /\
     word_subword (word_join4 a b c d : int128) (64,64) =
       (word_join:int32->int32->64 word) d c`,
  REWRITE_TAC[word_join4] THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* SHA1H bridge.                                                             *)
(*                                                                           *)
(* SHA1H reads the bottom 32-bit lane, ROLs by 30, and zero-extends to 128.  *)
(* In word_join4 form the input is (a,b,c,d) and the output is               *)
(* (ROL_30 a, 0, 0, 0).                                                      *)
(* ------------------------------------------------------------------------- *)

let SHA1H_BRIDGE = prove
 (`!a b c d:int32.
    sha1h (word_join4 a b c d) =
    word_join4 (word_rol a 30) (word 0) (word 0) (word 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha1h; word_join4] THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* sha1_compress_round_pre: HW-shaped helper that takes an f-selector ft     *)
(* and a pre-summed kw = sha1_K t + W_t. Performs one round of compression.  *)
(* The four SHA1_COMPRESS_ROUND_PRE_EQ_* lemmas show how this lines up with  *)
(* the FIPS-shaped sha1_compress_round in each of the four 20-round bands.  *)
(* ------------------------------------------------------------------------- *)

let sha1_compress_round_pre = new_definition
 `sha1_compress_round_pre (ft:num) (kw:int32) (state:int32 list) : int32 list =
    let a = EL 0 state and b = EL 1 state and c = EL 2 state
    and d = EL 3 state and e = EL 4 state in
    let T = word_add (word_rol a 5)
              (word_add (sha1_funct ft b c d)
                 (word_add e kw)) in
    [T; a; word_rol b 30; c; d]`;;

let SHA1_COMPRESS_ROUND_PRE_EQ_LO = prove
 (`!t (W_t:int32) state.
     t < 20
     ==> sha1_compress_round_pre 0 (word_add (sha1_K t) W_t) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha1_compress_round_pre; sha1_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1_funct; sha1_f] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[SHA1_CH_EQ_CHOOSE] THEN
  CONV_TAC WORD_RULE);;

let SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_LO = prove
 (`!t (W_t:int32) state.
     20 <= t /\ t < 40
     ==> sha1_compress_round_pre 1 (word_add (sha1_K t) W_t) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha1_compress_round_pre; sha1_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1_funct; sha1_f] THEN
  SUBGOAL_THEN `~(t < 20) /\ t < 40` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[SHA1_PARITY_EQ] THEN
  CONV_TAC WORD_RULE);;

let SHA1_COMPRESS_ROUND_PRE_EQ_MAJ = prove
 (`!t (W_t:int32) state.
     40 <= t /\ t < 60
     ==> sha1_compress_round_pre 2 (word_add (sha1_K t) W_t) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha1_compress_round_pre; sha1_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1_funct; sha1_f] THEN
  SUBGOAL_THEN `~(t < 20) /\ ~(t < 40) /\ t < 60` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[SHA1_MAJ_EQ_MAJORITY] THEN
  CONV_TAC WORD_RULE);;

let SHA1_COMPRESS_ROUND_PRE_EQ_PARITY_HI = prove
 (`!t (W_t:int32) state.
     60 <= t /\ t < 80
     ==> sha1_compress_round_pre 1 (word_add (sha1_K t) W_t) state =
         sha1_compress_round t W_t state`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha1_compress_round_pre; sha1_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1_funct; sha1_f] THEN
  SUBGOAL_THEN `~(t < 20) /\ ~(t < 40) /\ ~(t < 60)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[SHA1_PARITY_EQ] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Single-round step lemmas: extracting the 128-bit and 32-bit halves from   *)
(* one iteration of sha1hash_loop matches word_join4 of the expected new     *)
(* state and the unchanged d, respectively.                                  *)
(*                                                                           *)
(* Four lemmas, one per `e` index 0..3, since sha1_elem indexes the kw word  *)
(* corresponding to the round.                                               *)
(* ------------------------------------------------------------------------- *)

let SHA1_HASH_LOOP_STEP_TAC =
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `!ft a b c d e:int32 kw:int32.
      word_add e
        (word_add (word_rol (a:int32) 5)
          (word_add (sha1_funct ft b c d) kw)) =
      word_add (word_rol (a:int32) 5)
        (word_add (sha1_funct ft b c d) (word_add e kw))`
   ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[sha1hash_loop; sha1_elem] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[WORD_JOIN4_SUBWORD] THEN
  FIRST_ASSUM (fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[word_join4] THEN
  CONJ_TAC THEN BITBLAST_TAC;;

let SHA1_HASH_LOOP_STEP0 = prove
 (`!ft a b c d kw0 kw1 kw2 kw3 e:int32.
    word_subword (sha1hash_loop ft 0
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (0,128)
      = word_join4
          (word_add (word_rol a 5)
            (word_add (sha1_funct ft b c d) (word_add e kw0)))
          a (word_rol b 30) c /\
    word_subword (sha1hash_loop ft 0
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (128,32) = d`,
  SHA1_HASH_LOOP_STEP_TAC);;

let SHA1_HASH_LOOP_STEP1 = prove
 (`!ft a b c d kw0 kw1 kw2 kw3 e:int32.
    word_subword (sha1hash_loop ft 1
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (0,128)
      = word_join4
          (word_add (word_rol a 5)
            (word_add (sha1_funct ft b c d) (word_add e kw1)))
          a (word_rol b 30) c /\
    word_subword (sha1hash_loop ft 1
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (128,32) = d`,
  SHA1_HASH_LOOP_STEP_TAC);;

let SHA1_HASH_LOOP_STEP2 = prove
 (`!ft a b c d kw0 kw1 kw2 kw3 e:int32.
    word_subword (sha1hash_loop ft 2
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (0,128)
      = word_join4
          (word_add (word_rol a 5)
            (word_add (sha1_funct ft b c d) (word_add e kw2)))
          a (word_rol b 30) c /\
    word_subword (sha1hash_loop ft 2
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (128,32) = d`,
  SHA1_HASH_LOOP_STEP_TAC);;

let SHA1_HASH_LOOP_STEP3 = prove
 (`!ft a b c d kw0 kw1 kw2 kw3 e:int32.
    word_subword (sha1hash_loop ft 3
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (0,128)
      = word_join4
          (word_add (word_rol a 5)
            (word_add (sha1_funct ft b c d) (word_add e kw3)))
          a (word_rol b 30) c /\
    word_subword (sha1hash_loop ft 3
      (word_join4 a b c d) e
      (word_join4 kw0 kw1 kw2 kw3) : 160 word) (128,32) = d`,
  SHA1_HASH_LOOP_STEP_TAC);;

(* ------------------------------------------------------------------------- *)
(* SHA1C/P/M bridges: each rewrites one HW invocation of sha1{c,p,m} as four *)
(* applications of sha1_compress_round_pre with the right ft selector.       *)
(*                                                                           *)
(* In the proof, sha1{c,p,m} is unfolded once, sha1hash is unfolded into     *)
(* four sha1hash_loop applications, the four step lemmas above rewrite each  *)
(* loop iteration into a word_join4 of the next state, and the four          *)
(* sha1_compress_round_pre applications on the RHS reduce by EL/let to the  *)
(* same word_join4.                                                          *)
(* ------------------------------------------------------------------------- *)

let SHA1C_BRIDGE = prove
 (`!a b c d e kw0 kw1 kw2 kw3:int32.
    let s0 = [a;b;c;d;e] in
    let s1 = sha1_compress_round_pre 0 kw0 s0 in
    let s2 = sha1_compress_round_pre 0 kw1 s1 in
    let s3 = sha1_compress_round_pre 0 kw2 s2 in
    let s4 = sha1_compress_round_pre 0 kw3 s3 in
    sha1c (word_join4 a b c d) e (word_join4 kw0 kw1 kw2 kw3) =
    word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1c; sha1hash] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA1_HASH_LOOP_STEP0; SHA1_HASH_LOOP_STEP1;
              SHA1_HASH_LOOP_STEP2; SHA1_HASH_LOOP_STEP3] THEN
  REWRITE_TAC[sha1_compress_round_pre] THEN
  CONV_TAC(DEPTH_CONV(let_CONV ORELSEC EL_CONV)) THEN
  REFL_TAC);;

let SHA1P_BRIDGE = prove
 (`!a b c d e kw0 kw1 kw2 kw3:int32.
    let s0 = [a;b;c;d;e] in
    let s1 = sha1_compress_round_pre 1 kw0 s0 in
    let s2 = sha1_compress_round_pre 1 kw1 s1 in
    let s3 = sha1_compress_round_pre 1 kw2 s2 in
    let s4 = sha1_compress_round_pre 1 kw3 s3 in
    sha1p (word_join4 a b c d) e (word_join4 kw0 kw1 kw2 kw3) =
    word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1p; sha1hash] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA1_HASH_LOOP_STEP0; SHA1_HASH_LOOP_STEP1;
              SHA1_HASH_LOOP_STEP2; SHA1_HASH_LOOP_STEP3] THEN
  REWRITE_TAC[sha1_compress_round_pre] THEN
  CONV_TAC(DEPTH_CONV(let_CONV ORELSEC EL_CONV)) THEN
  REFL_TAC);;

let SHA1M_BRIDGE = prove
 (`!a b c d e kw0 kw1 kw2 kw3:int32.
    let s0 = [a;b;c;d;e] in
    let s1 = sha1_compress_round_pre 2 kw0 s0 in
    let s2 = sha1_compress_round_pre 2 kw1 s1 in
    let s3 = sha1_compress_round_pre 2 kw2 s2 in
    let s4 = sha1_compress_round_pre 2 kw3 s3 in
    sha1m (word_join4 a b c d) e (word_join4 kw0 kw1 kw2 kw3) =
    word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1m; sha1hash] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA1_HASH_LOOP_STEP0; SHA1_HASH_LOOP_STEP1;
              SHA1_HASH_LOOP_STEP2; SHA1_HASH_LOOP_STEP3] THEN
  REWRITE_TAC[sha1_compress_round_pre] THEN
  CONV_TAC(DEPTH_CONV(let_CONV ORELSEC EL_CONV)) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* SHA1SU bridge: the sha1su0+sha1su1 pair extends the message schedule by  *)
(* four words, per the FIPS recurrence                                       *)
(*    W_t = ROL_1 (W_{t-3} XOR W_{t-8} XOR W_{t-14} XOR W_{t-16}).           *)
(*                                                                           *)
(* Inputs are four packed 4-lane W blocks containing W_{i+0..i+15}; output  *)
(* is the next 4-lane block W_{i+16..i+19}.                                  *)
(* ------------------------------------------------------------------------- *)

let SHA1SU_BRIDGE = prove
 (`!w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
    let w16 = word_rol (word_xor w13 (word_xor w8 (word_xor w2 w0))) 1 in
    let w17 = word_rol (word_xor w14 (word_xor w9 (word_xor w3 w1))) 1 in
    let w18 = word_rol (word_xor w15 (word_xor w10 (word_xor w4 w2))) 1 in
    let w19 = word_rol (word_xor w16 (word_xor w11 (word_xor w5 w3))) 1 in
    sha1su1 (sha1su0 (word_join4 w0 w1 w2 w3) (word_join4 w4 w5 w6 w7)
                     (word_join4 w8 w9 w10 w11))
            (word_join4 w12 w13 w14 w15) =
    word_join4 w16 w17 w18 w19`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha1su0; sha1su1; word_join4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BITBLAST_TAC);;
