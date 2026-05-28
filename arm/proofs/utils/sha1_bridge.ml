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
 (`!a b c d kw0 kw1 kw2 kw3:int32. !e:int128.
    let s0 = [a;b;c;d;(word_subword e (0,32):int32)] in
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
 (`!a b c d kw0 kw1 kw2 kw3:int32. !e:int128.
    let s0 = [a;b;c;d;(word_subword e (0,32):int32)] in
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
 (`!a b c d kw0 kw1 kw2 kw3:int32. !e:int128.
    let s0 = [a;b;c;d;(word_subword e (0,32):int32)] in
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

(* ========================================================================= *)
(* Phase 9 byte-level bridges.                                               *)
(*                                                                           *)
(* These connect the byte-level public spec (in arm/proofs/utils/             *)
(* sha1_spec.ml: sha1_word_be / sha1_block_word / sha1_block_from_bytes /     *)
(* sha1_blocks_from_bytes / sha1_hash_bytes) to the int32-list view that      *)
(* SHA1_HW_SUBROUTINE_CORRECT (in arm/proofs/sha1_block_data_order_hw_       *)
(* ensures.ml) consumes.                                                     *)
(* ========================================================================= *)

(* Length of the block decomposition. *)
let LENGTH_SHA1_BLOCKS_FROM_BYTES = prove
 (`!num_blocks bs.
    LENGTH (sha1_blocks_from_bytes num_blocks bs) = num_blocks`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha1_blocks_from_bytes; LENGTH; LENGTH_APPEND;
                  ARITH; ADD1]);;

(* The j-th block of a num_blocks-block decomposition. *)
let EL_SHA1_BLOCKS_FROM_BYTES = prove
 (`!num_blocks bs j.
    j < num_blocks
    ==> EL j (sha1_blocks_from_bytes num_blocks bs) =
        sha1_block_from_bytes j bs`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ADD1; sha1_blocks_from_bytes; EL_APPEND;
              LENGTH_SHA1_BLOCKS_FROM_BYTES] THEN
  ASM_CASES_TAC `j:num < num_blocks` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `j:num = num_blocks` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_REFL; EL; HD; LT_REFL]);;

(* Each block produced by sha1_block_from_bytes has length 16. *)
let LENGTH_SHA1_BLOCK_FROM_BYTES = prove
 (`!j bs. LENGTH (sha1_block_from_bytes j bs) = 16`,
  REWRITE_TAC[sha1_block_from_bytes; LENGTH; ARITH]);;

(* Therefore every block in the multi-block decomposition has length 16. *)
let ALL_LENGTH_SHA1_BLOCKS_FROM_BYTES = prove
 (`!num_blocks bs.
    ALL (\bl. LENGTH bl = 16) (sha1_blocks_from_bytes num_blocks bs)`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha1_blocks_from_bytes; ALL; ALL_APPEND;
                  ADD1; LENGTH_SHA1_BLOCK_FROM_BYTES]);;

(* The k-th word of the j-th block, for k < 16. *)
let EL_SHA1_BLOCK_FROM_BYTES = prove
 (`!j bs k.
    k < 16
    ==> EL k (sha1_block_from_bytes j bs) = sha1_block_word j k bs`,
  GEN_TAC THEN GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[sha1_block_from_bytes] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* word_bytereverse of sha1_block_word reduces to a raw 4-byte read.        *)
(* This is the key identity: it says "the FIPS-big-endian word, after an    *)
(* extra word_bytereverse, is just the natural little-endian decode of the  *)
(* 4 bytes." That natural decode is what `read (memory :> bytes32 _)`       *)
(* produces when bytes are stored little-endian (the norm).                 *)
let WORD_BYTEREVERSE_SHA1_BLOCK_WORD = prove
 (`!j k bs.
    word_bytereverse (sha1_block_word j k bs) :int32 =
    word(num_of_bytelist [EL (64*j + 4*k + 0) bs;
                          EL (64*j + 4*k + 1) bs;
                          EL (64*j + 4*k + 2) bs;
                          EL (64*j + 4*k + 3) bs])`,
  REWRITE_TAC[sha1_block_word; sha1_word_be; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* Memory-level helpers: byte-list reads project to bytes32 / bytes128 reads. *)

(* A bytes128 read can be split into a word_join4 of four bytes32 reads. *)
let READ_BYTES128_AS_WORD_JOIN4_BYTES32 = prove
 (`!a s.
    read (memory :> bytes128 a) s :int128 =
    word_join4 (read (memory :> bytes32 a) s)
               (read (memory :> bytes32 (word_add a (word 4))) s)
               (read (memory :> bytes32 (word_add a (word 8))) s)
               (read (memory :> bytes32 (word_add a (word 12))) s)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
    [CONJUNCT1 (CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [CONJUNCT1 (CONJUNCT2 (CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
  REWRITE_TAC[word_join4;
              WORD_RULE `word_add (word_add a (word 8)) (word 4) =
                         word_add a (word 12)`] THEN
  BITBLAST_TAC);;

(* If a bytelist of length 4 reads to [b0;b1;b2;b3], the bytes32 read at the *)
(* same address is word(num_of_bytelist [b0;b1;b2;b3]).                       *)
let READ_BYTES32_FROM_BYTELIST_4 = prove
 (`!a s b0 b1 b2 b3.
    read (memory :> bytelist (a,4)) s = [b0;b1;b2;b3]
    ==> read (memory :> bytes32 a) s :int32 =
        word(num_of_bytelist [b0;b1;b2;b3])`,
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through;
              READ_BYTELIST_EQ_BYTES; read] THEN
  MESON_TAC[]);;

(* Byte-by-byte projection of a bytelist read: each byte at offset i is      *)
(* EL i of the byte list. The list-as-spec form makes this independent of    *)
(* the master address.                                                       *)
let READ_MEMORY_FROM_BYTELIST = prove
 (`!(l:byte list) a s i.
    read (memory :> bytelist (a, LENGTH l)) s = l /\ i < LENGTH l
    ==> read memory s (word_add a (word i)) = EL i l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT] THEN
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist_clauses; CONS_11;
              EL; HD; TL; WORD_ADD_0] THEN
  REWRITE_TAC[ARITH_RULE
    `(SUC i = LENGTH t \/ SUC i < LENGTH t) <=> i < LENGTH t`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`word_add (a:int64) (word 1)`; `s:armstate`; `i:num`]) THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[WORD_RULE
    `word_add (word_add a (word 1)) (word i) = word_add a (word (SUC i))`]);;

(* A 4-byte slice of a master bytelist read becomes a bytes32 read.          *)
let SHA1_BYTES32_FROM_BYTELIST = prove
 (`!s data_ptr (bs:byte list) m.
    read (memory :> bytelist (data_ptr, LENGTH bs)) s = bs /\
    m + 4 <= LENGTH bs
    ==>
    read (memory :> bytes32 (word_add data_ptr (word m))) s :int32 =
      word(num_of_bytelist
             [EL m bs; EL (m+1) bs; EL (m+2) bs; EL (m+3) bs])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC READ_BYTES32_FROM_BYTELIST_4 THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist_clauses;
                  ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; CONS_11] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV
   [WORD_RULE `word_add (word_add (word_add (word_add data_ptr (word m))
                          (word 1)) (word 1)) (word 1) =
               word_add data_ptr (word (m + 3))`] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV
   [WORD_RULE `word_add (word_add (word_add data_ptr (word m)) (word 1))
                         (word 1) = word_add data_ptr (word (m + 2))`] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV
   [WORD_RULE `word_add (word_add data_ptr (word m)) (word 1) =
               word_add data_ptr (word (m + 1))`] THEN
  CONJ_TAC THENL [
    MP_TAC(SPECL [`bs:byte list`; `data_ptr:int64`; `s:armstate`; `m:num`]
      READ_MEMORY_FROM_BYTELIST) THEN
    ASM_SIMP_TAC[WORD_ADD_0; ARITH_RULE `m + 4 <= n ==> m < n`];
    CONJ_TAC THENL [
      MP_TAC(SPECL [`bs:byte list`; `data_ptr:int64`; `s:armstate`; `m + 1`]
        READ_MEMORY_FROM_BYTELIST) THEN
      ASM_SIMP_TAC[ARITH_RULE `m + 4 <= n ==> m + 1 < n`];
      CONJ_TAC THENL [
        MP_TAC(SPECL [`bs:byte list`; `data_ptr:int64`; `s:armstate`; `m + 2`]
          READ_MEMORY_FROM_BYTELIST) THEN
        ASM_SIMP_TAC[ARITH_RULE `m + 4 <= n ==> m + 2 < n`];
        MP_TAC(SPECL [`bs:byte list`; `data_ptr:int64`; `s:armstate`; `m + 3`]
          READ_MEMORY_FROM_BYTELIST) THEN
        ASM_SIMP_TAC[ARITH_RULE `m + 4 <= n ==> m + 3 < n`]
      ]
    ]
  ]);;

(* A 16-byte slice of a master bytelist read becomes a bytes128 read,        *)
(* expressed as a word_join4 of four 4-byte word-of-num_of_bytelist forms.   *)
let SHA1_BYTES128_FROM_BYTELIST = prove
 (`!s data_ptr (bs:byte list) m.
    read (memory :> bytelist (data_ptr, LENGTH bs)) s = bs /\
    m + 16 <= LENGTH bs
    ==>
    read (memory :> bytes128 (word_add data_ptr (word m))) s :int128 =
      word_join4
        (word(num_of_bytelist [EL m bs; EL(m+1) bs; EL(m+2) bs; EL(m+3) bs]))
        (word(num_of_bytelist [EL(m+4) bs; EL(m+5) bs;
                               EL(m+6) bs; EL(m+7) bs]))
        (word(num_of_bytelist [EL(m+8) bs; EL(m+9) bs;
                               EL(m+10) bs; EL(m+11) bs]))
        (word(num_of_bytelist [EL(m+12) bs; EL(m+13) bs;
                               EL(m+14) bs; EL(m+15) bs]))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[READ_BYTES128_AS_WORD_JOIN4_BYTES32] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV
   [WORD_RULE `word_add (word_add data_ptr (word m)) (word 4) =
               word_add data_ptr (word (m + 4))`] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV
   [WORD_RULE `word_add (word_add data_ptr (word m)) (word 8) =
               word_add data_ptr (word (m + 8))`] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV
   [WORD_RULE `word_add (word_add data_ptr (word m)) (word 12) =
               word_add data_ptr (word (m + 12))`] THEN
  MP_TAC(SPECL [`s:armstate`; `data_ptr:int64`; `bs:byte list`; `m:num`]
    SHA1_BYTES32_FROM_BYTELIST) THEN
  ASM_SIMP_TAC[ARITH_RULE `m + 16 <= n ==> m + 4 <= n`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`s:armstate`; `data_ptr:int64`; `bs:byte list`; `m + 4`]
    SHA1_BYTES32_FROM_BYTELIST) THEN
  ASM_SIMP_TAC[ARITH_RULE `m + 16 <= n ==> (m + 4) + 4 <= n`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`s:armstate`; `data_ptr:int64`; `bs:byte list`; `m + 8`]
    SHA1_BYTES32_FROM_BYTELIST) THEN
  ASM_SIMP_TAC[ARITH_RULE `m + 16 <= n ==> (m + 8) + 4 <= n`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`s:armstate`; `data_ptr:int64`; `bs:byte list`; `m + 12`]
    SHA1_BYTES32_FROM_BYTELIST) THEN
  ASM_SIMP_TAC[ARITH_RULE `m + 16 <= n ==> (m + 12) + 4 <= n`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(m + 4) + 1 = m + 5`;
              ARITH_RULE `(m + 4) + 2 = m + 6`;
              ARITH_RULE `(m + 4) + 3 = m + 7`;
              ARITH_RULE `(m + 8) + 1 = m + 9`;
              ARITH_RULE `(m + 8) + 2 = m + 10`;
              ARITH_RULE `(m + 8) + 3 = m + 11`;
              ARITH_RULE `(m + 12) + 1 = m + 13`;
              ARITH_RULE `(m + 12) + 2 = m + 14`;
              ARITH_RULE `(m + 12) + 3 = m + 15`]);;
