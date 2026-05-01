(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas connecting SHA-256 algorithmic spec to x86 SHA-NI         *)
(* instruction semantics.                                                    *)
(*                                                                           *)
(* Depends on:                                                               *)
(*   - common/sha256_spec.ml   (algorithmic spec)                            *)
(*   - x86/proofs/x86.ml       (x86 semantics including SHA-NI)              *)
(*                                                                           *)
(* x86 SHA-NI state packing (see Intel SDM Vol. 2B, SHA extensions) splits   *)
(* the 8-word working state into two 128-bit lanes:                          *)
(*                                                                           *)
(*   ABEF lane: [ F | E | B | A ]  (bits 0..31 = F, 32..63 = E, ...)         *)
(*   CDGH lane: [ H | G | D | C ]                                            *)
(*                                                                           *)
(* sha256rnds2 takes the CDGH lane in its first operand (dest) and the ABEF  *)
(* lane in its second operand (src), reads the round-key + message addends   *)
(* from xmm0, and advances 2 compression rounds.  The result is a new ABEF   *)
(* lane (written into dest).  A second sha256rnds2 with arguments swapped   *)
(* completes a 4-round group, yielding a fresh ABEF/CDGH pair.               *)
(* ========================================================================= *)

needs "common/sha256_spec.ml";;
needs "x86/proofs/x86.ml";;

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
(* Pre-addition equivalence: the assembly pre-adds K[t]+W[t] before          *)
(* sha256rnds2, so the atomic bridge uses sha256_compress_round kw (word 0). *)
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
(* Needed because paddd may produce word_add W K instead of word_add K W.    *)
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

(* ========================================================================= *)
(* Phase 2: Packing helpers and subword lemmas.                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* word_join4 a b c d : lane 0 = a, lane 1 = b, lane 2 = c, lane 3 = d       *)
(* (same bit layout as ARM's word_join4 to keep proofs interchangeable).     *)
(* ------------------------------------------------------------------------- *)

let word_join4 = new_definition
 `word_join4 (a:int32) (b:int32) (c:int32) (d:int32) : int128 =
    (word_join:int32->96 word->int128) d
      ((word_join:int32->64 word->96 word) c
        ((word_join:int32->int32->64 word) b a))`;;

(* ------------------------------------------------------------------------- *)
(* x86 SHA-NI state packing.                                                 *)
(*                                                                           *)
(* ABEF_PACK packs the 4 working variables {A,B,E,F} into one xmm register.  *)
(* Lane order (Intel SDM): lane 0 = F, 1 = E, 2 = B, 3 = A.                  *)
(*                                                                           *)
(* CDGH_PACK packs {C,D,G,H}: lane 0 = H, 1 = G, 2 = D, 3 = C.               *)
(* ------------------------------------------------------------------------- *)

let ABEF_PACK = new_definition
 `ABEF_PACK (a:int32) (b:int32) (e:int32) (f:int32) : int128 =
    word_join4 f e b a`;;

let CDGH_PACK = new_definition
 `CDGH_PACK (c:int32) (d:int32) (g:int32) (h:int32) : int128 =
    word_join4 h g d c`;;

(* ------------------------------------------------------------------------- *)
(* Subword extraction lemmas for word_join4.                                 *)
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
(* Subword extraction for ABEF_PACK / CDGH_PACK, to be used directly by the  *)
(* bridge proofs.                                                            *)
(* ------------------------------------------------------------------------- *)

let ABEF_PACK_SUBWORD = prove
 (`!a b e f:int32.
     word_subword (ABEF_PACK a b e f : int128) (0,32) = f /\
     word_subword (ABEF_PACK a b e f : int128) (32,32) = e /\
     word_subword (ABEF_PACK a b e f : int128) (64,32) = b /\
     word_subword (ABEF_PACK a b e f : int128) (96,32) = a`,
  REWRITE_TAC[ABEF_PACK; WORD_JOIN4_SUBWORD]);;

let CDGH_PACK_SUBWORD = prove
 (`!c d g h:int32.
     word_subword (CDGH_PACK c d g h : int128) (0,32) = h /\
     word_subword (CDGH_PACK c d g h : int128) (32,32) = g /\
     word_subword (CDGH_PACK c d g h : int128) (64,32) = d /\
     word_subword (CDGH_PACK c d g h : int128) (96,32) = c`,
  REWRITE_TAC[CDGH_PACK; WORD_JOIN4_SUBWORD]);;

(* ------------------------------------------------------------------------- *)
(* Sanity check against hand-computed lane values.  Catches lane-order bugs  *)
(* in ABEF_PACK / CDGH_PACK before they propagate into downstream bridges.   *)
(*                                                                           *)
(* With A=0x11111111, B=0x22222222, E=0x55555555, F=0x66666666:              *)
(*   ABEF_PACK produces the 128-bit value                                    *)
(*     0x11111111_22222222_55555555_66666666                                 *)
(*   i.e. A in the top (bits 96..127) and F in the bottom (bits 0..31).     *)
(* ------------------------------------------------------------------------- *)

let ABEF_PACK_SANITY = prove
 (`ABEF_PACK (word 0x11111111) (word 0x22222222)
             (word 0x55555555) (word 0x66666666) =
   word 0x11111111222222225555555566666666 : int128`,
  REWRITE_TAC[ABEF_PACK; word_join4] THEN CONV_TAC WORD_REDUCE_CONV);;

let CDGH_PACK_SANITY = prove
 (`CDGH_PACK (word 0x33333333) (word 0x44444444)
             (word 0x77777777) (word 0x88888888) =
   word 0x33333333444444447777777788888888 : int128`,
  REWRITE_TAC[CDGH_PACK; word_join4] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ========================================================================= *)
(* Phase 3: Pure-value form of x86_SHA256RNDS2 and the 2-round bridge.       *)
(*                                                                           *)
(* x86_SHA256RNDS2 in x86/proofs/x86.ml is a state transformer defined as    *)
(*                                                                           *)
(*   x86_SHA256RNDS2 dest src wk s =                                         *)
(*     let cdgh = read dest s and abef = read src s                          *)
(*     and wkval = read wk s in                                              *)
(*     ... pure computation of the new ABEF lane ...                         *)
(*     let res = ... in                                                      *)
(*     (dest := res) s                                                       *)
(*                                                                           *)
(* We factor out the pure value computation as sha_ni_rnds2, mirroring the   *)
(* aesenc / x86_AESENC split in x86/proofs/aes.ml, so that bridging to the   *)
(* FIPS 180-4 spec can be done at the value level.                           *)
(* ========================================================================= *)

let sha_ni_rnds2 = new_definition
 `sha_ni_rnds2 (cdgh:int128) (abef:int128) (wkval:int128) : int128 =
    let a_0 = word_subword abef (96,32):(32)word
    and b_0 = word_subword abef (64,32):(32)word
    and c_0 = word_subword cdgh (96,32):(32)word
    and d_0 = word_subword cdgh (64,32):(32)word
    and e_0 = word_subword abef (32,32):(32)word
    and f_0 = word_subword abef (0,32):(32)word
    and g_0 = word_subword cdgh (32,32):(32)word
    and h_0 = word_subword cdgh (0,32):(32)word
    and wk0 = word_subword wkval (0,32):(32)word
    and wk1 = word_subword wkval (32,32):(32)word in
    let t_0 = word_add (word_add (word_add (sha256_Ch e_0 f_0 g_0)
                                           (sha256_Sigma1 e_0))
                                 wk0) h_0 in
    let a_1 = word_add t_0 (word_add (sha256_Maj a_0 b_0 c_0)
                                     (sha256_Sigma0 a_0))
    and b_1 = a_0
    and c_1 = b_0
    and d_1 = c_0
    and e_1 = word_add t_0 d_0
    and f_1 = e_0
    and g_1 = f_0
    and h_1 = g_0 in
    let t_1 = word_add (word_add (word_add (sha256_Ch e_1 f_1 g_1)
                                           (sha256_Sigma1 e_1))
                                 wk1) h_1 in
    let a_2 = word_add t_1 (word_add (sha256_Maj a_1 b_1 c_1)
                                     (sha256_Sigma0 a_1))
    and b_2 = a_1
    and e_2 = word_add t_1 d_1
    and f_2 = e_1 in
    (word (val f_2 + val e_2 * 2 EXP 32 +
           val b_2 * 2 EXP 64 + val a_2 * 2 EXP 96) : int128)`;;

(* x86_SHA256RNDS2 is exactly (dest := sha_ni_rnds2 ...) s.                  *)
let X86_SHA256RNDS2_ALT = prove
 (`!dest src wk s.
     x86_SHA256RNDS2 dest src wk s =
       (dest := sha_ni_rnds2 (read dest s) (read src s) (read wk s)) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[x86_SHA256RNDS2; sha_ni_rnds2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* word(val a + val b * 2^32 + val c * 2^64 + val d * 2^96) is the 128-bit   *)
(* word obtained by splicing four 32-bit words; equivalently, word_join4.    *)
(* Needed to bring the sha_ni_rnds2 result into word_join4 form.             *)
(* ------------------------------------------------------------------------- *)

let WORD_VAL_JOIN4 = prove
 (`!a b c d:int32.
     (word (val a + val b * 2 EXP 32 + val c * 2 EXP 64 +
            val d * 2 EXP 96) : int128) =
     word_join4 a b c d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Two spec rounds of sha256_compress_round rewritten in the sum order the   *)
(* hardware semantics produce (h+...+T1, T1+T2 etc.).  This matches each     *)
(* individual lane of sha_ni_rnds2's word_join4 result without requiring     *)
(* WORD_RULE to descend into sha256_Ch / sha256_Sigma arguments.             *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_ROUND_2_HW_FORM = prove
 (`!a b c d e f g h wk0 wk1:int32.
     sha256_compress_round wk1 (word 0)
       (sha256_compress_round wk0 (word 0) [a;b;c;d;e;f;g;h]) =
     (let T0 = word_add
                (word_add (word_add (sha256_Ch e f g) (sha256_Sigma1 e))
                          wk0)
                h in
      let A1 = word_add T0
                (word_add (sha256_Maj a b c) (sha256_Sigma0 a)) in
      let E1 = word_add T0 d in
      let T1 = word_add
                (word_add (word_add (sha256_Ch E1 e f)
                                    (sha256_Sigma1 E1))
                          wk1)
                g in
      let A2 = word_add T1
                (word_add (sha256_Maj A1 a b) (sha256_Sigma0 A1)) in
      let E2 = word_add T1 c in
      [A2; A1; a; b; E2; E1; e; f])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha256_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `word_add d (word_add h (word_add (sha256_Sigma1 e)
                             (word_add (sha256_Ch (e:int32) f g)
                                       (wk0:int32)))) =
     word_add (word_add (word_add (word_add (sha256_Ch e f g)
                                            (sha256_Sigma1 e))
                                  wk0) h) d`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_add (word_add h (word_add (sha256_Sigma1 e)
                           (word_add (sha256_Ch (e:int32) f g) (wk0:int32))))
              (word_add (sha256_Sigma0 (a:int32)) (sha256_Maj a b c)) =
     word_add (word_add (word_add (word_add (sha256_Ch e f g)
                                            (sha256_Sigma1 e))
                                  wk0) h)
              (word_add (sha256_Maj a b c) (sha256_Sigma0 a))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* SHA256RNDS2_BRIDGE: the 2-round atomic bridge.                            *)
(*                                                                           *)
(* Given working state [a;b;c;d;e;f;g;h] packed as ABEF/CDGH and pre-added   *)
(* round-key+message values wk0 (for round 0) and wk1 (for round 1) packed   *)
(* in the low two lanes of wkval, one sha256rnds2 call advances two          *)
(* compression rounds and writes the new ABEF lane.                          *)
(*                                                                           *)
(* The top two lanes of wkval are ignored by the hardware (the spec uses     *)
(* word 0 for them), so we leave them free (wk2, wk3) in the statement.      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Pure-value forms of x86_SHA256MSG1 / x86_SHA256MSG2, mirroring the        *)
(* aesenc / x86_AESENC split.                                                *)
(* ------------------------------------------------------------------------- *)

let sha_ni_msg1 = new_definition
 `sha_ni_msg1 (x:int128) (y:int128) : int128 =
    let w0 = word_subword x (0,32):(32)word
    and w1 = word_subword x (32,32):(32)word
    and w2 = word_subword x (64,32):(32)word
    and w3 = word_subword x (96,32):(32)word
    and w4 = word_subword y (0,32):(32)word in
    (word (val (word_add w0 (sha256_sigma0 w1)) +
           val (word_add w1 (sha256_sigma0 w2)) * 2 EXP 32 +
           val (word_add w2 (sha256_sigma0 w3)) * 2 EXP 64 +
           val (word_add w3 (sha256_sigma0 w4)) * 2 EXP 96) : int128)`;;

let sha_ni_msg2 = new_definition
 `sha_ni_msg2 (x:int128) (y:int128) : int128 =
    let w14 = word_subword y (64,32):(32)word
    and w15 = word_subword y (96,32):(32)word in
    let w16 = word_add (word_subword x (0,32):(32)word)
                       (sha256_sigma1 w14) in
    let w17 = word_add (word_subword x (32,32):(32)word)
                       (sha256_sigma1 w15) in
    let w18 = word_add (word_subword x (64,32):(32)word)
                       (sha256_sigma1 w16) in
    let w19 = word_add (word_subword x (96,32):(32)word)
                       (sha256_sigma1 w17) in
    (word (val w16 + val w17 * 2 EXP 32 +
           val w18 * 2 EXP 64 + val w19 * 2 EXP 96) : int128)`;;

let X86_SHA256MSG1_ALT = prove
 (`!dest src s.
     x86_SHA256MSG1 dest src s =
       (dest := sha_ni_msg1 (read dest s) (read src s)) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[x86_SHA256MSG1; sha_ni_msg1] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;

let X86_SHA256MSG2_ALT = prove
 (`!dest src s.
     x86_SHA256MSG2 dest src s =
       (dest := sha_ni_msg2 (read dest s) (read src s)) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[x86_SHA256MSG2; sha_ni_msg2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* SHA256MSG1_BRIDGE: sha256msg1 applied to two vectors of message-schedule  *)
(* words produces w_i + sigma0(w_{i+1}) for each of the four lanes.  Only    *)
(* the lowest 32-bit lane of the second operand is consumed.                 *)
(* ------------------------------------------------------------------------- *)

let SHA256MSG1_BRIDGE = prove
 (`!w0 w1 w2 w3 w4 w5 w6 w7:int32.
     sha_ni_msg1 (word_join4 w0 w1 w2 w3) (word_join4 w4 w5 w6 w7) =
     word_join4 (word_add w0 (sha256_sigma0 w1))
                (word_add w1 (sha256_sigma0 w2))
                (word_add w2 (sha256_sigma0 w3))
                (word_add w3 (sha256_sigma0 w4))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha_ni_msg1; WORD_JOIN4_SUBWORD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_VAL_JOIN4]);;

(* ------------------------------------------------------------------------- *)
(* SHA256MSG2_BRIDGE: sha256msg2 partially completes the message schedule.  *)
(*                                                                           *)
(* Given x = [x0;x1;x2;x3] (typically x_i = w_i + sigma0(w_{i+1}) + w_{i+9}  *)
(* from a prior sha256msg1+paddd+palignr), and y = [_;_;w14;w15] (the top    *)
(* two lanes of the previous message block), sha256msg2 writes               *)
(*   w16 = x0 + sigma1(w14)                                                  *)
(*   w17 = x1 + sigma1(w15)                                                  *)
(*   w18 = x2 + sigma1(w16)  -- note the inner chain                         *)
(*   w19 = x3 + sigma1(w17)                                                  *)
(* ------------------------------------------------------------------------- *)

let SHA256MSG2_BRIDGE = prove
 (`!x0 x1 x2 x3 y0 y1 w14 w15:int32.
     sha_ni_msg2 (word_join4 x0 x1 x2 x3) (word_join4 y0 y1 w14 w15) =
     (let w16 = word_add x0 (sha256_sigma1 w14) in
      let w17 = word_add x1 (sha256_sigma1 w15) in
      let w18 = word_add x2 (sha256_sigma1 w16) in
      let w19 = word_add x3 (sha256_sigma1 w17) in
      word_join4 w16 w17 w18 w19)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha_ni_msg2; WORD_JOIN4_SUBWORD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_VAL_JOIN4]);;

let SHA256RNDS2_BRIDGE = prove
 (`!a b c d e f g h wk0 wk1 wk2 wk3:int32.
    let s1 = sha256_compress_round wk0 (word 0) [a;b;c;d;e;f;g;h] in
    let s2 = sha256_compress_round wk1 (word 0) s1 in
    sha_ni_rnds2 (CDGH_PACK c d g h) (ABEF_PACK a b e f)
                 (word_join4 wk0 wk1 wk2 wk3) =
    ABEF_PACK (EL 0 s2) (EL 1 s2) (EL 4 s2) (EL 5 s2)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_2_HW_FORM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[sha_ni_rnds2; ABEF_PACK; CDGH_PACK; WORD_JOIN4_SUBWORD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_VAL_JOIN4; WORD_JOIN4_EQ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE);;

(* Flattened (let-free) rewrite form, easier to use as a REWRITE_TAC rule.   *)
let SHA256RNDS2_BRIDGE_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256RNDS2_BRIDGE;;

(* ------------------------------------------------------------------------- *)
(* The second sha256rnds2 call in a 4-round group reuses the OLD ABEF lane   *)
(* (saved in xmm1 in the asm) as its "CDGH" input.  After the first rnds2   *)
(* call advances two rounds, the spec's new (c,d,g,h) = old (a,b,e,f), so    *)
(* the CDGH_PACK of state_{i+2} and the ABEF_PACK of state_i coincide at     *)
(* the bit level.  This is a lane-order equality.                            *)
(* ------------------------------------------------------------------------- *)

let CDGH_EQ_ABEF = prove
 (`!a b e f:int32. CDGH_PACK a b e f = ABEF_PACK a b e f`,
  REWRITE_TAC[CDGH_PACK; ABEF_PACK]);;

(* After two rounds, CDGH lane contents (slots 2,3,6,7 of the state list)    *)
(* equal the initial ABEF contents (slots 0,1,4,5).                          *)
let CDGH_AFTER_2_IS_ABEF = prove
 (`!a b c d e f g h kw0 kw1:int32.
     let s2 = sha256_compress_round kw1 (word 0)
               (sha256_compress_round kw0 (word 0) [a;b;c;d;e;f;g;h]) in
     CDGH_PACK (EL 2 s2) (EL 3 s2) (EL 6 s2) (EL 7 s2) = ABEF_PACK a b e f`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_2_HW_FORM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[CDGH_EQ_ABEF]);;

(* Flattened form, suitable for REWRITE_TAC / MP_TAC.                        *)
let CDGH_AFTER_2_IS_ABEF_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV) CDGH_AFTER_2_IS_ABEF;;

(* ------------------------------------------------------------------------- *)
(* LENGTH preservation across one sha256_compress_round.                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA256_COMPRESS_ROUND = prove
 (`!K W state:int32 list.
     LENGTH state = 8 ==> LENGTH(sha256_compress_round K W state) = 8`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[sha256_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* List decomposition lemma: any 8-element int32 list equals the explicit    *)
(* [EL 0 s; ...; EL 7 s] form.  Used below to re-fold the argument of an    *)
(* outer sha256_compress_round after applying SHA256RNDS2_BRIDGE to an inner *)
(* 2-round composition.                                                      *)
(* ------------------------------------------------------------------------- *)

let EL_EXPAND_8 = prove
 (`!s:int32 list.
     LENGTH s = 8 ==>
     [EL 0 s; EL 1 s; EL 2 s; EL 3 s;
      EL 4 s; EL 5 s; EL 6 s; EL 7 s] = s`,
  GEN_TAC THEN
  REWRITE_TAC[num_CONV `8`; num_CONV `7`; num_CONV `6`;
              num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`;
              LENGTH_EQ_CONS; LENGTH_EQ_NIL; NOT_CONS_NIL; CONS_11] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EL; HD; TL]);;

(* ========================================================================= *)
(* Phase 4: Per-group 4-round bridge.                                        *)
(*                                                                           *)
(* A round-group consists of 2 sha256rnds2 calls advancing 4 compression     *)
(* rounds.  Concretely:                                                      *)
(*                                                                           *)
(*   call 1 (asm `sha256rnds2 xmm2, xmm1`):                                  *)
(*     dest (cdgh slot) = xmm2 = CDGH_PACK (C,D,G,H) of state_i              *)
(*     src  (abef slot) = xmm1 = ABEF_PACK (A,B,E,F) of state_i              *)
(*     wk                       = word_join4 kw0 kw1 _ _                     *)
(*     → xmm2 := ABEF_PACK of state_{i+2}                                    *)
(*                                                                           *)
(*   call 2 (asm `sha256rnds2 xmm1, xmm2`):                                  *)
(*     dest (cdgh slot) = xmm1 = ABEF_PACK of state_i, reinterpreted as      *)
(*                                CDGH_PACK of state_{i+2}                   *)
(*                                (equal by CDGH_AFTER_2_IS_ABEF / lane eq)  *)
(*     src  (abef slot) = xmm2 = ABEF_PACK of state_{i+2}                    *)
(*     wk                       = word_join4 kw2 kw3 _ _                     *)
(*     → xmm1 := ABEF_PACK of state_{i+4}                                    *)
(* ------------------------------------------------------------------------- *)

let GROUP_BRIDGE_H = prove
 (`!A B C D E FF G H kw0 kw1 kw2 kw3:int32.
     let s2 = sha256_compress_round kw1 (word 0)
                (sha256_compress_round kw0 (word 0)
                   [A;B;C;D;E;FF;G;H]) in
     let s4 = sha256_compress_round kw3 (word 0)
                (sha256_compress_round kw2 (word 0) s2) in
     sha_ni_rnds2
       (ABEF_PACK A B E FF)
       (sha_ni_rnds2 (CDGH_PACK C D G H) (ABEF_PACK A B E FF)
                     (word_join4 kw0 kw1 (word 0) (word 0)))
       (word_join4 kw2 kw3 (word 0) (word 0)) =
     ABEF_PACK (EL 0 s4) (EL 1 s4) (EL 4 s4) (EL 5 s4)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256RNDS2_BRIDGE_FLAT] THEN
  MP_TAC(ISPECL
    [`A:int32`;`B:int32`;`C:int32`;`D:int32`;
     `E:int32`;`FF:int32`;`G:int32`;`H:int32`;
     `kw0:int32`;`kw1:int32`] CDGH_AFTER_2_IS_ABEF_FLAT) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
  REWRITE_TAC[SHA256RNDS2_BRIDGE_FLAT] THEN
  SUBGOAL_THEN
    `LENGTH (sha256_compress_round kw1 (word 0)
              (sha256_compress_round kw0 (word 0)
                 [A;B;C;D;(E:int32);FF;G;H])) = 8`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_SHA256_COMPRESS_ROUND THEN
    MATCH_MP_TAC LENGTH_SHA256_COMPRESS_ROUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP EL_EXPAND_8 th]) THEN
  REFL_TAC);;

(* Flattened form for use as a rewrite rule. *)
let GROUP_BRIDGE_H_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV) GROUP_BRIDGE_H;;

(* ------------------------------------------------------------------------- *)
(* The "H2" view: after the second sha256rnds2 of a group, xmm2 holds        *)
(* the INTERMEDIATE ABEF (= ABEF_PACK of state_{i+2}) — which at the bit     *)
(* level coincides with CDGH_PACK of state_{i+4} (by CDGH_AFTER_2_IS_ABEF    *)
(* applied to rounds 2-3 of the group starting from state_{i+2}).            *)
(*                                                                           *)
(* The CUT_POINT tactic uses both H and H2 to rewrite reads of xmm1 / xmm2   *)
(* at group boundaries.                                                      *)
(* ------------------------------------------------------------------------- *)

let GROUP_BRIDGE_H2 = prove
 (`!A B C D E FF G H kw0 kw1:int32.
     let s2 = sha256_compress_round kw1 (word 0)
                (sha256_compress_round kw0 (word 0)
                   [A;B;C;D;E;FF;G;H]) in
     sha_ni_rnds2 (CDGH_PACK C D G H) (ABEF_PACK A B E FF)
                  (word_join4 kw0 kw1 (word 0) (word 0)) =
     ABEF_PACK (EL 0 s2) (EL 1 s2) (EL 4 s2) (EL 5 s2)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256RNDS2_BRIDGE_FLAT]);;

let GROUP_BRIDGE_H2_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV) GROUP_BRIDGE_H2;;
