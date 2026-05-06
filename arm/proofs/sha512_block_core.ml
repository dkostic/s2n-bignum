(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-512 single-block compression core: 80 rounds + state add-back.        *)
(*                                                                           *)
(* Proves correctness of a straight-line ARM64 implementation that uses      *)
(* SHA512H/SHA512H2/SHA512SU0/SHA512SU1 hardware instructions for 40 round  *)
(* groups (2 rounds each = 80 total), with final state add-back.             *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q0 = word_join b a, Q1 = word_join d c,                                *)
(*   Q2 = word_join f e, Q3 = word_join h g                                 *)
(*   Q16..Q23 = schedule pairs, Q(16+j) = word_join w(2j+1) w(2j)           *)
(*              (already byte-reversed from memory order)                    *)
(*   X3 = pointer to K table, 80 x int64 = 640 bytes                        *)
(*                                                                           *)
(* Output: Q0..Q3 = final state (compressed + initial add-back).             *)
(*                                                                           *)
(* Register rotation follows aws-lc's 5-phase cycle on v0..v4; after 40      *)
(* groups (40 mod 5 = 0) the state is back in v0..v3 ready for add-back.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha512_bridge.ml";;

(* ========================================================================= *)
(* Helper lemmas / conversions (SHA-256 analogues).                          *)
(* ========================================================================= *)

let EL_RECONSTRUCT_512 = end_itlist CONJ (List.map (fun n ->
  prove(subst[mk_small_numeral n, `n:num`]
    `!s:int64 list. EL n [EL 0 s; EL 1 s; EL 2 s; EL 3 s;
      EL 4 s; EL 5 s; EL 6 s; EL 7 s] = EL n s`,
    GEN_TAC THEN CONV_TAC(LAND_CONV EL_CONV) THEN REFL_TAC)) (0--7));;

let SHA512_COMPRESS_ROUND_EL_LIST = prove
 (`!K W s:int64 list.
    sha512_compress_round K W [EL 0 s; EL 1 s; EL 2 s; EL 3 s;
      EL 4 s; EL 5 s; EL 6 s; EL 7 s] = sha512_compress_round K W s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha512_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[EL_RECONSTRUCT_512]);;

(* Unroll sha512_compress n W state to n nested sha512_compress_round calls. *)
let rec SHA512_COMPRESS_UNROLL_CONV tm =
  let n_tm = rand(rator(rator tm)) in
  if n_tm = `0` then REWRITE_CONV[sha512_compress] tm
  else
    let n = dest_small_numeral n_tm in
    let arith_th = ARITH_RULE
      (mk_eq(n_tm, mk_comb(mk_comb(`(+)`, mk_small_numeral(n-1)), `1`))) in
    let step1 = ONCE_REWRITE_CONV[arith_th] tm in
    let step2 = CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[sha512_compress])) step1 in
    CONV_RULE(RAND_CONV(RAND_CONV SHA512_COMPRESS_UNROLL_CONV)) step2;;

(* ========================================================================= *)
(* Per-round-group bridges (40 of each, covering 2 rounds per group).        *)
(*                                                                           *)
(* GROUP_BRIDGE_H512.(i): the fused H+H2 bridge specialized to round group  *)
(* i. Expresses the new {b',a'} pack as word_join (EL 1 st) (EL 0 st) where  *)
(* st = sha512_compress (2*(i+1)) W H.                                       *)
(*                                                                           *)
(* GROUP_BRIDGE_MID.(i): the new {d',c'} pack (= v_MID reg in the hw).      *)
(* Expresses it as word_join (EL 5 st) (EL 4 st).                            *)
(* ========================================================================= *)

let mk_group_bridge_h512 i =
  let base_s = mk_small_numeral(2 * i) and
      target_s = mk_small_numeral(2 * (i + 1)) in
  let i0 = mk_small_numeral(2*i) and i1 = mk_small_numeral(2*i+1) in
  prove(list_mk_forall([`W:int64 list`; `H:int64 list`],
         subst [base_s, `b:num`; target_s, `t:num`;
                i0, `i0:num`; i1, `i1:num`]
    `let sb = sha512_compress b W H in let st = sha512_compress t W H in
     (word_join:int64->int64->int128) (EL 1 st) (EL 0 st) =
     sha512h2
      (sha512h
        ((word_join:int64->int64->int128)
          (word_add (EL 7 sb) (word_add (EL i0 sha512_K) (EL i0 W)))
          (word_add (EL 6 sb) (word_add (EL i1 sha512_K) (EL i1 W))))
        ((word_join:int64->int64->int128) (EL 6 sb) (EL 5 sb))
        ((word_join:int64->int64->int128) (EL 4 sb) (EL 3 sb)))
      ((word_join:int64->int64->int128) (EL 3 sb) (EL 2 sb))
      ((word_join:int64->int64->int128) (EL 1 sb) (EL 0 sb))`),
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA512_H_H2_BRIDGE_FLAT] THEN
    REWRITE_TAC[SHA512_COMPRESS_ROUND_PREADD; SHA512_COMPRESS_ROUND_EL_LIST] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA512_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha512_compress n W (state:int64 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA512_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha512_compress n W (state:int64 list)`))))) THEN REFL_TAC);;

let mk_group_bridge_mid i =
  let base_s = mk_small_numeral(2 * i) and
      target_s = mk_small_numeral(2 * (i + 1)) in
  let i0 = mk_small_numeral(2*i) and i1 = mk_small_numeral(2*i+1) in
  prove(list_mk_forall([`W:int64 list`; `H:int64 list`],
         subst [base_s, `b:num`; target_s, `t:num`;
                i0, `i0:num`; i1, `i1:num`]
    `let sb = sha512_compress b W H in let st = sha512_compress t W H in
     (word_join:int64->int64->int128) (EL 5 st) (EL 4 st) =
     (word_join:int64->int64->int128)
      (word_add (EL 3 sb)
        (word_subword
          (sha512h ((word_join:int64->int64->int128)
                    (word_add (EL 7 sb) (word_add (EL i0 sha512_K) (EL i0 W)))
                    (word_add (EL 6 sb) (word_add (EL i1 sha512_K) (EL i1 W))))
                   ((word_join:int64->int64->int128) (EL 6 sb) (EL 5 sb))
                   ((word_join:int64->int64->int128) (EL 4 sb) (EL 3 sb))) (64,64)))
      (word_add (EL 2 sb)
        (word_subword
          (sha512h ((word_join:int64->int64->int128)
                    (word_add (EL 7 sb) (word_add (EL i0 sha512_K) (EL i0 W)))
                    (word_add (EL 6 sb) (word_add (EL i1 sha512_K) (EL i1 W))))
                   ((word_join:int64->int64->int128) (EL 6 sb) (EL 5 sb))
                   ((word_join:int64->int64->int128) (EL 4 sb) (EL 3 sb))) (0,64)))`),
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV
      [CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPECL [`EL 0 (sha512_compress b W H:int64 list)`;
                `EL 1 (sha512_compress b W H:int64 list)`;
                `EL 2 (sha512_compress b W H:int64 list)`;
                `EL 3 (sha512_compress b W H:int64 list)`;
                `EL 4 (sha512_compress b W H:int64 list)`;
                `EL 5 (sha512_compress b W H:int64 list)`;
                `EL 6 (sha512_compress b W H:int64 list)`;
                `EL 7 (sha512_compress b W H:int64 list)`;
                subst [i0,`i:num`] `word_add (EL i (sha512_K:int64 list)) (EL i W):int64`;
                subst [i1,`i:num`] `word_add (EL i (sha512_K:int64 list)) (EL i W):int64`]
          SHA512_MID_BRIDGE)] THEN
    REWRITE_TAC[SHA512_COMPRESS_ROUND_PREADD; SHA512_COMPRESS_ROUND_EL_LIST] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA512_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha512_compress n W (state:int64 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA512_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha512_compress n W (state:int64 list)`))))) THEN REFL_TAC);;

let GROUP_BRIDGE_H512 = Array.init 40 mk_group_bridge_h512;;
let GROUP_BRIDGE_MID = Array.init 40 mk_group_bridge_mid;;

(* ========================================================================= *)
(* Schedule word extraction: EL k (sha512_message_schedule 64 M) for k<80.  *)
(* Structurally identical to SHA-256's EL_W_ALL_LIST, with 48→64 and         *)
(* list length 16 unchanged.                                                 *)
(* ========================================================================= *)

let w_abbrev_512 = ASSUME
  `sha512_message_schedule 64
   [w0:int64;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W`;;

let m_list_512 =
  `[w0:int64;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]`;;

let len_m_512 = prove(mk_eq(mk_comb(`LENGTH:int64 list->num`, m_list_512), `16`),
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let EL_W_ALL_LIST_512 =
  let el_w_acc = ref (List.map (fun k ->
    let th = SPECL [`64`; m_list_512; mk_small_numeral k] SHA512_SCHEDULE_PREFIX in
    let th1 = MP th (EQT_ELIM(REWRITE_CONV[len_m_512; ARITH] (lhand(concl th)))) in
    let th2 = CONV_RULE(RAND_CONV EL_CONV) th1 in
    CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev_512))) th2) (0--15)) in
  for n = 0 to 63 do
    let th = SPECL [mk_small_numeral n; m_list_512] SHA512_W_EXTEND in
    let cond_thm = prove(lhand(concl th), REWRITE_TAC[len_m_512] THEN ARITH_TAC) in
    let th2 = MP th cond_thm in
    let th3 = CONV_RULE(RAND_CONV(TOP_DEPTH_CONV let_CONV)) th2 in
    let th4 = CONV_RULE(RAND_CONV(DEPTH_CONV NUM_ADD_CONV)) th3 in
    let prefix_rules = List.init 16 (fun k ->
      let sth = SPECL [mk_small_numeral n; m_list_512; mk_small_numeral k]
        SHA512_SCHEDULE_PREFIX in
      try MP sth (EQT_ELIM(REWRITE_CONV[len_m_512; ARITH] (lhand(concl sth))))
      with _ -> TRUTH) in
    let th5 = REWRITE_RULE prefix_rules th4 in
    let th6 = CONV_RULE(RAND_CONV(DEPTH_CONV EL_CONV)) th5 in
    let mono_rules = List.init (min n 64) (fun i ->
      let k = i + 16 in
      if k < n + 16 then
        let sth = SPECL [mk_small_numeral n; `64`; m_list_512; mk_small_numeral k]
          SHA512_SCHEDULE_MONO in
        try let cond_thm = prove(lhand(concl sth),
              REWRITE_TAC[len_m_512] THEN ARITH_TAC) in
            CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV w_abbrev_512)))
              (GSYM(MP sth cond_thm))
        with _ -> TRUTH
      else TRUTH) in
    let th7 = REWRITE_RULE mono_rules th6 in
    let th8 = REWRITE_RULE !el_w_acc th7 in
    let th9 = CONV_RULE(LAND_CONV(REWRITE_CONV[ARITH])) th8 in
    let th10 = CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV w_abbrev_512))) th9 in
    el_w_acc := !el_w_acc @ [th10]
  done;
  !el_w_acc;;

(* ========================================================================= *)
(* Shift lemmas: sha512_compress_round and sha512_compress at LENGTH 8 shift *)
(* positions 1..3 and 5..7 to positions 0..2 and 4..6 respectively.          *)
(* These express the fact that one round of compression pushes state letters *)
(* down by one position, keeping the algorithm correct while hardware layout *)
(* stays in place.                                                           *)
(* ========================================================================= *)

let LEN8_DESTRUCTURE = prove
 (`!l:int64 list. LENGTH l = 8 ==>
    ?x0 x1 x2 x3 x4 x5 x6 x7. l = [x0;x1;x2;x3;x4;x5;x6;x7]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `8 = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))`] THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let SHA512_COMPRESS_ROUND_SHIFT = prove
 (`!K W state:int64 list. LENGTH state = 8 ==>
    EL 1 (sha512_compress_round K W state) = EL 0 state /\
    EL 2 (sha512_compress_round K W state) = EL 1 state /\
    EL 3 (sha512_compress_round K W state) = EL 2 state /\
    EL 5 (sha512_compress_round K W state) = EL 4 state /\
    EL 6 (sha512_compress_round K W state) = EL 5 state /\
    EL 7 (sha512_compress_round K W state) = EL 6 state`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LEN8_DESTRUCTURE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[sha512_compress_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[EL; HD; TL] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

let SHA512_COMPRESS_SHIFT = prove
 (`!n W state:int64 list. LENGTH state = 8 ==>
    EL 1 (sha512_compress (n+1) W state) = EL 0 (sha512_compress n W state) /\
    EL 2 (sha512_compress (n+1) W state) = EL 1 (sha512_compress n W state) /\
    EL 3 (sha512_compress (n+1) W state) = EL 2 (sha512_compress n W state) /\
    EL 5 (sha512_compress (n+1) W state) = EL 4 (sha512_compress n W state) /\
    EL 6 (sha512_compress (n+1) W state) = EL 5 (sha512_compress n W state) /\
    EL 7 (sha512_compress (n+1) W state) = EL 6 (sha512_compress n W state)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (sha512_compress n W (state:int64 list)) = 8` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_SHA512_COMPRESS THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[SHA512_COMPRESS_ROUND_SHIFT; sha512_compress]]);;

let SHA512_COMPRESS_SHIFT2 = prove
 (`!n W state:int64 list. LENGTH state = 8 ==>
    EL 2 (sha512_compress (n+2) W state) = EL 0 (sha512_compress n W state) /\
    EL 3 (sha512_compress (n+2) W state) = EL 1 (sha512_compress n W state) /\
    EL 6 (sha512_compress (n+2) W state) = EL 4 (sha512_compress n W state) /\
    EL 7 (sha512_compress (n+2) W state) = EL 5 (sha512_compress n W state)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n+1`; `W:int64 list`; `state:int64 list`] SHA512_COMPRESS_SHIFT) THEN
  MP_TAC(SPECL [`n:num`; `W:int64 list`; `state:int64 list`] SHA512_COMPRESS_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(n+1)+1 = n+2`] THEN
  MESON_TAC[]);;

(* Specialized forms for H = [a;b;c;d;e;f;g;h]: SHIFT2 with LENGTH hypothesis
   discharged, and EL-to-raw for compress 2. *)

let EL_COMPRESS_SHIFT2_H8 = prove
 (`!n W a b c d e f g h:int64.
    EL 2 (sha512_compress (n+2) W [a;b;c;d;e;f;g;h]) =
     EL 0 (sha512_compress n W [a;b;c;d;e;f;g;h]) /\
    EL 3 (sha512_compress (n+2) W [a;b;c;d;e;f;g;h]) =
     EL 1 (sha512_compress n W [a;b;c;d;e;f;g;h]) /\
    EL 6 (sha512_compress (n+2) W [a;b;c;d;e;f;g;h]) =
     EL 4 (sha512_compress n W [a;b;c;d;e;f;g;h]) /\
    EL 7 (sha512_compress (n+2) W [a;b;c;d;e;f;g;h]) =
     EL 5 (sha512_compress n W [a;b;c;d;e;f;g;h])`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC SHA512_COMPRESS_SHIFT2 THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let EL_COMPRESS_2_RAW = prove
 (`!W a b c d e f g h:int64.
    EL 2 (sha512_compress 2 W [a;b;c;d;e;f;g;h]) = a /\
    EL 3 (sha512_compress 2 W [a;b;c;d;e;f;g;h]) = b /\
    EL 6 (sha512_compress 2 W [a;b;c;d;e;f;g;h]) = e /\
    EL 7 (sha512_compress 2 W [a;b;c;d;e;f;g;h]) = f`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`0`; `W:int64 list`; `a:int64`; `b:int64`; `c:int64`;
                `d:int64`; `e:int64`; `f:int64`; `g:int64`; `h:int64`]
    EL_COMPRESS_SHIFT2_H8) THEN
  REWRITE_TAC[ARITH_RULE `0+2 = 2`; sha512_compress] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* Machine code and execution rule.                                          *)
(* ========================================================================= *)

let sha512_block_core_mc = define_from_elf "sha512_block_core_mc"
  (file_on_path !load_path "arm/sha2/sha512_block_core.o");;

let EXEC = ARM_MK_EXEC_RULE sha512_block_core_mc;;

(* ========================================================================= *)
(* ADD_SIMP_RULE_512: normalize SIMD outputs of ADD V.2D / EXT V.16B #8       *)
(* after symbolic execution of each round group.                             *)
(* ========================================================================= *)

let ADD_SIMP_RULE_512 = REWRITE_RULE[WORD_JOIN_64_HI_LO; WORD_JOIN_MID64];;

(* ========================================================================= *)
(* Phase register arrays for aws-lc's 5-phase cycle.                          *)
(*   Phase p (0..4): BA, DC, FE, HG, RES, MID are v-register indices.         *)
(*   HG coincides with RES (destination of sha512h/h2).                       *)
(*   Group i has phase (i mod 5).                                             *)
(* ========================================================================= *)

let phase_res_arr_512 = [|3;2;4;1;0|];;   (* RES / HG: new {b,a} pack reg *)
let phase_mid_arr_512 = [|4;1;0;3;2|];;   (* MID:      new {d,c} pack reg *)

(* ========================================================================= *)
(* CUT_POINT_TAC_512 for group i at state s_name:                             *)
(*   Assert 2 cut subgoals (read Q(RES) s = compress-form, Q(MID) = ... ),    *)
(*   prove each via ASM_REWRITE with the fused H+H2 / MID bridge +            *)
(*   EL_COMPRESS_2_RAW + SHIFT2 + EL_W_ALL_LIST_512.                          *)
(*   Then discard residual sha512h/sha512h2 assumptions, and for groups 0..31 *)
(*   apply SHA512SU_BRIDGE_FLAT to any sha512su1 term.                        *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Opaque-letter abbreviation helper: `a<i+1>`, `b<i+1>`, `e<i+1>`, `f<i+1>`  *)
(* stand for EL 0/1/4/5 of sha512_compress 2(i+1) W [a;b;c;d;e;f;g;h].        *)
(*                                                                           *)
(* Reason: without abbreviations, the Q-register cut hypotheses that         *)
(* ARM_STEPS_TAC propagates through every subsequent instruction contain     *)
(* `sha512_compress 2(i+1) W [a;..;h]` sub-terms. Per-instruction simulation *)
(* time grows super-linearly with the compress index as the matcher has to   *)
(* re-derive larger and larger terms. By abbreviating positions 0/1/4/5 of   *)
(* each cut as letters, ARM_STEPS sees only `word_join b_{i+1} a_{i+1}` etc. *)
(*                                                                           *)
(* positions 2/3/6/7 of compress 2(i+1) W H are not independent; they equal  *)
(* positions 0/1/4/5 of compress 2i W H (the previous cut's letters) via     *)
(* SHIFT2. The CUT_SUBGOAL_TAC below unfolds the abbreviations to derive the *)
(* letter equalities needed by the next cut's bridge.                        *)
(* ========================================================================= *)

let cut_letter_name k i = k ^ string_of_int(i+1);;

(* Build `read Q s = word_join <hi> <lo>` where <hi>,<lo> are either the      *)
(* concrete letters `a..h` (i=0) or the abbreviated letters a<i+1>,b<i+1>, .. *)
let mk_q_cut_letter q sname k_hi k_lo i =
  let hi = mk_var(cut_letter_name k_hi i,`:int64`) in
  let lo = mk_var(cut_letter_name k_lo i,`:int64`) in
  let q_tm = mk_comb(mk_comb(
    `read:(armstate,int128)component->armstate->int128`, q),
    mk_var(sname,`:armstate`)) in
  mk_eq(q_tm,
    list_mk_icomb "word_join" [hi;lo]);;

(* Abbreviate one EL position of sha512_compress 2(i+1) W [a;b;c;d;e;f;g;h]
   as a fresh int64 letter name k_name^(string_of_int(i+1)). *)
let abbrev_compress_el_tac i k_name pos =
  let tgt_n = 2*(i+1) in
  let tgt = mk_small_numeral tgt_n in
  let pos_tm = mk_small_numeral pos in
  let letter = cut_letter_name k_name i in
  let rhs = subst
    [tgt,`t:num`; pos_tm,`p:num`]
    `EL p (sha512_compress t W [a:int64;b;c;d;e;f;g;h])` in
  let eq_tm = mk_eq(mk_var(letter,`:int64`), rhs) in
  ABBREV_TAC eq_tm;;

let CUT_POINT_TAC_512 i sname =
  let p = i mod 5 in
  let q_res = mk_const("Q" ^ string_of_int phase_res_arr_512.(p),[]) in
  let q_mid = mk_const("Q" ^ string_of_int phase_mid_arr_512.(p),[]) in
  let bridge_h = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int64 list`; `[a:int64;b;c;d;e;f;g;h]`] GROUP_BRIDGE_H512.(i)) in
  let bridge_mid = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int64 list`; `[a:int64;b;c;d;e;f;g;h]`] GROUP_BRIDGE_MID.(i)) in
  (* Shift lemma: for group i>=1, specialise EL_COMPRESS_SHIFT2_H8 at n=2*(i-1)
     so EL 2/3/6/7 (compress 2i W H) = EL 0/1/4/5 (compress 2(i-1) W H).
     For i=0 the bridge bottoms out at `compress 0 W H`, which unfolds via
     CONJUNCT1 sha512_compress + EL_CONV below. *)
  let shift2_thm =
    if i = 0 then TRUTH
    else CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
           (SPECL [mk_small_numeral(2*(i-1));
                   `W:int64 list`;
                   `a:int64`;`b:int64`;`c:int64`;`d:int64`;
                   `e:int64`;`f:int64`;`g:int64`;`h:int64`]
             EL_COMPRESS_SHIFT2_H8) in
  let el_w_local = [List.nth EL_W_ALL_LIST_512 (2*i);
                    List.nth EL_W_ALL_LIST_512 (2*i+1)] in
  (* Full-compress-form cut statements (what the bridge produces). *)
  let target_n = 2 * (i + 1) in
  let target = mk_small_numeral target_n in
  let q_res_tm_full = subst [sname, `s:armstate`; target, `t:num`]
    (mk_eq(mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`, q_res),
                   `s:armstate`),
           `(word_join:int64->int64->int128)
              (EL 1 (sha512_compress t W [a:int64;b;c;d;e;f;g;h]:int64 list))
              (EL 0 (sha512_compress t W [a;b;c;d;e;f;g;h]))`)) in
  let q_mid_tm_full = subst [sname, `s:armstate`; target, `t:num`]
    (mk_eq(mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`, q_mid),
                   `s:armstate`),
           `(word_join:int64->int64->int128)
              (EL 5 (sha512_compress t W [a:int64;b;c;d;e;f;g;h]:int64 list))
              (EL 4 (sha512_compress t W [a;b;c;d;e;f;g;h]))`)) in
  let CUT_SUBGOAL_TAC bridge =
    ASM_REWRITE_TAC[bridge] THEN
    REWRITE_TAC[shift2_thm] THEN
    REWRITE_TAC[CONJUNCT1 sha512_compress] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC el_w_local THEN
    REFL_TAC in
  (* Introduce the compress-form cuts, then abbreviate positions 0/1/4/5. *)
  SUBGOAL_THEN q_res_tm_full ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h; ALL_TAC] THEN
  SUBGOAL_THEN q_mid_tm_full ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_mid; ALL_TAC] THEN
  (* Discard residual sha512h/sha512h2 raw hypotheses (including the one the
     cut just replaced). *)
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let n = fst(dest_const t) in n = "sha512h" || n = "sha512h2"
      with _ -> false)) (concl th)))) THEN
  (* Abbreviate positions 0,1,4,5 of compress 2(i+1) W [a;b;c;d;e;f;g;h] so
     ARM_STEPS_TAC sees opaque letters on the Q cut hypotheses. Order: 0/1
     first, then 4/5 (ABBREV_TAC rewrites RHS->LHS in hyps). *)
  abbrev_compress_el_tac i "a" 0 THEN
  abbrev_compress_el_tac i "b" 1 THEN
  abbrev_compress_el_tac i "e" 4 THEN
  abbrev_compress_el_tac i "f" 5 THEN
  (if i < 32 then
    RULE_ASSUM_TAC(fun th ->
      if can (find_term (fun t ->
          try fst(dest_const t) = "sha512su1" with _ -> false)) (concl th)
      then REWRITE_RULE[SHA512SU_BRIDGE_FLAT] th
      else th)
   else ALL_TAC);;

(* ========================================================================= *)
(* Correctness theorem (Phase D work in progress — body is CHEAT_TAC).      *)
(* ========================================================================= *)

let SHA512_BLOCK_CORE_CORRECT = prove
 (`!(a:int64) b c d (e:int64) f g h
    (w0:int64) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    kptr pc ret_pc.
    nonoverlapping (kptr, 640) (word pc, LENGTH sha512_block_core_mc)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha512_block_core_mc /\
          read PC s = word pc /\
          read X30 s = word ret_pc /\
          read X3 s = kptr /\
          read Q0 s = (word_join:int64->int64->int128) b a /\
          read Q1 s = (word_join:int64->int64->int128) d c /\
          read Q2 s = (word_join:int64->int64->int128) f e /\
          read Q3 s = (word_join:int64->int64->int128) h g /\
          read Q16 s = (word_join:int64->int64->int128) w1 w0 /\
          read Q17 s = (word_join:int64->int64->int128) w3 w2 /\
          read Q18 s = (word_join:int64->int64->int128) w5 w4 /\
          read Q19 s = (word_join:int64->int64->int128) w7 w6 /\
          read Q20 s = (word_join:int64->int64->int128) w9 w8 /\
          read Q21 s = (word_join:int64->int64->int128) w11 w10 /\
          read Q22 s = (word_join:int64->int64->int128) w13 w12 /\
          read Q23 s = (word_join:int64->int64->int128) w15 w14 /\
          (!i. i < 40 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
            (word_join:int64->int64->int128)
              (EL (2 * i + 1) sha512_K) (EL (2 * i) sha512_K)))
     (\s. read PC s = word ret_pc /\
          (let M = [w0;w1;w2;w3;w4;w5;w6;w7;
                    w8;w9;w10;w11;w12;w13;w14;w15] in
           let H = [a;b;c;d;e;f;g;h] in
           let result = sha512_block M H in
           read Q0 s = (word_join:int64->int64->int128)
                         (EL 1 result) (EL 0 result) /\
           read Q1 s = (word_join:int64->int64->int128)
                         (EL 3 result) (EL 2 result) /\
           read Q2 s = (word_join:int64->int64->int128)
                         (EL 5 result) (EL 4 result) /\
           read Q3 s = (word_join:int64->int64->int128)
                         (EL 7 result) (EL 6 result)))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                 Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24;
                 Q28; Q29; Q30; Q31] ,,
      MAYCHANGE [events])`,
  CHEAT_TAC);;
