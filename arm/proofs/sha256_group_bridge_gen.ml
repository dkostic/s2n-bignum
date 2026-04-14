(* Generate per-round-group bridge lemmas: sha256_compress -> sha256h *)
(* Requires sha256_block_core_setup.ml to be loaded *)

let SHA256_COMPRESS_ROUND_EL_LIST = prove(
 `!K W s:int32 list.
   sha256_compress_round K W [EL 0 s; EL 1 s; EL 2 s; EL 3 s; EL 4 s; EL 5 s; EL 6 s; EL 7 s] =
   sha256_compress_round K W s`,
 REPEAT GEN_TAC THEN REWRITE_TAC[sha256_compress_round] THEN
 CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[EL_RECONSTRUCT]);;

let EL_RECONSTRUCT = end_itlist CONJ
  (List.map (fun n ->
    prove(subst[mk_small_numeral n, `n:num`]
      `!s:int32 list. EL n [EL 0 s; EL 1 s; EL 2 s; EL 3 s; EL 4 s; EL 5 s; EL 6 s; EL 7 s] = EL n s`,
      GEN_TAC THEN CONV_TAC(LAND_CONV EL_CONV) THEN REFL_TAC))
  (0--7));;

(* Generate bridge for round group i *)
let mk_group_bridge_h i =
  let base = 4 * i and target = 4 * (i + 1) in
  let base_s = mk_small_numeral base and target_s = mk_small_numeral target in
  let goal_tm = subst
    [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i), `i0:num`;
     mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`;
     mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha256_compress b W H in
      let st = sha256_compress t W H in
      word_join4 (EL 0 st) (EL 1 st) (EL 2 st) (EL 3 st) =
      sha256h (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
              (word_join4 (EL 4 sb) (EL 5 sb) (EL 6 sb) (EL 7 sb))
              (word_join4 (word_add (EL i0 W) (EL i0 sha256_K))
                          (word_add (EL i1 W) (EL i1 sha256_K))
                          (word_add (EL i2 W) (EL i2 sha256_K))
                          (word_add (EL i3 W) (EL i3 sha256_K)))` in
  prove(goal_tm,
    REPEAT GEN_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV
      [CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM] THEN
    REWRITE_TAC[EL_RECONSTRUCT] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN
    REFL_TAC);;

(* Same for SHA256H2 (EFGH half: EL 4..7) *)
let mk_group_bridge_h2 i =
  let base = 4 * i and target = 4 * (i + 1) in
  let base_s = mk_small_numeral base and target_s = mk_small_numeral target in
  let goal_tm = subst
    [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i), `i0:num`;
     mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`;
     mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha256_compress b W H in
      let st = sha256_compress t W H in
      word_join4 (EL 4 st) (EL 5 st) (EL 6 st) (EL 7 st) =
      sha256h2 (word_join4 (EL 4 sb) (EL 5 sb) (EL 6 sb) (EL 7 sb))
               (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
               (word_join4 (word_add (EL i0 W) (EL i0 sha256_K))
                           (word_add (EL i1 W) (EL i1 sha256_K))
                           (word_add (EL i2 W) (EL i2 sha256_K))
                           (word_add (EL i3 W) (EL i3 sha256_K)))` in
  prove(goal_tm,
    REPEAT GEN_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV
      [CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM] THEN
    REWRITE_TAC[EL_RECONSTRUCT] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN
    REFL_TAC);;

(* Generate all 16 group bridges *)
let GROUP_BRIDGE_H = Array.init 16 (fun i ->
  let th = mk_group_bridge_h i in
  Printf.printf "Group %d SHA256H bridge proved\n%!" i; th);;

let GROUP_BRIDGE_H2 = Array.init 16 (fun i ->
  let th = mk_group_bridge_h2 i in
  Printf.printf "Group %d SHA256H2 bridge proved\n%!" i; th);;
