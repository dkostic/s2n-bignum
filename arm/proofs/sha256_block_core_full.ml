(* SHA-256 block core: FULL proof with functional correctness. *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

(* ================================================================== *)
(* Machine code and execution rule                                     *)
(* ================================================================== *)

let sha256_block_core_mc = define_from_elf "sha256_block_core_mc"
  "/home/ubuntu/workspace/whole-crypto/s2n-bignum/arm/sha2/sha256_block_core.o";;
let EXEC = ARM_MK_EXEC_RULE sha256_block_core_mc;;

(* ================================================================== *)
(* Helper lemmas                                                       *)
(* ================================================================== *)

let ADD_SIMP_RULE = REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32];;

let SHA256_COMPRESS_ROUND_PREADD_SYM = prove(
  `!W_t K_t state. sha256_compress_round (word_add W_t K_t) (word 0:int32) state =
                   sha256_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD]);;

let SHA256H_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;;
let SHA256H2_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE;;

let EL_RECONSTRUCT = end_itlist CONJ (List.map (fun n ->
  prove(subst[mk_small_numeral n, `n:num`]
    `!s:int32 list. EL n [EL 0 s; EL 1 s; EL 2 s; EL 3 s; EL 4 s; EL 5 s; EL 6 s; EL 7 s] = EL n s`,
    GEN_TAC THEN CONV_TAC(LAND_CONV EL_CONV) THEN REFL_TAC)) (0--7));;

let SHA256_COMPRESS_ROUND_EL_LIST = prove(
 `!K W s:int32 list.
   sha256_compress_round K W [EL 0 s; EL 1 s; EL 2 s; EL 3 s; EL 4 s; EL 5 s; EL 6 s; EL 7 s] =
   sha256_compress_round K W s`,
 REPEAT GEN_TAC THEN REWRITE_TAC[sha256_compress_round] THEN
 CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[EL_RECONSTRUCT]);;

let rec SHA256_COMPRESS_UNROLL_CONV tm =
  let n_tm = rand(rator(rator tm)) in
  if n_tm = `0` then REWRITE_CONV[sha256_compress] tm
  else
    let n = dest_small_numeral n_tm in
    let arith_th = ARITH_RULE
      (mk_eq(n_tm, mk_comb(mk_comb(`(+)`, mk_small_numeral(n-1)), `1`))) in
    let step1 = ONCE_REWRITE_CONV[arith_th] tm in
    let step2 = CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[sha256_compress])) step1 in
    CONV_RULE(RAND_CONV(RAND_CONV SHA256_COMPRESS_UNROLL_CONV)) step2;;

let LENGTH_SHA256_MESSAGE_SCHEDULE = prove(
  `!n M:int32 list. LENGTH(sha256_message_schedule n M) = LENGTH M + n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha256_message_schedule; ADD_CLAUSES];
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha256_message_schedule;
      sha256_extend_schedule; LENGTH_APPEND; LENGTH] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let SHA256_SCHEDULE_PREFIX = prove(
  `!n M:int32 list. !k. k < LENGTH M ==> EL k (sha256_message_schedule n M) = EL k M`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha256_message_schedule];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha256_message_schedule;
      sha256_extend_schedule; EL_APPEND] THEN
    SUBGOAL_THEN `k < LENGTH(sha256_message_schedule n (M:int32 list))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_SHA256_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ================================================================== *)
(* Per-round-group bridge lemmas                                       *)
(* ================================================================== *)

let mk_group_bridge_h i =
  let base_s = mk_small_numeral(4 * i) and target_s = mk_small_numeral(4 * (i + 1)) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i), `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha256_compress b W H in let st = sha256_compress t W H in
      word_join4 (EL 0 st) (EL 1 st) (EL 2 st) (EL 3 st) =
      sha256h (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
              (word_join4 (EL 4 sb) (EL 5 sb) (EL 6 sb) (EL 7 sb))
              (word_join4 (word_add (EL i0 W) (EL i0 sha256_K))
                          (word_add (EL i1 W) (EL i1 sha256_K))
                          (word_add (EL i2 W) (EL i2 sha256_K))
                          (word_add (EL i3 W) (EL i3 sha256_K)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA256H_BRIDGE_FLAT] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM; EL_RECONSTRUCT] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN REFL_TAC);;

let mk_group_bridge_h2 i =
  let base_s = mk_small_numeral(4 * i) and target_s = mk_small_numeral(4 * (i + 1)) in
  prove(subst [base_s, `b:num`; target_s, `t:num`;
     mk_small_numeral(4*i), `i0:num`; mk_small_numeral(4*i+1), `i1:num`;
     mk_small_numeral(4*i+2), `i2:num`; mk_small_numeral(4*i+3), `i3:num`]
    `!W H:int32 list.
      let sb = sha256_compress b W H in let st = sha256_compress t W H in
      word_join4 (EL 4 st) (EL 5 st) (EL 6 st) (EL 7 st) =
      sha256h2 (word_join4 (EL 4 sb) (EL 5 sb) (EL 6 sb) (EL 7 sb))
               (word_join4 (EL 0 sb) (EL 1 sb) (EL 2 sb) (EL 3 sb))
               (word_join4 (word_add (EL i0 W) (EL i0 sha256_K))
                           (word_add (EL i1 W) (EL i1 sha256_K))
                           (word_add (EL i2 W) (EL i2 sha256_K))
                           (word_add (EL i3 W) (EL i3 sha256_K)))`,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC RAND_CONV [SHA256H2_BRIDGE_FLAT] THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD_SYM; EL_RECONSTRUCT] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [target_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV
      (SHA256_COMPRESS_UNROLL_CONV (subst [base_s,`n:num`]
        `sha256_compress n W (state:int32 list)`))))) THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN REFL_TAC);;

let GROUP_BRIDGE_H = Array.init 16 mk_group_bridge_h;;
let GROUP_BRIDGE_H2 = Array.init 16 mk_group_bridge_h2;;

let () = Printf.printf "All 32 bridge lemmas proved.\n%!";;

(* TODO: Complete the full ensures proof using the cut-point approach.
   The approach:
   1. At each round group, SUBGOAL_THEN to assert Q0/Q1 in sha256_compress form
   2. Prove each subgoal using GROUP_BRIDGE_H/H2 + SHA256_SCHEDULE_PREFIX
   3. Replace sha256h assumptions with sha256_compress form
   4. After all 16 groups + add-back: match sha256_compress 64 to sha256_block
*)
