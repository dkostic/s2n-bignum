(* Setup for interactive sha256_block_core proof *)
needs "arm/proofs/utils/sha256_bridge.ml";;

let sha256_block_core_mc = define_from_elf "sha256_block_core_mc"
  "/home/ubuntu/workspace/whole-crypto/s2n-bignum/arm/sha2/sha256_block_core.o";;
let EXEC = ARM_MK_EXEC_RULE sha256_block_core_mc;;
let ADD_SIMP_RULE = REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32];;

let SHA256_COMPRESS_ROUND_PREADD_SYM = prove(
  `!W_t K_t state. sha256_compress_round (word_add W_t K_t) (word 0:int32) state =
                   sha256_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD]);;

let SHA256H_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;;
let SHA256H2_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE;;

(* Only bridge assumptions containing sha256h or sha256h2 *)
let bridge_Q0Q1 th =
  let c = concl th in
  if can (find_term (fun t -> try fst(dest_const t) = "sha256h" with _ -> false)) c
  then
    let th1 = REWRITE_RULE[SHA256H_BRIDGE_FLAT; SHA256H2_BRIDGE_FLAT] th in
    REWRITE_RULE[SHA256_COMPRESS_ROUND_PREADD_SYM] th1
  else th;;

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

(* Incremental fold4: fold 4 compress_round calls on top of sha256_compress(4*i) *)
let COMPRESS_FOLD4 =
  let mk i =
    let base = 4 * i and target = 4 * (i + 1) in
    let target_tm = mk_small_numeral target and base_tm = mk_small_numeral base in
    let target_term = list_mk_comb(`sha256_compress`,
      [target_tm; `W:int32 list`; `state:int32 list`]) in
    let full_unroll = SHA256_COMPRESS_UNROLL_CONV target_term in
    if i = 0 then GSYM full_unroll
    else
      let base_unroll = SHA256_COMPRESS_UNROLL_CONV
        (list_mk_comb(`sha256_compress`, [base_tm; `W:int32 list`; `state:int32 list`])) in
      GSYM(CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[GSYM base_unroll])) full_unroll) in
  Array.init 16 mk;;

(* ================================================================== *)
(* Schedule lemmas: connect sha256_message_schedule to sha256su        *)
(* ================================================================== *)

let EL_APPEND_LENGTH = prove(
  `!l:A list. !x. EL (LENGTH l) (APPEND l [x]) = x`,
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

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

let SHA256_SCHEDULE_MONO = prove(
  `!n1 n2 M:int32 list. !k. k < LENGTH M + n1 /\ n1 <= n2 ==>
    EL k (sha256_message_schedule n2 M) = EL k (sha256_message_schedule n1 M)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `n1 <= n2:num` THENL
     [REWRITE_TAC[ARITH_RULE `SUC n2 = n2 + 1`; sha256_message_schedule; sha256_extend_schedule; EL_APPEND] THEN
      SUBGOAL_THEN `k < LENGTH(sha256_message_schedule n2 (M:int32 list))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_SHA256_MESSAGE_SCHEDULE] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `n1 = SUC n2` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; REFL_TAC]]]);;

let SHA256_SCHEDULE_NEWEST = prove(
  `!n M:int32 list. LENGTH M = 16 ==>
    EL (n + 16) (sha256_message_schedule (n + 1) M) =
    (let W = sha256_message_schedule n M in
     word_add (sha256_sigma1 (EL (n + 14) W))
       (word_add (EL (n + 9) W)
         (word_add (sha256_sigma0 (EL (n + 1) W)) (EL n W))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha256_message_schedule; sha256_extend_schedule] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `n + 16 = LENGTH(sha256_message_schedule n (M:int32 list))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SHA256_MESSAGE_SCHEDULE] THEN ARITH_TAC;
    REWRITE_TAC[EL_APPEND_LENGTH]]);;

let SHA256_W_EXTEND = prove(
  `!n M:int32 list. LENGTH M = 16 /\ n < 48 ==>
    EL (n + 16) (sha256_message_schedule 48 M) =
    (let W = sha256_message_schedule n M in
     word_add (sha256_sigma1 (EL (n + 14) W))
       (word_add (EL (n + 9) W)
         (word_add (sha256_sigma0 (EL (n + 1) W)) (EL n W))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL (n + 16) (sha256_message_schedule 48 (M:int32 list)) =
                EL (n + 16) (sha256_message_schedule (n + 1) M)` SUBST1_TAC THENL
   [MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SHA256_SCHEDULE_NEWEST THEN ASM_REWRITE_TAC[]]);;

(* EL k (sha256_block M H) = word_add (EL k (compress 64 W H)) (EL k H) *)
let SHA256_BLOCK_EL = prove(
  `!M H:int32 list. LENGTH H = 8 ==>
    !k. k < 8 ==> EL k (sha256_block M H) =
      word_add (EL k (sha256_compress 64 (sha256_message_schedule 48 M) H)) (EL k H)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha256_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EL_MAP2 THEN
  SUBGOAL_THEN `LENGTH (sha256_compress 64 (sha256_message_schedule 48 (M:int32 list)) (H:int32 list)) = 8`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_SHA256_COMPRESS THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;
