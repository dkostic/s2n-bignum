(* SHA-256 block core proof, version 2: with postcondition matching.         *)
(* This version uses cut-points after each round group to keep terms small. *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha256_bridge.ml";;

let sha256_block_core_mc = define_from_elf "sha256_block_core_mc"
  "/home/ubuntu/workspace/whole-crypto/s2n-bignum/arm/sha2/sha256_block_core.o";;

let EXEC = ARM_MK_EXEC_RULE sha256_block_core_mc;;

(* ========================================================================= *)
(* Helper lemmas and conversions.                                            *)
(* ========================================================================= *)

let ADD_SIMP_RULE = REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32];;

(* PREADD with swapped arguments: word_add W K -> K first *)
let SHA256_COMPRESS_ROUND_PREADD_SYM = prove(
  `!W_t K_t state. sha256_compress_round (word_add W_t K_t) (word 0:int32) state =
                   sha256_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD]);;

(* Conversion to unroll sha256_compress n to nested compress_round calls *)
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

(* Generate incremental fold4 lemmas: fold 4 CR calls into sha256_compress *)
(* COMPRESS_FOLD4.(i) : CR^4(sha256_compress(4*i) W state) = sha256_compress(4*(i+1)) W state *)
let COMPRESS_FOLD4 =
  let mk i =
    let base = 4 * i in
    let target = 4 * (i + 1) in
    let target_tm = mk_small_numeral target and base_tm = mk_small_numeral base in
    let target_term = list_mk_comb(`sha256_compress`,
      [target_tm; `W:int32 list`; `state:int32 list`]) in
    let full_unroll = SHA256_COMPRESS_UNROLL_CONV target_term in
    if i = 0 then GSYM full_unroll
    else
      let base_unroll = SHA256_COMPRESS_UNROLL_CONV
        (list_mk_comb(`sha256_compress`,
          [base_tm; `W:int32 list`; `state:int32 list`])) in
      GSYM(CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[GSYM base_unroll])) full_unroll) in
  Array.init 16 mk;;

(* The flattened bridge rules *)
let SHA256H_BRIDGE_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;;
let SHA256H2_BRIDGE_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE;;
let SHA256SU_BRIDGE_FLAT =
  CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256SU_BRIDGE;;

(* Bridge + fold tactic for Q0 and Q1 ONLY after each round group.         *)
(* Only targets assumptions about sha256h/sha256h2 (Q0/Q1), not schedule   *)
(* registers. This is crucial for performance - applying bridge rules to    *)
(* all assumptions causes the schedule terms to blow up.                    *)
let BRIDGE_AND_FOLD_TAC i =
  let bridge_fold th =
    let c = concl th in
    (* Only process assumptions that contain sha256h or sha256h2 *)
    if can (find_term (fun t -> try fst(dest_const t) = "sha256h" with _ -> false)) c ||
       can (find_term (fun t -> try fst(dest_const t) = "sha256h2" with _ -> false)) c
    then
      let th1 = REWRITE_RULE[SHA256H_BRIDGE_FLAT; SHA256H2_BRIDGE_FLAT] th in
      let th2 = REWRITE_RULE[SHA256_COMPRESS_ROUND_PREADD_SYM] th1 in
      REWRITE_RULE[COMPRESS_FOLD4.(i)] th2
    else th in
  RULE_ASSUM_TAC bridge_fold;;

(* Combined round group tactic *)
let ROUND_GROUP_TAC i group_steps =
  ARM_STEPS_TAC EXEC group_steps THEN
  RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  BRIDGE_AND_FOLD_TAC i;;

(* ========================================================================= *)
(* Smoke test: just the first round group with bridging+folding.            *)
(* ========================================================================= *)

let SHA256_BLOCK_CORE_TEST2 = time prove(
 `!(a:int32) b c d (e:int32) f g h
   (w0:int32) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
   kptr pc ret_pc.
   nonoverlapping (kptr, 256) (word pc, 436)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_block_core_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X1 s = kptr /\
         read Q0 s = word_join4 a b c d /\
         read Q1 s = word_join4 e f g h /\
         read Q4 s = word_join4 w0 w1 w2 w3 /\
         read Q5 s = word_join4 w4 w5 w6 w7 /\
         read Q6 s = word_join4 w8 w9 w10 w11 /\
         read Q7 s = word_join4 w12 w13 w14 w15 /\
         (!i. i < 16 ==>
           read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
           word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                      (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)))
    (\s. T)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q18; Q19] ,,
     MAYCHANGE [events])`,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN

  (* Steps 1-2: Save initial state *)
  ARM_STEPS_TAC EXEC (1--2) THEN

  (* Round groups 0-11 with bridging + folding *)
  ROUND_GROUP_TAC 0 (3--9) THEN
  ROUND_GROUP_TAC 1 (10--16) THEN
  ROUND_GROUP_TAC 2 (17--23) THEN
  ROUND_GROUP_TAC 3 (24--30) THEN
  ROUND_GROUP_TAC 4 (31--37) THEN
  ROUND_GROUP_TAC 5 (38--44) THEN
  ROUND_GROUP_TAC 6 (45--51) THEN
  ROUND_GROUP_TAC 7 (52--58) THEN
  ROUND_GROUP_TAC 8 (59--65) THEN
  ROUND_GROUP_TAC 9 (66--72) THEN
  ROUND_GROUP_TAC 10 (73--79) THEN
  ROUND_GROUP_TAC 11 (80--86) THEN

  (* Round groups 12-15 (no schedule update) *)
  ROUND_GROUP_TAC 12 (87--91) THEN
  ROUND_GROUP_TAC 13 (92--96) THEN
  ROUND_GROUP_TAC 14 (97--101) THEN
  ROUND_GROUP_TAC 15 (102--106) THEN

  (* Steps 107-109: ADD state add-back + RET *)
  ARM_STEPS_TAC EXEC (107--109) THEN
  RULE_ASSUM_TAC ADD_SIMP_RULE THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;
