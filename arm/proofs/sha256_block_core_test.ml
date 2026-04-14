(* Test: symbolic execution of sha256_block_core with postcondition T *)

needs "arm/proofs/utils/sha256_bridge.ml";;

let sha256_block_core_mc = define_from_elf "sha256_block_core_mc"
  "/home/ubuntu/workspace/whole-crypto/s2n-bignum/arm/sha2/sha256_block_core.o";;

let EXEC = ARM_MK_EXEC_RULE sha256_block_core_mc;;

let ADD_SIMP_RULE = REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32];;

let ROUND_GROUP_TAC gs =
  ARM_STEPS_TAC EXEC gs THEN RULE_ASSUM_TAC ADD_SIMP_RULE;;

let SHA256_BLOCK_CORE_EXEC_TEST = time prove(
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

  (* Round groups 0-11 (with schedule update, 7 steps each) *)
  ROUND_GROUP_TAC (3--9) THEN
  ROUND_GROUP_TAC (10--16) THEN
  ROUND_GROUP_TAC (17--23) THEN
  ROUND_GROUP_TAC (24--30) THEN
  ROUND_GROUP_TAC (31--37) THEN
  ROUND_GROUP_TAC (38--44) THEN
  ROUND_GROUP_TAC (45--51) THEN
  ROUND_GROUP_TAC (52--58) THEN
  ROUND_GROUP_TAC (59--65) THEN
  ROUND_GROUP_TAC (66--72) THEN
  ROUND_GROUP_TAC (73--79) THEN
  ROUND_GROUP_TAC (80--86) THEN

  (* Round groups 12-15 (no schedule update, 5 steps each) *)
  ROUND_GROUP_TAC (87--91) THEN
  ROUND_GROUP_TAC (92--96) THEN
  ROUND_GROUP_TAC (97--101) THEN
  ROUND_GROUP_TAC (102--106) THEN

  (* Steps 107-109: ADD state add-back + RET *)
  ARM_STEPS_TAC EXEC (107--109) THEN
  RULE_ASSUM_TAC ADD_SIMP_RULE THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;
