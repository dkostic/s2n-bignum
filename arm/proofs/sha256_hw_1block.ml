(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 HW single-block correctness (num_blocks = 1).                     *)
(* Separated from sha256_block_data_order_hw.ml for faster iteration on      *)
(* the multi-block proof.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/sha256_block_data_order_hw.ml";;

let SHA256_HW_1BLOCK_CORRECT = time prove(
 `!(a:int32) b c d (e:int32) f g h
   (m0:int32) m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
   state_ptr data_ptr kptr pc.
   ALL (nonoverlapping (state_ptr, 32))
       [(word pc, 496); (data_ptr, 64); (kptr, 256)] /\
   nonoverlapping (data_ptr, 64) (word pc, 496) /\
   nonoverlapping (kptr, 256) (word pc, 496)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_hw_mc /\
         read PC s = word pc /\
         read X30 s = word(pc + 0x1ec) /\
         read X0 s = state_ptr /\
         read X1 s = data_ptr /\
         read X2 s = word 1 /\
         read X3 s = kptr /\
         read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
         read (memory :> bytes128 (word_add state_ptr (word 16))) s =
           word_join4 e f g h /\
         read (memory :> bytes128 data_ptr) s = word_join4 m0 m1 m2 m3 /\
         read (memory :> bytes128 (word_add data_ptr (word 16))) s =
           word_join4 m4 m5 m6 m7 /\
         read (memory :> bytes128 (word_add data_ptr (word 32))) s =
           word_join4 m8 m9 m10 m11 /\
         read (memory :> bytes128 (word_add data_ptr (word 48))) s =
           word_join4 m12 m13 m14 m15 /\
         (!i. i < 16 ==>
           read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
           word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                      (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)))
    (\s. read PC s = word(pc + 0x1ec) /\
         (let M = [word_bytereverse m0; word_bytereverse m1;
                   word_bytereverse m2; word_bytereverse m3;
                   word_bytereverse m4; word_bytereverse m5;
                   word_bytereverse m6; word_bytereverse m7;
                   word_bytereverse m8; word_bytereverse m9;
                   word_bytereverse m10; word_bytereverse m11;
                   word_bytereverse m12; word_bytereverse m13;
                   word_bytereverse m14; word_bytereverse m15] in
          let H = [a;b;c;d;e;f;g;h] in
          let result = sha256_block M H in
          read (memory :> bytes128 state_ptr) s =
            word_join4 (EL 0 result) (EL 1 result)
                       (EL 2 result) (EL 3 result) /\
          read (memory :> bytes128 (word_add state_ptr (word 16))) s =
            word_join4 (EL 4 result) (EL 5 result)
                       (EL 6 result) (EL 7 result)))
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q18; Q19] ,,
     MAYCHANGE [memory :> bytes(state_ptr, 32)] ,,
     MAYCHANGE [events])`,

  REWRITE_TAC[ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
  ARM_STEPS_TAC HW_EXEC (1--14) THEN
  RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  SUBGOAL_THEN `read Q4 s14 = word_join4 (word_bytereverse m0:int32) (word_bytereverse m1) (word_bytereverse m2) (word_bytereverse m3)` (fun th -> RULE_ASSUM_TAC(fun asm -> if can (term_match [] `read Q4 s = x:int128`) (concl asm) && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm)) then th else asm)) THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN
  SUBGOAL_THEN `read Q5 s14 = word_join4 (word_bytereverse m4:int32) (word_bytereverse m5) (word_bytereverse m6) (word_bytereverse m7)` (fun th -> RULE_ASSUM_TAC(fun asm -> if can (term_match [] `read Q5 s = x:int128`) (concl asm) && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm)) then th else asm)) THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN
  SUBGOAL_THEN `read Q6 s14 = word_join4 (word_bytereverse m8:int32) (word_bytereverse m9) (word_bytereverse m10) (word_bytereverse m11)` (fun th -> RULE_ASSUM_TAC(fun asm -> if can (term_match [] `read Q6 s = x:int128`) (concl asm) && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm)) then th else asm)) THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN
  SUBGOAL_THEN `read Q7 s14 = word_join4 (word_bytereverse m12:int32) (word_bytereverse m13) (word_bytereverse m14) (word_bytereverse m15)` (fun th -> RULE_ASSUM_TAC(fun asm -> if can (term_match [] `read Q7 s = x:int128`) (concl asm) && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm)) then th else asm)) THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN
  ABBREV_TAC `w0 = word_bytereverse m0 :int32` THEN ABBREV_TAC `w1 = word_bytereverse m1 :int32` THEN
  ABBREV_TAC `w2 = word_bytereverse m2 :int32` THEN ABBREV_TAC `w3 = word_bytereverse m3 :int32` THEN
  ABBREV_TAC `w4 = word_bytereverse m4 :int32` THEN ABBREV_TAC `w5 = word_bytereverse m5 :int32` THEN
  ABBREV_TAC `w6 = word_bytereverse m6 :int32` THEN ABBREV_TAC `w7 = word_bytereverse m7 :int32` THEN
  ABBREV_TAC `w8 = word_bytereverse m8 :int32` THEN ABBREV_TAC `w9 = word_bytereverse m9 :int32` THEN
  ABBREV_TAC `w10 = word_bytereverse m10 :int32` THEN ABBREV_TAC `w11 = word_bytereverse m11 :int32` THEN
  ABBREV_TAC `w12 = word_bytereverse m12 :int32` THEN ABBREV_TAC `w13 = word_bytereverse m13 :int32` THEN
  ABBREV_TAC `w14 = word_bytereverse m14 :int32` THEN ABBREV_TAC `w15 = word_bytereverse m15 :int32` THEN
  ABBREV_TAC `W = sha256_message_schedule 48 [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]` THEN
  (let w_hyp_tm = `sha256_message_schedule 48 [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W` in
  ARM_STEPS_TAC HW_EXEC (15--21) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 0 `s21:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (22--28) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 1 `s28:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (29--35) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 2 `s35:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (36--42) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 3 `s42:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (43--49) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 4 `s49:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (50--56) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 5 `s56:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (57--63) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 6 `s63:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (64--70) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 7 `s70:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (71--77) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 8 `s77:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (78--84) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 9 `s84:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (85--91) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 10 `s91:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (92--98) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 11 `s98:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (99--103) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 12 `s103:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (104--108) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 13 `s108:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (109--113) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 14 `s113:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (114--118) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN CUT_POINT_TAC_HW 15 `s118:armstate` THEN
  ARM_STEPS_TAC HW_EXEC (119--124) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POSTCOND_TAC_HW));;
