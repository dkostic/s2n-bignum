(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 message schedule computation using scalar instructions.            *)
(* Loads 16 big-endian message words, byte-swaps them, then extends the       *)
(* schedule to 64 words on a caller-provided buffer.                          *)
(* ========================================================================= *)

needs "arm/proofs/sha256_block_core.ml";;

(* Machine code *)

let sha256_schedule_scalar_mc = define_from_elf "sha256_schedule_scalar_mc"
  (file_on_path !load_path "arm/sha2/sha256_schedule_scalar.o");;

let SCALAR_SCHED_EXEC = ARM_MK_EXEC_RULE sha256_schedule_scalar_mc;;

(* Correctness theorem *)

let SHA256_SCHEDULE_SCALAR_CORRECT = prove
 (`!M wptr dptr pc.
    LENGTH M = 16 /\
    nonoverlapping (word pc, 128) (wptr:int64, 256) /\
    nonoverlapping (word pc, 128) (dptr:int64, 64) /\
    nonoverlapping (wptr, 256) (dptr, 64)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) sha256_schedule_scalar_mc /\
           read PC s = word pc /\
           read X0 s = wptr /\
           read X1 s = dptr /\
           (!t. t < 16 ==>
                read (memory :> bytes32(word_add dptr (word(4*t)))) s =
                word_bytereverse (EL t M)))
      (\s. read PC s = word(pc + 0x7c) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add wptr (word(4*t)))) s =
                EL t (sha256_message_schedule 48 M)))
      (MAYCHANGE [PC; X2; X3; X12; X13; X14; X15; X16; X17] ,,
       MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [memory :> bytes(wptr,256)] ,,
       MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst SCALAR_SCHED_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* Split into two phases at pc+0x1c *)
  ENSURES_SEQUENCE_TAC `pc + 0x1c`
    `\s. aligned_bytes_loaded s (word pc) sha256_schedule_scalar_mc /\
         read X0 s = wptr /\
         read X1 s = dptr /\
         (!t. t < 16 ==>
              read (memory :> bytes32(word_add wptr (word(4*t)))) s =
              EL t M) /\
         (!t. t < 16 ==>
              read (memory :> bytes32(word_add dptr (word(4*t)))) s =
              word_bytereverse (EL t M))` THEN
  CONJ_TAC THENL

  [(* ===== PHASE 1: load 16 words from dptr, byte-swap, store to wptr ===== *)

   ENSURES_WHILE_UP2_TAC `16` `pc + 0x4` `pc + 0x1c`
    `\i s. aligned_bytes_loaded s (word pc) sha256_schedule_scalar_mc /\
           read X0 s = wptr /\
           read X1 s = dptr /\
           read X17 s = word i /\
           (!t. t < 16 ==>
                read (memory :> bytes32(word_add dptr (word(4*t)))) s =
                word_bytereverse (EL t M)) /\
           (!t. t < i ==>
                read (memory :> bytes32(word_add wptr (word(4*t)))) s =
                EL t M)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL

    [(* Subgoal 1.1: 16 <> 0 *)
     ARITH_TAC;

     (* Subgoal 1.2: INIT -- precondition ==> invariant(0) at pc+4 *)
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC SCALAR_SCHED_EXEC (1--1) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LT] THEN MESON_TAC[];

     (* Subgoal 1.3: BODY -- one iteration *)
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `word_shl (word i:int64) 2 = word (4 * i)` ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `val (word i:int64) = i` ASSUME_TAC THENL
      [ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `read (memory :> bytes32 (word_add dptr (word (4 * i)))) s0 =
       word_bytereverse (EL i M)`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     ARM_STEPS_TAC SCALAR_SCHED_EXEC (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [(* PC conditional *)
       REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 16 ==> i < 2 EXP 64`;
                    ARITH_RULE `18446744073709551601 < 2 EXP 64`] THEN
       ASM_CASES_TAC `i + 1 = 16` THENL
        [ASM_REWRITE_TAC[LT_REFL] THEN
         SUBGOAL_THEN `i = 15` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
         SUBGOAL_THEN `i + 1 < 16` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~((i + 18446744073709551601) MOD 2 EXP 64 = 0)`
           ASSUME_TAC THENL
          [SUBGOAL_THEN
             `(i + 18446744073709551601) MOD 2 EXP 64 =
              i + 18446744073709551601` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
           ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[]];

       (* word_add counter *)
       CONV_TAC WORD_RULE;

       (* Memory preservation / extension *)
       GEN_TAC THEN DISCH_TAC THEN
       ASM_CASES_TAC `t < i` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `t:num = i` SUBST_ALL_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
       SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_32; DIMINDEX_64;
                LE_REFL; ARITH] THEN
       REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE]];

     (* Subgoal 1.4: EXIT -- invariant(16) at pc+0x1c ==> phase 1 post *)
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[]];

   (* ===== PHASE 2: compute W[16..63] from W[0..15] on the buffer ===== *)

   (* Phase 2 init: 2 instructions at pc+0x1c..pc+0x24 *)
   ENSURES_SEQUENCE_TAC `pc + 0x24`
    `\s. aligned_bytes_loaded s (word pc) sha256_schedule_scalar_mc /\
         read X0 s = wptr /\
         read X1 s = dptr /\
         read X2 s = wptr /\
         read X17 s = word 0 /\
         (!t. t < 16 ==>
              read (memory :> bytes32(word_add wptr (word(4*t)))) s =
              EL t M)` THEN
   CONJ_TAC THENL

    [ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC SCALAR_SCHED_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[];

     ALL_TAC] THEN

   (* Phase 2 loop *)
   ENSURES_WHILE_UP2_TAC `48` `pc + 0x24` `pc + 0x7c`
    `\i s. aligned_bytes_loaded s (word pc) sha256_schedule_scalar_mc /\
           read X0 s = wptr /\
           read X1 s = dptr /\
           read X2 s = word_add wptr (word (4 * i)) /\
           read X17 s = word i /\
           (!t. t < i + 16 ==>
                read (memory :> bytes32(word_add wptr (word(4*t)))) s =
                EL t (sha256_message_schedule i M))` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL

    [(* Subgoal 2.1: 48 <> 0 *)
     ARITH_TAC;

     (* Subgoal 2.2: INIT -- trivial (loopinv(0) already matches phase 2 pre) *)
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; sha256_message_schedule;
                     ADD_CLAUSES];

     (* Subgoal 2.3: BODY -- one iteration of schedule extension *)
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `word_add (word_add wptr (word (4 * i))) (word 0):int64 =
         word_add wptr (word(4 * i)) /\
       word_add (word_add wptr (word (4 * i))) (word 4):int64 =
         word_add wptr (word(4 * (i+1))) /\
       word_add (word_add wptr (word (4 * i))) (word 36):int64 =
         word_add wptr (word(4 * (i+9))) /\
       word_add (word_add wptr (word (4 * i))) (word 56):int64 =
         word_add wptr (word(4 * (i+14))) /\
       word_add (word_add wptr (word (4 * i))) (word 64):int64 =
         word_add wptr (word(4 * (i+16)))`
     STRIP_ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
     SUBGOAL_THEN
      `read (memory :> bytes32 (word_add wptr (word (4 * i)))) s0 =
       EL i (sha256_message_schedule i M) /\
       read (memory :> bytes32 (word_add wptr (word (4 * (i+1))))) s0 =
       EL (i+1) (sha256_message_schedule i M) /\
       read (memory :> bytes32 (word_add wptr (word (4 * (i+9))))) s0 =
       EL (i+9) (sha256_message_schedule i M) /\
       read (memory :> bytes32 (word_add wptr (word (4 * (i+14))))) s0 =
       EL (i+14) (sha256_message_schedule i M)`
     STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
       ALL_TAC] THEN
     ARM_STEPS_TAC SCALAR_SCHED_EXEC (1--22) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [(* PC conditional *)
       REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 48 ==> i < 2 EXP 64`;
                    ARITH_RULE `18446744073709551569 < 2 EXP 64`] THEN
       ASM_CASES_TAC `i + 1 = 48` THENL
        [ASM_REWRITE_TAC[LT_REFL] THEN
         SUBGOAL_THEN `i = 47` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         CONV_TAC NUM_REDUCE_CONV;
         SUBGOAL_THEN `i + 1 < 48` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~((i + 18446744073709551569) MOD 2 EXP 64 = 0)`
           ASSUME_TAC THENL
          [SUBGOAL_THEN
             `(i + 18446744073709551569) MOD 2 EXP 64 =
              i + 18446744073709551569` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
           ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[]];

       (* word_add counter *)
       CONV_TAC WORD_RULE;

       (* Memory invariant *)
       GEN_TAC THEN DISCH_TAC THEN
       ASM_CASES_TAC `t < i + 16` THENL
        [SUBGOAL_THEN
          `EL t (sha256_message_schedule (i+1) M) =
           EL t (sha256_message_schedule i M)`
         SUBST1_TAC THENL
          [MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN
           ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
           ALL_TAC] THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       SUBGOAL_THEN `t = i + 16` SUBST_ALL_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       MP_TAC(SPECL [`i:num`; `M:int32 list`] SHA256_SCHEDULE_NEWEST) THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
       SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
       SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                WORD_ZX_TRIVIAL] THEN
       CONV_TAC WORD_RULE];

     (* Subgoal 2.4: EXIT -- invariant(48) at pc+0x7c ==> final post *)
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;
