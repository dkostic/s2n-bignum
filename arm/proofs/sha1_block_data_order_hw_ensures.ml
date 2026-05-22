(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-1 multi-block hardware-accelerated function (Phase 7/8).              *)
(*                                                                           *)
(* Proves correctness of sha1_block_data_order_hw, which processes           *)
(* num_blocks consecutive 512-bit message blocks using ARM SHA-1 hardware    *)
(* instructions (SHA1C/SHA1P/SHA1M/SHA1H/SHA1SU0/SHA1SU1).                   *)
(*                                                                           *)
(* void sha1_block_data_order_hw(uint32_t state[5],                          *)
(*                               const uint8_t *data,                        *)
(*                               size_t num_blocks,                          *)
(*                               const uint32_t K[16])                       *)
(*                                                                           *)
(* The proof reuses the cut-point / per-band bridge infrastructure in        *)
(* arm/proofs/sha1_block_core.ml, wrapped in an ENSURES_WHILE_UP_TAC over    *)
(* the block index. PC offsets:                                              *)
(*   prologue:  pc+0x00..pc+0x18  (instr  1..7)                              *)
(*   loop top:  pc+0x1c           (instr  8)                                 *)
(*   body:      pc+0x1c..pc+0x1bc (instrs 8..112)                            *)
(*   CBNZ:      pc+0x1c0          (instr  113)                               *)
(*   epilogue:  pc+0x1c4..pc+0x1cc (instrs 114..116)                         *)
(*   RET:       pc+0x1d0          (instr  117)                               *)
(* ========================================================================= *)

needs "arm/proofs/sha1_block_data_order_hw.ml";;

(* ========================================================================= *)
(* Multi-block correctness theorem.                                          *)
(*                                                                           *)
(* The `blocks` parameter represents the SHA-1-ready message blocks (after   *)
(* byte-reversal). Memory contains word_bytereverse of each element (raw     *)
(* little-endian format); the assembly applies REV32 to convert.             *)
(*                                                                           *)
(* The loop invariant tracks sha1_hash_blocks i blocks [a;b;c;d;e] in        *)
(* (Q0, lane-0 of Q1) form, data pointer at data_ptr + 64*i, block counter  *)
(* at num_blocks - i.                                                        *)
(*                                                                           *)
(* Q1's upper 96 bits are unconstrained (left opaque) — the spec only        *)
(* depends on lane 0, and the iterated `add v1.4s, v1.4s, v2.4s` clobbers    *)
(* the upper lanes between blocks but their content does not affect the      *)
(* final state buffer.                                                       *)
(* ========================================================================= *)

let SHA1_HW_CORRECT = prove
 (`!num_blocks state_ptr data_ptr kptr
    (a:int32) (b:int32) (c:int32) (d:int32) (e:int32)
    (blocks:(int32 list) list) pc.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    ALL (nonoverlapping (state_ptr, 20))
        [(word pc, 468); (data_ptr, 64 * num_blocks); (kptr, 64)] /\
    nonoverlapping (data_ptr, 64 * num_blocks) (word pc, 468) /\
    nonoverlapping (kptr, 64) (word pc, 468)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha1_block_data_order_hw_mc /\
          read PC s = word pc /\
          read X0 s = state_ptr /\
          read X1 s = data_ptr /\
          read X2 s = word num_blocks /\
          read X3 s = kptr /\
          read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
          read (memory :> bytes32 (word_add state_ptr (word 16))) s = e /\
          (!j. j < num_blocks ==>
            read (memory :> bytes128 (word_add data_ptr (word(64 * j)))) s =
              word_join4 (word_bytereverse (EL 0 (EL j blocks)))
                         (word_bytereverse (EL 1 (EL j blocks)))
                         (word_bytereverse (EL 2 (EL j blocks)))
                         (word_bytereverse (EL 3 (EL j blocks))) /\
            read (memory :> bytes128 (word_add data_ptr (word(64 * j + 16)))) s =
              word_join4 (word_bytereverse (EL 4 (EL j blocks)))
                         (word_bytereverse (EL 5 (EL j blocks)))
                         (word_bytereverse (EL 6 (EL j blocks)))
                         (word_bytereverse (EL 7 (EL j blocks))) /\
            read (memory :> bytes128 (word_add data_ptr (word(64 * j + 32)))) s =
              word_join4 (word_bytereverse (EL 8 (EL j blocks)))
                         (word_bytereverse (EL 9 (EL j blocks)))
                         (word_bytereverse (EL 10 (EL j blocks)))
                         (word_bytereverse (EL 11 (EL j blocks))) /\
            read (memory :> bytes128 (word_add data_ptr (word(64 * j + 48)))) s =
              word_join4 (word_bytereverse (EL 12 (EL j blocks)))
                         (word_bytereverse (EL 13 (EL j blocks)))
                         (word_bytereverse (EL 14 (EL j blocks)))
                         (word_bytereverse (EL 15 (EL j blocks)))) /\
          (!i. i < 4 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
            word_join4 (sha1_K (20*i)) (sha1_K (20*i))
                       (sha1_K (20*i)) (sha1_K (20*i))))
     (\s. read PC s = word(pc + 0x1d0) /\
          (let result = sha1_hash_blocks num_blocks blocks [a;b;c;d;e] in
           read (memory :> bytes128 state_ptr) s =
             word_join4 (EL 0 result) (EL 1 result)
                        (EL 2 result) (EL 3 result) /\
           read (memory :> bytes32 (word_add state_ptr (word 16))) s =
             EL 4 result))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19;
                 Q20; Q21; Q22] ,,
      MAYCHANGE [memory :> bytes(state_ptr, 20)] ,,
      MAYCHANGE [events])`,

  REWRITE_TAC[ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `~(num_blocks = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN

  ENSURES_WHILE_UP_TAC `num_blocks:num` `pc + 0x1c` `pc + 0x1c0`
    `\i s. aligned_bytes_loaded s (word pc) sha1_block_data_order_hw_mc /\
           read X0 s = state_ptr /\
           read X1 s = word_add data_ptr (word(64 * i)) /\
           read X2 s = word(num_blocks - i) /\
           read X3 s = kptr /\
           read Q0 s = word_join4
             (EL 0 (sha1_hash_blocks i blocks [a;b;c;d;e]:int32 list))
             (EL 1 (sha1_hash_blocks i blocks [a;b;c;d;e]))
             (EL 2 (sha1_hash_blocks i blocks [a;b;c;d;e]))
             (EL 3 (sha1_hash_blocks i blocks [a;b;c;d;e])) /\
           word_subword (read Q1 s) (0,32):int32 =
             EL 4 (sha1_hash_blocks i blocks [a;b;c;d;e]) /\
           (!j. j < num_blocks ==>
             read (memory :> bytes128 (word_add data_ptr (word(64 * j)))) s =
               word_join4 (word_bytereverse (EL 0 (EL j blocks)))
                          (word_bytereverse (EL 1 (EL j blocks)))
                          (word_bytereverse (EL 2 (EL j blocks)))
                          (word_bytereverse (EL 3 (EL j blocks))) /\
             read (memory :> bytes128 (word_add data_ptr (word(64 * j + 16)))) s =
               word_join4 (word_bytereverse (EL 4 (EL j blocks)))
                          (word_bytereverse (EL 5 (EL j blocks)))
                          (word_bytereverse (EL 6 (EL j blocks)))
                          (word_bytereverse (EL 7 (EL j blocks))) /\
             read (memory :> bytes128 (word_add data_ptr (word(64 * j + 32)))) s =
               word_join4 (word_bytereverse (EL 8 (EL j blocks)))
                          (word_bytereverse (EL 9 (EL j blocks)))
                          (word_bytereverse (EL 10 (EL j blocks)))
                          (word_bytereverse (EL 11 (EL j blocks))) /\
             read (memory :> bytes128 (word_add data_ptr (word(64 * j + 48)))) s =
               word_join4 (word_bytereverse (EL 12 (EL j blocks)))
                          (word_bytereverse (EL 13 (EL j blocks)))
                          (word_bytereverse (EL 14 (EL j blocks)))
                          (word_bytereverse (EL 15 (EL j blocks)))) /\
           (!k. k < 4 ==>
             read (memory :> bytes128 (word_add kptr (word(16 * k)))) s =
             word_join4 (sha1_K (20*k)) (sha1_K (20*k))
                        (sha1_K (20*k)) (sha1_K (20*k))) /\
           read Q16 s =
             word_join4 (sha1_K 0) (sha1_K 0) (sha1_K 0) (sha1_K 0) /\
           read Q17 s =
             word_join4 (sha1_K 20) (sha1_K 20) (sha1_K 20) (sha1_K 20) /\
           read Q18 s =
             word_join4 (sha1_K 40) (sha1_K 40) (sha1_K 40) (sha1_K 40) /\
           read Q19 s =
             word_join4 (sha1_K 60) (sha1_K 60) (sha1_K 60) (sha1_K 60) /\
           read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
           read (memory :> bytes32 (word_add state_ptr (word 16))) s = e` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [

    (* ================================================================= *)
    (* Subgoal 1: INIT -- precondition + 7-instruction prologue ==>      *)
    (*            invariant(0) at pc+0x1c                                 *)
    (* Prologue: LDR Q0, LDR W4, INS_GEN Q1[0]=W4, LDR Q16-Q19           *)
    (* GHOST_INTRO_TAC binds initial Q1 so INS_GEN's chain isn't lost.   *)
    (* ================================================================= *)
    GHOST_INTRO_TAC `q1_init:int128` `read Q1` THEN
    ENSURES_INIT_TAC "s0" THEN
    EXPAND_K_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    ARM_STEPS_TAC SHA1_BLOCK_DATA_ORDER_HW_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[sha1_hash_blocks; WORD_ADD_0; MULT_CLAUSES; SUB_0] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    CONV_TAC WORD_BLAST;

    (* ================================================================= *)
    (* Subgoal 2: BODY -- invariant(i) at pc+0x1c ==>                    *)
    (*            invariant(i+1) at pc+0x1c0                             *)
    (*                                                                   *)
    (* Body executes pc+0x1c..pc+0x1bc (instrs 8..112).                  *)
    (* Pre-loop setup:                                                   *)
    (*   8..11: LDR Q4..Q7 from data_ptr (16-byte loads, raw bytes)     *)
    (*   12:    ADD X1, X1, #64    (advance data ptr)                    *)
    (*   13:    SUB X2, X2, #1     (decrement counter)                   *)
    (*   14..17: REV32 Q4..Q7      (byte-swap to logical layout)         *)
    (*   18:    MOV V22, V0        (save abcd for add-back)              *)
    (*   19..20: ADD V20=K0+W0,3, V21=K0+W4,7 (K+W bands)                *)
    (* Then 20 round groups (RG0..RG19) at 4 (RG0) or 5 (RG1+) instrs    *)
    (* per group, with K-band changes Q16->Q17->Q18->Q19 every 5 RGs.    *)
    (* Final 2 instrs (111,112): ADD Q1+=Q2, ADD Q0+=Q22 (e and abcd     *)
    (* add-back).                                                        *)
    (* ================================================================= *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `num_blocks - ii < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `num_blocks - ii` THEN
    GHOST_INTRO_TAC `q1_lane_init:int128` `read Q1` THEN
    ENSURES_INIT_TAC "s0" THEN
    EXPAND_K_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    EXPAND_DATA_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
    ARM_STEPS_TAC SHA1_BLOCK_DATA_ORDER_HW_EXEC (1--10) THEN
    REV32_BITBLAST_TAC `read Q4 s = x:int128`
      `read Q4 s10 = word_join4 ((EL 0 (EL ii blocks)):int32)
        (EL 1 (EL ii blocks)) (EL 2 (EL ii blocks))
        (EL 3 (EL ii blocks))` THEN
    REV32_BITBLAST_TAC `read Q5 s = x:int128`
      `read Q5 s10 = word_join4 ((EL 4 (EL ii blocks)):int32)
        (EL 5 (EL ii blocks)) (EL 6 (EL ii blocks))
        (EL 7 (EL ii blocks))` THEN
    REV32_BITBLAST_TAC `read Q6 s = x:int128`
      `read Q6 s10 = word_join4 ((EL 8 (EL ii blocks)):int32)
        (EL 9 (EL ii blocks)) (EL 10 (EL ii blocks))
        (EL 11 (EL ii blocks))` THEN
    REV32_BITBLAST_TAC `read Q7 s = x:int128`
      `read Q7 s10 = word_join4 ((EL 12 (EL ii blocks)):int32)
        (EL 13 (EL ii blocks)) (EL 14 (EL ii blocks))
        (EL 15 (EL ii blocks))` THEN
    ABBREV_TAC `w0 = (EL 0 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w1 = (EL 1 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w2 = (EL 2 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w3 = (EL 3 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w4 = (EL 4 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w5 = (EL 5 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w6 = (EL 6 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w7 = (EL 7 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w8 = (EL 8 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w9 = (EL 9 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w10 = (EL 10 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w11 = (EL 11 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w12 = (EL 12 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w13 = (EL 13 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w14 = (EL 14 (EL ii blocks)):int32` THEN
    ABBREV_TAC `w15 = (EL 15 (EL ii blocks)):int32` THEN
    ABBREV_TAC `W = sha1_message_schedule 64
      [w0:int32;w1;w2;w3;w4;w5;w6;w7;
       w8;w9;w10;w11;w12;w13;w14;w15]` THEN
    CHEAT_TAC;

    (* ================================================================= *)
    (* Subgoal 3: BACK-EDGE -- invariant(i) at pc+0x1c0 ==>              *)
    (*            invariant(i) at pc+0x1c (only for 0 < i < num_blocks) *)
    (* Just CBNZ X2, .Loop_hw — branches back since X2 = num_blocks-i!=0 *)
    (* ================================================================= *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    VAL_INT64_TAC `num_blocks - ii` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SHA1_BLOCK_DATA_ORDER_HW_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

    (* ================================================================= *)
    (* Subgoal 4: EXIT -- invariant(num_blocks) at pc+0x1c0 ==>          *)
    (*            postcondition at pc+0x1d0                              *)
    (* CBNZ falls through (x2=0), STR Q0, UMOV W4 Q1[0], STR W4 (4 instrs)*)
    (* RET (instr 117) at pc+0x1d0 is NOT executed; SUBROUTINE wraps it. *)
    (* ================================================================= *)
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                NONOVERLAPPING_CLAUSES; SUB_REFL] THEN
    VAL_INT64_TAC `num_blocks - num_blocks` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SHA1_BLOCK_DATA_ORDER_HW_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC WORD_BLAST
  ]);;
