(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 multi-block compression using scalar instructions only.           *)
(* Wraps the single-block scalar body in a block loop controlled by X2.      *)
(* Proved against sha256_hash_blocks from sha256_spec.ml.                    *)
(* ========================================================================= *)

needs "arm/proofs/sha256_block_scalar.ml";;

(* Machine code *)

let sha256_block_data_order_nohw_mc = define_from_elf
  "sha256_block_data_order_nohw_mc"
  (file_on_path !load_path "arm/sha2/sha256_block_data_order_nohw.o");;

let NOHW_EXEC = ARM_MK_EXEC_RULE sha256_block_data_order_nohw_mc;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for multi-block induction.                                  *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA256_HASH_BLOCKS_SCALAR = prove
 (`!n blocks H:int32 list. LENGTH H = 8
   ==> LENGTH(sha256_hash_blocks n blocks H) = 8`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha256_hash_blocks];
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha256_hash_blocks] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LENGTH_SHA256_BLOCK THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LENGTH_8_CONS = prove
 (`!L:A list. LENGTH L = 8 ==>
     ?a0 a1 a2 a3 a4 a5 a6 a7. L = [a0;a1;a2;a3;a4;a5;a6;a7]`,
  let suc8 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))` in
  REWRITE_TAC[GSYM suc8; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_8_EL = prove
 (`!L:A list. LENGTH L = 8 ==>
     L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L;
          EL 4 L; EL 5 L; EL 6 L; EL 7 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_8_CONS) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let SHA256_BLOCK_DATA_ORDER_NOHW_CORRECT = prove
 (`!num_blocks (blocks:(int32 list) list)
    (a:int32) b c d (e:int32) f g h
    state_ptr data_ptr kptr pc stackpointer.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,32); (stackpointer:int64,256)]
             [(word pc, 0x1c8);
              (data_ptr:int64, 64 * num_blocks);
              (kptr:int64, 256)] /\
    nonoverlapping (state_ptr,32) (stackpointer,256)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha256_block_data_order_nohw_mc /\
           read PC s = word (pc + 0x14) /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = data_ptr /\
           read X2 s = word num_blocks /\
           read X3 s = kptr /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t [a;b;c;d;e;f;g;h]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes32
                      (word_add data_ptr (word(64 * j + 4*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K))
      (\s. read PC s = word (pc + 0x1b0) /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t (sha256_hash_blocks num_blocks blocks
                        [a;b;c;d;e;f;g;h])))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26] ,,
       MAYCHANGE [memory :> bytes(state_ptr,32);
                  memory :> bytes(stackpointer,256)])`,
  let BIC_NORM = WORD_RULE
    `word_and (x:(N)word) (word_not y) = word_and (word_not y) x` in
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              fst NOHW_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_WHILE_UP_TAC `num_blocks:num` `pc + 0x14` `pc + 0x1ac`
    `\i s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = word_add data_ptr (word(64 * i)) /\
           read X2 s = word (num_blocks - i) /\
           read X3 s = kptr /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t (sha256_hash_blocks i blocks [a:int32;b;c;d;e;f;g;h])) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes32
                      (word_add data_ptr (word(64 * j + 4*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL

  [(* ===== num_blocks <> 0 ===== *)
   ASM_ARITH_TAC;

   (* ===== Init: pc+0x14 precondition implies invariant(0) ===== *)
   ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; SUB_0; sha256_hash_blocks];

   (* ===== Body: invariant(ii) at pc+0x14 => invariant(ii+1) at pc+0x1ac *)
   ALL_TAC;

   (* ===== Back-edge: invariant(ii) at pc+0x1ac => invariant(ii) at pc+0x14 *)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   SUBGOAL_THEN `num_blocks - i < 2 EXP 64` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   VAL_INT64_TAC `num_blocks - i` THEN
   ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC NOHW_EXEC [1] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   (* ===== Exit: invariant(num_blocks) at pc+0x1ac => postcondition at pc+0x1b0 *)
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
               NONOVERLAPPING_CLAUSES; SUB_REFL] THEN
   VAL_INT64_TAC `0` THEN
   ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC NOHW_EXEC (1--1) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  (* =================================================================== *)
  (* Body subgoal                                                        *)
  (* =================================================================== *)
  X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  SUBGOAL_THEN `num_blocks - ii < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `num_blocks - ii` THEN
  ABBREV_TAC `dptr_i = word_add data_ptr (word(64 * ii)):int64` THEN
  ABBREV_TAC `H_i = sha256_hash_blocks ii blocks [a:int32;b;c;d;e;f;g;h]` THEN
  SUBGOAL_THEN `LENGTH (H_i:int32 list) = 8` ASSUME_TAC THENL
   [EXPAND_TAC "H_i" THEN
    MATCH_MP_TAC LENGTH_SHA256_HASH_BLOCKS_SCALAR THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M_i = EL ii blocks:int32 list` THEN
  SUBGOAL_THEN `LENGTH (M_i:int32 list) = 16` ASSUME_TAC THENL
   [EXPAND_TAC "M_i" THEN
    UNDISCH_TAC `ALL (\bl:int32 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `H_i:int32 list` LIST_8_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `a_i = EL 0 H_i:int32` THEN
  ABBREV_TAC `b_i = EL 1 H_i:int32` THEN
  ABBREV_TAC `c_i = EL 2 H_i:int32` THEN
  ABBREV_TAC `d_i = EL 3 H_i:int32` THEN
  ABBREV_TAC `e_i = EL 4 H_i:int32` THEN
  ABBREV_TAC `f_i = EL 5 H_i:int32` THEN
  ABBREV_TAC `g_i = EL 6 H_i:int32` THEN
  ABBREV_TAC `h_i = EL 7 H_i:int32` THEN
  FIRST_ASSUM(fun th ->
    if is_eq (concl th) &&
       (try fst(dest_var(lhand(concl th))) = "H_i" with _ -> false)
    then ONCE_REWRITE_TAC[th] else FAIL_TAC "") THEN
  SUBGOAL_THEN
    `!t. word_add data_ptr (word(64 * ii + 4 * t):int64) =
         word_add dptr_i (word(4 * t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "dptr_i" THEN
    REWRITE_TAC[WORD_RULE
      `word_add (word_add d (word x:int64)) (word y) =
       word_add d (word (x + y))`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (* ===== Phase A: split at pc+0x30 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x30`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         (!t. t < 8 ==>
              read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
              EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes32
                    (word_add data_ptr (word(64 * j + 4*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add kptr (word(4*t)))) s =
              EL t sha256_K) /\
         (!t. t < 16 ==>
              read (memory :> bytes32(word_add stackpointer (word(4*t)))) s =
              EL t M_i)` THEN
  CONJ_TAC THENL

  [(* Phase A: load 16 words from dptr_i, REV, store to stackpointer *)
   ENSURES_WHILE_UP2_TAC `16` `pc + 0x18` `pc + 0x30`
    `\i s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = dptr_i /\
           read X2 s = word(num_blocks - ii) /\
           read X3 s = kptr /\
           read X17 s = word i /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes32
                      (word_add data_ptr (word(64 * j + 4*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K) /\
           (!t. t < i ==>
                read (memory :> bytes32(word_add stackpointer (word(4*t)))) s =
                EL t M_i)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ARITH_TAC;
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC NOHW_EXEC (1--1) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LT] THEN MESON_TAC[];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `i < 16` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `word_shl (word i:int64) 2 = word (4 * i)` ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `val (word i:int64) = i` ASSUME_TAC THENL
      [ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `read (memory :> bytes32 (word_add dptr_i (word (4 * i)))) s0 =
       word_bytereverse (EL i M_i)`
     ASSUME_TAC THENL
      [FIRST_X_ASSUM(fun th ->
         MP_TAC(SPECL [`ii:num`; `i:num`] th) THEN
         ANTS_TAC THENL
          [UNDISCH_TAC `ii < num_blocks` THEN UNDISCH_TAC `i < 16` THEN
           ARITH_TAC;
           ALL_TAC]) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ARM_STEPS_TAC NOHW_EXEC (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 16 ==> i < 2 EXP 64`;
                    ARITH_RULE `18446744073709551601 < 2 EXP 64`] THEN
       ASM_CASES_TAC `i + 1 = 16` THENL
        [ASM_REWRITE_TAC[LT_REFL] THEN
         SUBGOAL_THEN `i = 15` SUBST1_TAC THENL
          [UNDISCH_TAC `i + 1 = 16` THEN ARITH_TAC; ALL_TAC] THEN
         CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
         SUBGOAL_THEN `i + 1 < 16` ASSUME_TAC THENL
          [UNDISCH_TAC `i < 16` THEN UNDISCH_TAC `~(i + 1 = 16)` THEN
           ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~((i + 18446744073709551601) MOD 2 EXP 64 = 0)`
           ASSUME_TAC THENL
          [SUBGOAL_THEN
             `(i + 18446744073709551601) MOD 2 EXP 64 =
              i + 18446744073709551601` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN
             UNDISCH_TAC `i + 1 < 16` THEN ARITH_TAC; ALL_TAC] THEN
           UNDISCH_TAC `i + 1 < 16` THEN ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[]];
       CONV_TAC WORD_RULE;
       GEN_TAC THEN DISCH_TAC THEN
       ASM_CASES_TAC `t < i` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `t:num = i` SUBST_ALL_TAC THENL
        [UNDISCH_TAC `t < i + 1` THEN UNDISCH_TAC `~(t < i)` THEN
         ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
       SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_32; DIMINDEX_64;
                LE_REFL; ARITH] THEN
       REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE]];
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[]];

   ALL_TAC] THEN

  (* ===== Phase B: split at pc+0x90 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x90`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         (!t. t < 8 ==>
              read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
              EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes32
                    (word_add data_ptr (word(64 * j + 4*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add kptr (word(4*t)))) s =
              EL t sha256_K) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add stackpointer (word(4*t)))) s =
              EL t (sha256_message_schedule 48 M_i))` THEN
  CONJ_TAC THENL

  [(* Phase B: extend message schedule on stack *)
   ENSURES_SEQUENCE_TAC `pc + 0x38`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X4 s = stackpointer /\
         read X3 s = kptr /\
         read X17 s = word 0 /\
         (!t. t < 8 ==>
              read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
              EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes32
                    (word_add data_ptr (word(64 * j + 4*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add kptr (word(4*t)))) s =
              EL t sha256_K) /\
         (!t. t < 16 ==>
              read (memory :> bytes32(word_add stackpointer (word(4*t)))) s =
              EL t M_i)` THEN
   CONJ_TAC THENL
    [ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC NOHW_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN

   ENSURES_WHILE_UP2_TAC `48` `pc + 0x38` `pc + 0x90`
    `\i s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = dptr_i /\
           read X2 s = word(num_blocks - ii) /\
           read X4 s = word_add stackpointer (word (4 * i)) /\
           read X3 s = kptr /\
           read X17 s = word i /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes32
                      (word_add data_ptr (word(64 * j + 4*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K) /\
           (!t. t < i + 16 ==>
                read (memory :> bytes32(word_add stackpointer (word(4*t)))) s =
                EL t (sha256_message_schedule i M_i))` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ARITH_TAC;
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; sha256_message_schedule;
                     ADD_CLAUSES];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `word_add (word_add stackpointer (word (4 * i))) (word 0):int64 =
         word_add stackpointer (word(4 * i)) /\
       word_add (word_add stackpointer (word (4 * i))) (word 4):int64 =
         word_add stackpointer (word(4 * (i+1))) /\
       word_add (word_add stackpointer (word (4 * i))) (word 36):int64 =
         word_add stackpointer (word(4 * (i+9))) /\
       word_add (word_add stackpointer (word (4 * i))) (word 56):int64 =
         word_add stackpointer (word(4 * (i+14))) /\
       word_add (word_add stackpointer (word (4 * i))) (word 64):int64 =
         word_add stackpointer (word(4 * (i+16)))`
     STRIP_ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
     SUBGOAL_THEN
      `read (memory :> bytes32 (word_add stackpointer (word (4 * i)))) s0 =
       EL i (sha256_message_schedule i M_i) /\
       read (memory :> bytes32 (word_add stackpointer (word (4 * (i+1))))) s0 =
       EL (i+1) (sha256_message_schedule i M_i) /\
       read (memory :> bytes32 (word_add stackpointer (word (4 * (i+9))))) s0 =
       EL (i+9) (sha256_message_schedule i M_i) /\
       read (memory :> bytes32 (word_add stackpointer (word (4 * (i+14))))) s0 =
       EL (i+14) (sha256_message_schedule i M_i)`
     STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `i < 48` THEN ARITH_TAC;
       ALL_TAC] THEN
     ARM_STEPS_TAC NOHW_EXEC (1--22) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 48 ==> i < 2 EXP 64`;
                    ARITH_RULE `18446744073709551569 < 2 EXP 64`] THEN
       ASM_CASES_TAC `i + 1 = 48` THENL
        [ASM_REWRITE_TAC[LT_REFL] THEN
         SUBGOAL_THEN `i = 47` SUBST1_TAC THENL
          [UNDISCH_TAC `i + 1 = 48` THEN ARITH_TAC; ALL_TAC] THEN
         CONV_TAC NUM_REDUCE_CONV;
         SUBGOAL_THEN `i + 1 < 48` ASSUME_TAC THENL
          [UNDISCH_TAC `i < 48` THEN UNDISCH_TAC `~(i + 1 = 48)` THEN
           ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~((i + 18446744073709551569) MOD 2 EXP 64 = 0)`
           ASSUME_TAC THENL
          [SUBGOAL_THEN
             `(i + 18446744073709551569) MOD 2 EXP 64 =
              i + 18446744073709551569` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN
             UNDISCH_TAC `i + 1 < 48` THEN ARITH_TAC; ALL_TAC] THEN
           UNDISCH_TAC `i + 1 < 48` THEN ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[]];
       CONV_TAC WORD_RULE;
       GEN_TAC THEN DISCH_TAC THEN
       ASM_CASES_TAC `t < i + 16` THENL
        [SUBGOAL_THEN
          `EL t (sha256_message_schedule (i+1) M_i) =
           EL t (sha256_message_schedule i M_i)`
         SUBST1_TAC THENL
          [MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN
           ASM_REWRITE_TAC[] THEN
           UNDISCH_TAC `t < i + 16` THEN ARITH_TAC;
           ALL_TAC] THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       SUBGOAL_THEN `t = i + 16` SUBST_ALL_TAC THENL
        [UNDISCH_TAC `t < (i + 1) + 16` THEN UNDISCH_TAC `~(t < i + 16)` THEN
         ARITH_TAC; ALL_TAC] THEN
       MP_TAC(SPECL [`i:num`; `M_i:int32 list`] SHA256_SCHEDULE_NEWEST) THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
       SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
       SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                WORD_ZX_TRIVIAL] THEN
       CONV_TAC WORD_RULE];
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     UNDISCH_TAC `t < 64` THEN ARITH_TAC];

   ALL_TAC] THEN

  (* ===== Phase C: split at pc+0xd0 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xd0`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X4 s = word_zx (a_i:int32) /\
         read X5 s = word_zx (b_i:int32) /\
         read X6 s = word_zx (c_i:int32) /\
         read X7 s = word_zx (d_i:int32) /\
         read X8 s = word_zx (e_i:int32) /\
         read X9 s = word_zx (f_i:int32) /\
         read X10 s = word_zx (g_i:int32) /\
         read X11 s = word_zx (h_i:int32) /\
         read X19 s = word_zx (a_i:int32) /\
         read X20 s = word_zx (b_i:int32) /\
         read X21 s = word_zx (c_i:int32) /\
         read X22 s = word_zx (d_i:int32) /\
         read X23 s = word_zx (e_i:int32) /\
         read X24 s = word_zx (f_i:int32) /\
         read X25 s = word_zx (g_i:int32) /\
         read X26 s = word_zx (h_i:int32) /\
         (!t. t < 8 ==>
              read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
              EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes32
                    (word_add data_ptr (word(64 * j + 4*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add kptr (word(4*t)))) s =
              EL t sha256_K) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add stackpointer (word(4*t)))) s =
              EL t (sha256_message_schedule 48 M_i))` THEN
  CONJ_TAC THENL

  [(* Phase C: load state into W4..W11 and save to W19..W26 *)
   ENSURES_INIT_TAC "s0" THEN
   MAP_EVERY (fun k ->
     let th = SPECL [k] (ASSUME
      `forall t.
           t < 8
           ==> read (memory :> bytes32 (word_add state_ptr (word (4 * t)))) s0 =
               EL t [a_i:int32; b_i; c_i; d_i; e_i; f_i; g_i; h_i]`) in
     MP_TAC th THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH; EL; HD; TL] THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     REWRITE_TAC[WORD_ADD_0] THEN
     DISCH_TAC)
    [`0`; `1`; `2`; `3`; `4`; `5`; `6`; `7`] THEN
   ARM_STEPS_TAC NOHW_EXEC (1--16) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
   REWRITE_TAC[EL; HD; TL] THEN
   CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];

   ALL_TAC] THEN

  (* ===== Phase D: split at pc+0x164 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x164`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X4 s = word_zx (EL 0 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X5 s = word_zx (EL 1 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X6 s = word_zx (EL 2 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X7 s = word_zx (EL 3 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X8 s = word_zx (EL 4 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X9 s = word_zx (EL 5 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X10 s = word_zx (EL 6 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X11 s = word_zx (EL 7 (sha256_compress 64
                    (sha256_message_schedule 48 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X19 s = word_zx (a_i:int32) /\
         read X20 s = word_zx (b_i:int32) /\
         read X21 s = word_zx (c_i:int32) /\
         read X22 s = word_zx (d_i:int32) /\
         read X23 s = word_zx (e_i:int32) /\
         read X24 s = word_zx (f_i:int32) /\
         read X25 s = word_zx (g_i:int32) /\
         read X26 s = word_zx (h_i:int32) /\
         (!t. t < 8 ==>
              read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
              EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes32
                    (word_add data_ptr (word(64 * j + 4*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add kptr (word(4*t)))) s =
              EL t sha256_K)` THEN
  CONJ_TAC THENL

  [(* Phase D: 64-round compression loop *)
   ABBREV_TAC `W = sha256_message_schedule 48 M_i` THEN
   ENSURES_WHILE_UP2_TAC `64` `pc + 0xd4` `pc + 0x164`
    `\i s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = dptr_i /\
           read X2 s = word(num_blocks - ii) /\
           read X3 s = kptr /\
           read X17 s = word i /\
           read X4 s = word_zx (EL 0 (sha256_compress i W
                                      [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X5 s = word_zx (EL 1 (sha256_compress i W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X6 s = word_zx (EL 2 (sha256_compress i W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X7 s = word_zx (EL 3 (sha256_compress i W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X8 s = word_zx (EL 4 (sha256_compress i W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X9 s = word_zx (EL 5 (sha256_compress i W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X10 s = word_zx (EL 6 (sha256_compress i W
                                       [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X11 s = word_zx (EL 7 (sha256_compress i W
                                       [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X19 s = word_zx (a_i:int32) /\
           read X20 s = word_zx (b_i:int32) /\
           read X21 s = word_zx (c_i:int32) /\
           read X22 s = word_zx (d_i:int32) /\
           read X23 s = word_zx (e_i:int32) /\
           read X24 s = word_zx (f_i:int32) /\
           read X25 s = word_zx (g_i:int32) /\
           read X26 s = word_zx (h_i:int32) /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes32
                      (word_add data_ptr (word(64 * j + 4*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add stackpointer (word(4*t)))) s =
                EL t W) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ARITH_TAC;
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC NOHW_EXEC (1--1) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[sha256_compress] THEN
     CONV_TAC(DEPTH_CONV EL_CONV) THEN
     REWRITE_TAC[];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `i < 64` THEN ARITH_TAC; ALL_TAC] THEN
     ABBREV_TAC `sc_i = sha256_compress i W
                        [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]` THEN
     SUBGOAL_THEN
      `sha256_compress (i+1) W [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i] =
       sha256_compress_round (EL i sha256_K) (EL i W)
        [EL 0 sc_i; EL 1 sc_i; EL 2 sc_i; EL 3 sc_i; EL 4 sc_i; EL 5 sc_i;
         EL 6 sc_i; EL 7 sc_i]`
     SUBST1_TAC THENL
      [REWRITE_TAC[sha256_compress; SHA256_COMPRESS_ROUND_EL_LIST] THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MAP_EVERY ABBREV_TAC
      [`K_t = (EL i sha256_K):int32`; `W_t = (EL i W):int32`] THEN
     REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                 sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
     SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
     REWRITE_TAC[DIMINDEX_32; EL; HD; TL; ARITH] THEN
     CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[GSYM(CONJUNCT1 EL)] THEN
     SUBGOAL_THEN `word_shl (word i:int64) 2 = word (4 * i)` ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `val (word i:int64) = i` ASSUME_TAC THENL
      [ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `read (memory :> bytes32 (word_add kptr (word (4 * i)))) s0 = K_t /\
       read (memory :> bytes32 (word_add stackpointer (word (4 * i)))) s0 =
       W_t`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     ARM_STEPS_TAC NOHW_EXEC (1--36) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
              WORD_ZX_TRIVIAL] THEN
     REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD;
                   VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 64
                      ==> i < 2 EXP 64 /\ i < 2 EXP 32 /\
                          1 < 2 EXP 32 /\ 64 < 2 EXP 32 /\
                          i + 1 < 2 EXP 32`;
                    ARITH_RULE `18446744073709551553 < 2 EXP 64`] THEN
       ASM_CASES_TAC `i + 1 = 64` THENL
        [ASM_REWRITE_TAC[LT_REFL] THEN
         SUBGOAL_THEN `i = 63` SUBST1_TAC THENL
          [UNDISCH_TAC `i + 1 = 64` THEN ARITH_TAC; ALL_TAC] THEN
         CONV_TAC NUM_REDUCE_CONV;
         SUBGOAL_THEN `i + 1 < 64` ASSUME_TAC THENL
          [UNDISCH_TAC `i < 64` THEN UNDISCH_TAC `~(i + 1 = 64)` THEN
           ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~((i + 18446744073709551553) MOD 2 EXP 64 = 0)` ASSUME_TAC
         THENL
          [SUBGOAL_THEN
             `(i + 18446744073709551553) MOD 2 EXP 64 =
              i + 18446744073709551553` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN
             UNDISCH_TAC `i + 1 < 64` THEN ARITH_TAC; ALL_TAC] THEN
           UNDISCH_TAC `i + 1 < 64` THEN ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[]];
       ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
       REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                   DIMINDEX_32; DIMINDEX_64] THEN
       SIMP_TAC[MOD_LT; ARITH_RULE `1 < 2 EXP 32`] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 64
                      ==> i < 2 EXP 32 /\ i + 1 < 2 EXP 32 /\
                          i + 1 < 2 EXP 64`] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       MATCH_MP_TAC MOD_LT THEN
       UNDISCH_TAC `i < 64` THEN ARITH_TAC;
       REWRITE_TAC[BIC_NORM];
       REWRITE_TAC[BIC_NORM]];
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[]];

   ALL_TAC] THEN

  (* ===== Phase E: split at pc+0x184 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x184`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X4 s = word_zx (word_add
            (EL 0 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) a_i) /\
         read X5 s = word_zx (word_add
            (EL 1 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) b_i) /\
         read X6 s = word_zx (word_add
            (EL 2 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) c_i) /\
         read X7 s = word_zx (word_add
            (EL 3 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) d_i) /\
         read X8 s = word_zx (word_add
            (EL 4 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) e_i) /\
         read X9 s = word_zx (word_add
            (EL 5 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) f_i) /\
         read X10 s = word_zx (word_add
            (EL 6 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) g_i) /\
         read X11 s = word_zx (word_add
            (EL 7 (sha256_compress 64
                   (sha256_message_schedule 48 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) h_i) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes32
                    (word_add data_ptr (word(64 * j + 4*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 64 ==>
              read (memory :> bytes32(word_add kptr (word(4*t)))) s =
              EL t sha256_K)` THEN
  CONJ_TAC THENL

  [(* Phase E: 8 ADDs for add-back *)
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC NOHW_EXEC (1--8) THEN
   ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
            WORD_ZX_TRIVIAL] THEN
   REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
   REPEAT CONJ_TAC THEN
   (CONV_TAC WORD_RULE ORELSE ASM_REWRITE_TAC[]);

   ALL_TAC] THEN

  (* ===== Phase F + postamble: 8 stores + add x1 + sub x2 ===== *)
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC NOHW_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* X1 = word_add data_ptr (word(64 * (ii + 1))) *)
    EXPAND_TAC "dptr_i" THEN CONV_TAC WORD_RULE;
    (* X2 = word(num_blocks - (ii + 1)) *)
    SUBGOAL_THEN `num_blocks - ii = (num_blocks - (ii + 1)) + 1` ASSUME_TAC THENL
     [UNDISCH_TAC `ii < num_blocks` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    (* memory read at state_ptr: EL t (sha256_hash_blocks (ii+1) blocks H0) *)
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `ii + 1 = SUC ii`;
                sha256_hash_blocks;
                ARITH_RULE `SUC ii = ii + 1`] THEN
    EXPAND_TAC "M_i" THEN EXPAND_TAC "H_i" THEN
    MP_TAC(SPECL [`M_i:int32 list`;
                  `[a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`] SHA256_BLOCK_EL) THEN
    ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:num`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `sha256_block M_i H_i = sha256_block M_i [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC(`t:num`,`t:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD; TL] THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
    REWRITE_TAC[GSYM(CONJUNCT1 EL)]]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper.                                                       *)
(* ------------------------------------------------------------------------- *)

let SHA256_BLOCK_DATA_ORDER_NOHW_SUBROUTINE_CORRECT = prove
 (`!num_blocks (blocks:(int32 list) list)
    (a:int32) b c d (e:int32) f g h
    state_ptr data_ptr kptr pc stackpointer returnaddress.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    nonoverlapping (state_ptr,32)
                   (word_sub stackpointer (word 320), 320) /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,32);
              (word_sub stackpointer (word 320):int64, 320)]
             [(word pc, 0x1c8);
              (data_ptr:int64, 64 * num_blocks);
              (kptr:int64, 256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha256_block_data_order_nohw_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           read X0 s = state_ptr /\
           read X1 s = data_ptr /\
           read X2 s = word num_blocks /\
           read X3 s = kptr /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t [a;b;c;d;e;f;g;h]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes32
                      (word_add data_ptr (word(64 * j + 4*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K))
      (\s. read PC s = returnaddress /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t (sha256_hash_blocks num_blocks blocks
                        [a;b;c;d;e;f;g;h])))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(state_ptr,32);
                  memory :> bytes(word_sub stackpointer (word 320), 320)])`,
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) NOHW_EXEC
        SHA256_BLOCK_DATA_ORDER_NOHW_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26]` 320);;
