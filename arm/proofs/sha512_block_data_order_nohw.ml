(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-512 multi-block compression using scalar instructions only.           *)
(* Direct 64-bit analogue of sha256_block_data_order_nohw.ml, proved         *)
(* against sha512_hash_blocks from sha512_spec.ml. No hw crypto.             *)
(* ========================================================================= *)

needs "arm/proofs/utils/sha512_bridge.ml";;

(* Machine code *)

let sha512_block_data_order_nohw_mc = define_from_elf
  "sha512_block_data_order_nohw_mc"
  (file_on_path !load_path "arm/sha2/sha512_block_data_order_nohw.o");;

let NOHW_EXEC = ARM_MK_EXEC_RULE sha512_block_data_order_nohw_mc;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for multi-block induction.                                  *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA512_HASH_BLOCKS_SCALAR = prove
 (`!n blocks H:int64 list. LENGTH H = 8
   ==> LENGTH(sha512_hash_blocks n blocks H) = 8`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha512_hash_blocks];
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha512_hash_blocks] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LENGTH_SHA512_BLOCK THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LENGTH_8_CONS_64 = prove
 (`!L:A list. LENGTH L = 8 ==>
     ?a0 a1 a2 a3 a4 a5 a6 a7. L = [a0;a1;a2;a3;a4;a5;a6;a7]`,
  let suc8 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))` in
  REWRITE_TAC[GSYM suc8; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_8_EL_64 = prove
 (`!L:A list. LENGTH L = 8 ==>
     L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L;
          EL 4 L; EL 5 L; EL 6 L; EL 7 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_8_CONS_64) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* 8-element destructure lemma for EL_CONV on sha512_compress_round outputs. *)

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

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let SHA512_BLOCK_DATA_ORDER_NOHW_CORRECT = prove
 (`!num_blocks (blocks:(int64 list) list)
    (a:int64) b c d (e:int64) f g h
    state_ptr data_ptr kptr pc stackpointer.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,64); (stackpointer:int64,640)]
             [(word pc, 0x1c8);
              (data_ptr:int64, 128 * num_blocks);
              (kptr:int64, 640)] /\
    nonoverlapping (state_ptr,64) (stackpointer,640)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha512_block_data_order_nohw_mc /\
           read PC s = word (pc + 0x14) /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = data_ptr /\
           read X2 s = word num_blocks /\
           read X3 s = kptr /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t [a;b;c;d;e;f;g;h]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes64
                      (word_add data_ptr (word(128 * j + 8*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 80 ==>
                read (memory :> bytes64(word_add kptr (word(8*t)))) s =
                EL t sha512_K))
      (\s. read PC s = word (pc + 0x1b0) /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t (sha512_hash_blocks num_blocks blocks
                        [a;b;c;d;e;f;g;h])))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26] ,,
       MAYCHANGE [memory :> bytes(state_ptr,64);
                  memory :> bytes(stackpointer,640)])`,
  let BIC_NORM = WORD_RULE
    `word_and (x:(N)word) (word_not y) = word_and (word_not y) x` in
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              fst NOHW_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_WHILE_UP_TAC `num_blocks:num` `pc + 0x14` `pc + 0x1ac`
    `\i s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = word_add data_ptr (word(128 * i)) /\
           read X2 s = word (num_blocks - i) /\
           read X3 s = kptr /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t (sha512_hash_blocks i blocks [a:int64;b;c;d;e;f;g;h])) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes64
                      (word_add data_ptr (word(128 * j + 8*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 80 ==>
                read (memory :> bytes64(word_add kptr (word(8*t)))) s =
                EL t sha512_K)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL

  [(* ===== num_blocks <> 0 ===== *)
   ASM_ARITH_TAC;

   (* ===== Init: pc+0x14 precondition implies invariant(0) ===== *)
   ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; SUB_0; sha512_hash_blocks];

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
  ABBREV_TAC `dptr_i = word_add data_ptr (word(128 * ii)):int64` THEN
  ABBREV_TAC `H_i = sha512_hash_blocks ii blocks [a:int64;b;c;d;e;f;g;h]` THEN
  SUBGOAL_THEN `LENGTH (H_i:int64 list) = 8` ASSUME_TAC THENL
   [EXPAND_TAC "H_i" THEN
    MATCH_MP_TAC LENGTH_SHA512_HASH_BLOCKS_SCALAR THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M_i = EL ii blocks:int64 list` THEN
  SUBGOAL_THEN `LENGTH (M_i:int64 list) = 16` ASSUME_TAC THENL
   [EXPAND_TAC "M_i" THEN
    UNDISCH_TAC `ALL (\bl:int64 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `H_i:int64 list` LIST_8_EL_64) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `a_i = EL 0 H_i:int64` THEN
  ABBREV_TAC `b_i = EL 1 H_i:int64` THEN
  ABBREV_TAC `c_i = EL 2 H_i:int64` THEN
  ABBREV_TAC `d_i = EL 3 H_i:int64` THEN
  ABBREV_TAC `e_i = EL 4 H_i:int64` THEN
  ABBREV_TAC `f_i = EL 5 H_i:int64` THEN
  ABBREV_TAC `g_i = EL 6 H_i:int64` THEN
  ABBREV_TAC `h_i = EL 7 H_i:int64` THEN
  FIRST_ASSUM(fun th ->
    if is_eq (concl th) &&
       (try fst(dest_var(lhand(concl th))) = "H_i" with _ -> false)
    then ONCE_REWRITE_TAC[th] else FAIL_TAC "") THEN
  SUBGOAL_THEN
    `!t. word_add data_ptr (word(128 * ii + 8 * t):int64) =
         word_add dptr_i (word(8 * t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "dptr_i" THEN
    REWRITE_TAC[WORD_RULE
      `word_add (word_add d (word x:int64)) (word y) =
       word_add d (word (x + y))`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (* ===== Phase A: split at pc+0x30 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x30`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         (!t. t < 8 ==>
              read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
              EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes64
                    (word_add data_ptr (word(128 * j + 8*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add kptr (word(8*t)))) s =
              EL t sha512_K) /\
         (!t. t < 16 ==>
              read (memory :> bytes64(word_add stackpointer (word(8*t)))) s =
              EL t M_i)` THEN
  CONJ_TAC THENL

  [(* Phase A: load 16 words from dptr_i, REV, store to stackpointer *)
   ENSURES_WHILE_UP2_TAC `16` `pc + 0x18` `pc + 0x30`
    `\i s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = dptr_i /\
           read X2 s = word(num_blocks - ii) /\
           read X3 s = kptr /\
           read X17 s = word i /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes64
                      (word_add data_ptr (word(128 * j + 8*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 80 ==>
                read (memory :> bytes64(word_add kptr (word(8*t)))) s =
                EL t sha512_K) /\
           (!t. t < i ==>
                read (memory :> bytes64(word_add stackpointer (word(8*t)))) s =
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
     SUBGOAL_THEN `word_shl (word i:int64) 3 = word (8 * i)` ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `val (word i:int64) = i` ASSUME_TAC THENL
      [ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `read (memory :> bytes64 (word_add dptr_i (word (8 * i)))) s0 =
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
       ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE]];
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[]];

   ALL_TAC] THEN

  (* ===== Phase B: split at pc+0x90 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x90`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         (!t. t < 8 ==>
              read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
              EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes64
                    (word_add data_ptr (word(128 * j + 8*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add kptr (word(8*t)))) s =
              EL t sha512_K) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add stackpointer (word(8*t)))) s =
              EL t (sha512_message_schedule 64 M_i))` THEN
  CONJ_TAC THENL

  [(* Phase B: extend message schedule on stack *)
   ENSURES_SEQUENCE_TAC `pc + 0x38`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X4 s = stackpointer /\
         read X3 s = kptr /\
         read X17 s = word 0 /\
         (!t. t < 8 ==>
              read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
              EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes64
                    (word_add data_ptr (word(128 * j + 8*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add kptr (word(8*t)))) s =
              EL t sha512_K) /\
         (!t. t < 16 ==>
              read (memory :> bytes64(word_add stackpointer (word(8*t)))) s =
              EL t M_i)` THEN
   CONJ_TAC THENL
    [ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC NOHW_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN

   ENSURES_WHILE_UP2_TAC `64` `pc + 0x38` `pc + 0x90`
    `\i s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = dptr_i /\
           read X2 s = word(num_blocks - ii) /\
           read X4 s = word_add stackpointer (word (8 * i)) /\
           read X3 s = kptr /\
           read X17 s = word i /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes64
                      (word_add data_ptr (word(128 * j + 8*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 80 ==>
                read (memory :> bytes64(word_add kptr (word(8*t)))) s =
                EL t sha512_K) /\
           (!t. t < i + 16 ==>
                read (memory :> bytes64(word_add stackpointer (word(8*t)))) s =
                EL t (sha512_message_schedule i M_i))` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ARITH_TAC;
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; sha512_message_schedule;
                     ADD_CLAUSES];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `word_add (word_add stackpointer (word (8 * i))) (word 0):int64 =
         word_add stackpointer (word(8 * i)) /\
       word_add (word_add stackpointer (word (8 * i))) (word 8):int64 =
         word_add stackpointer (word(8 * (i+1))) /\
       word_add (word_add stackpointer (word (8 * i))) (word 72):int64 =
         word_add stackpointer (word(8 * (i+9))) /\
       word_add (word_add stackpointer (word (8 * i))) (word 112):int64 =
         word_add stackpointer (word(8 * (i+14))) /\
       word_add (word_add stackpointer (word (8 * i))) (word 128):int64 =
         word_add stackpointer (word(8 * (i+16)))`
     STRIP_ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
     SUBGOAL_THEN
      `read (memory :> bytes64 (word_add stackpointer (word (8 * i)))) s0 =
       EL i (sha512_message_schedule i M_i) /\
       read (memory :> bytes64 (word_add stackpointer (word (8 * (i+1))))) s0 =
       EL (i+1) (sha512_message_schedule i M_i) /\
       read (memory :> bytes64 (word_add stackpointer (word (8 * (i+9))))) s0 =
       EL (i+9) (sha512_message_schedule i M_i) /\
       read (memory :> bytes64 (word_add stackpointer (word (8 * (i+14))))) s0 =
       EL (i+14) (sha512_message_schedule i M_i)`
     STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `i < 64` THEN ARITH_TAC;
       ALL_TAC] THEN
     ARM_STEPS_TAC NOHW_EXEC (1--22) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 64 ==> i < 2 EXP 64`;
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
         SUBGOAL_THEN `~((i + 18446744073709551553) MOD 2 EXP 64 = 0)`
           ASSUME_TAC THENL
          [SUBGOAL_THEN
             `(i + 18446744073709551553) MOD 2 EXP 64 =
              i + 18446744073709551553` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN
             UNDISCH_TAC `i + 1 < 64` THEN ARITH_TAC; ALL_TAC] THEN
           UNDISCH_TAC `i + 1 < 64` THEN ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[]];
       CONV_TAC WORD_RULE;
       GEN_TAC THEN DISCH_TAC THEN
       ASM_CASES_TAC `t < i + 16` THENL
        [SUBGOAL_THEN
          `EL t (sha512_message_schedule (i+1) M_i) =
           EL t (sha512_message_schedule i M_i)`
         SUBST1_TAC THENL
          [MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN
           ASM_REWRITE_TAC[] THEN
           UNDISCH_TAC `t < i + 16` THEN ARITH_TAC;
           ALL_TAC] THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       SUBGOAL_THEN `t = i + 16` SUBST_ALL_TAC THENL
        [UNDISCH_TAC `t < (i + 1) + 16` THEN UNDISCH_TAC `~(t < i + 16)` THEN
         ARITH_TAC; ALL_TAC] THEN
       MP_TAC(SPECL [`i:num`; `M_i:int64 list`] SHA512_SCHEDULE_NEWEST) THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
       SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
       CONV_TAC WORD_RULE];
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     UNDISCH_TAC `t < 80` THEN ARITH_TAC];

   ALL_TAC] THEN

  (* ===== Phase C: split at pc+0xd0 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xd0`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X4 s = (a_i:int64) /\
         read X5 s = (b_i:int64) /\
         read X6 s = (c_i:int64) /\
         read X7 s = (d_i:int64) /\
         read X8 s = (e_i:int64) /\
         read X9 s = (f_i:int64) /\
         read X10 s = (g_i:int64) /\
         read X11 s = (h_i:int64) /\
         read X19 s = (a_i:int64) /\
         read X20 s = (b_i:int64) /\
         read X21 s = (c_i:int64) /\
         read X22 s = (d_i:int64) /\
         read X23 s = (e_i:int64) /\
         read X24 s = (f_i:int64) /\
         read X25 s = (g_i:int64) /\
         read X26 s = (h_i:int64) /\
         (!t. t < 8 ==>
              read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
              EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes64
                    (word_add data_ptr (word(128 * j + 8*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add kptr (word(8*t)))) s =
              EL t sha512_K) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add stackpointer (word(8*t)))) s =
              EL t (sha512_message_schedule 64 M_i))` THEN
  CONJ_TAC THENL

  [(* Phase C: load state into X4..X11 and save to X19..X26 *)
   ENSURES_INIT_TAC "s0" THEN
   MAP_EVERY (fun k ->
     let th = SPECL [k] (ASSUME
      `forall t.
           t < 8
           ==> read (memory :> bytes64 (word_add state_ptr (word (8 * t)))) s0 =
               EL t [a_i:int64; b_i; c_i; d_i; e_i; f_i; g_i; h_i]`) in
     MP_TAC th THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH; EL; HD; TL] THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     REWRITE_TAC[WORD_ADD_0] THEN
     DISCH_TAC)
    [`0`; `1`; `2`; `3`; `4`; `5`; `6`; `7`] THEN
   ARM_STEPS_TAC NOHW_EXEC (1--16) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[EL; HD; TL] THEN
   CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];

   ALL_TAC] THEN

  (* ===== Phase D: split at pc+0x164 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x164`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X4 s = EL 0 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X5 s = EL 1 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X6 s = EL 2 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X7 s = EL 3 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X8 s = EL 4 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X9 s = EL 5 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X10 s = EL 6 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X11 s = EL 7 (sha512_compress 80
                    (sha512_message_schedule 64 M_i)
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         read X19 s = (a_i:int64) /\
         read X20 s = (b_i:int64) /\
         read X21 s = (c_i:int64) /\
         read X22 s = (d_i:int64) /\
         read X23 s = (e_i:int64) /\
         read X24 s = (f_i:int64) /\
         read X25 s = (g_i:int64) /\
         read X26 s = (h_i:int64) /\
         (!t. t < 8 ==>
              read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
              EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes64
                    (word_add data_ptr (word(128 * j + 8*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add kptr (word(8*t)))) s =
              EL t sha512_K)` THEN
  CONJ_TAC THENL

  [(* Phase D: 80-round compression loop *)
   ABBREV_TAC `W = sha512_message_schedule 64 M_i` THEN
   ENSURES_WHILE_UP2_TAC `80` `pc + 0xd4` `pc + 0x164`
    `\i s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
           read SP s = stackpointer /\
           read X0 s = state_ptr /\
           read X1 s = dptr_i /\
           read X2 s = word(num_blocks - ii) /\
           read X3 s = kptr /\
           read X17 s = word i /\
           read X4 s = EL 0 (sha512_compress i W
                             [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X5 s = EL 1 (sha512_compress i W
                             [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X6 s = EL 2 (sha512_compress i W
                             [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X7 s = EL 3 (sha512_compress i W
                             [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X8 s = EL 4 (sha512_compress i W
                             [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X9 s = EL 5 (sha512_compress i W
                             [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X10 s = EL 6 (sha512_compress i W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X11 s = EL 7 (sha512_compress i W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           read X19 s = (a_i:int64) /\
           read X20 s = (b_i:int64) /\
           read X21 s = (c_i:int64) /\
           read X22 s = (d_i:int64) /\
           read X23 s = (e_i:int64) /\
           read X24 s = (f_i:int64) /\
           read X25 s = (g_i:int64) /\
           read X26 s = (h_i:int64) /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes64
                      (word_add data_ptr (word(128 * j + 8*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 80 ==>
                read (memory :> bytes64(word_add stackpointer (word(8*t)))) s =
                EL t W) /\
           (!t. t < 80 ==>
                read (memory :> bytes64(word_add kptr (word(8*t)))) s =
                EL t sha512_K)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ARITH_TAC;
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC NOHW_EXEC (1--1) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[sha512_compress] THEN
     CONV_TAC(DEPTH_CONV EL_CONV) THEN
     REWRITE_TAC[];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `i < 80` THEN ARITH_TAC; ALL_TAC] THEN
     ABBREV_TAC `sc_i = sha512_compress i W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]` THEN
     SUBGOAL_THEN
      `sha512_compress (i+1) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i] =
       sha512_compress_round (EL i sha512_K) (EL i W)
        [EL 0 sc_i; EL 1 sc_i; EL 2 sc_i; EL 3 sc_i; EL 4 sc_i; EL 5 sc_i;
         EL 6 sc_i; EL 7 sc_i]`
     SUBST1_TAC THENL
      [REWRITE_TAC[sha512_compress; SHA512_COMPRESS_ROUND_EL_LIST] THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MAP_EVERY ABBREV_TAC
      [`K_t = (EL i sha512_K):int64`; `W_t = (EL i W):int64`] THEN
     REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                 sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
     SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
     REWRITE_TAC[DIMINDEX_64; EL; HD; TL; ARITH] THEN
     CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[GSYM(CONJUNCT1 EL)] THEN
     SUBGOAL_THEN `word_shl (word i:int64) 3 = word (8 * i)` ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `val (word i:int64) = i` ASSUME_TAC THENL
      [ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `read (memory :> bytes64 (word_add kptr (word (8 * i)))) s0 = K_t /\
       read (memory :> bytes64 (word_add stackpointer (word (8 * i)))) s0 =
       W_t`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     ARM_STEPS_TAC NOHW_EXEC (1--36) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
       ASM_SIMP_TAC[MOD_LT;
                    ARITH_RULE `i < 80 ==> i < 2 EXP 64`;
                    ARITH_RULE `18446744073709551537 < 2 EXP 64`] THEN
       ASM_CASES_TAC `i + 1 = 80` THENL
        [ASM_REWRITE_TAC[LT_REFL] THEN
         SUBGOAL_THEN `i = 79` SUBST1_TAC THENL
          [UNDISCH_TAC `i + 1 = 80` THEN ARITH_TAC; ALL_TAC] THEN
         CONV_TAC NUM_REDUCE_CONV;
         SUBGOAL_THEN `i + 1 < 80` ASSUME_TAC THENL
          [UNDISCH_TAC `i < 80` THEN UNDISCH_TAC `~(i + 1 = 80)` THEN
           ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~((i + 18446744073709551537) MOD 2 EXP 64 = 0)` ASSUME_TAC
         THENL
          [SUBGOAL_THEN
             `(i + 18446744073709551537) MOD 2 EXP 64 =
              i + 18446744073709551537` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN
             UNDISCH_TAC `i + 1 < 80` THEN ARITH_TAC; ALL_TAC] THEN
           UNDISCH_TAC `i + 1 < 80` THEN ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[]];
       CONV_TAC WORD_RULE;
       REWRITE_TAC[BIC_NORM];
       REWRITE_TAC[BIC_NORM]];
     ENSURES_INIT_TAC "s0" THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[]];

   ALL_TAC] THEN

  (* ===== Phase E: split at pc+0x184 ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x184`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw_mc /\
         read SP s = stackpointer /\
         read X0 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X4 s = word_add
            (EL 0 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) a_i /\
         read X5 s = word_add
            (EL 1 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) b_i /\
         read X6 s = word_add
            (EL 2 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) c_i /\
         read X7 s = word_add
            (EL 3 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) d_i /\
         read X8 s = word_add
            (EL 4 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) e_i /\
         read X9 s = word_add
            (EL 5 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) f_i /\
         read X10 s = word_add
            (EL 6 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) g_i /\
         read X11 s = word_add
            (EL 7 (sha512_compress 80
                   (sha512_message_schedule 64 M_i)
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) h_i /\
         (!j t. j < num_blocks /\ t < 16 ==>
              read (memory :> bytes64
                    (word_add data_ptr (word(128 * j + 8*t)))) s =
              word_bytereverse (EL t (EL j blocks))) /\
         (!t. t < 80 ==>
              read (memory :> bytes64(word_add kptr (word(8*t)))) s =
              EL t sha512_K)` THEN
  CONJ_TAC THENL

  [(* Phase E: 8 ADDs for add-back *)
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC NOHW_EXEC (1--8) THEN
   ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   (CONV_TAC WORD_RULE ORELSE ASM_REWRITE_TAC[]);

   ALL_TAC] THEN

  (* ===== Phase F + postamble: 8 stores + add x1 + sub x2 ===== *)
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC NOHW_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* X1 = word_add data_ptr (word(128 * (ii + 1))) *)
    EXPAND_TAC "dptr_i" THEN CONV_TAC WORD_RULE;
    (* X2 = word(num_blocks - (ii + 1)) *)
    SUBGOAL_THEN `num_blocks - ii = (num_blocks - (ii + 1)) + 1` ASSUME_TAC THENL
     [UNDISCH_TAC `ii < num_blocks` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    (* memory read at state_ptr: EL t (sha512_hash_blocks (ii+1) blocks H0) *)
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `ii + 1 = SUC ii`;
                sha512_hash_blocks;
                ARITH_RULE `SUC ii = ii + 1`] THEN
    EXPAND_TAC "M_i" THEN EXPAND_TAC "H_i" THEN
    MP_TAC(SPECL [`M_i:int64 list`;
                  `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`] SHA512_BLOCK_EL) THEN
    ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:num`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `sha512_block M_i H_i = sha512_block M_i [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`
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
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[GSYM(CONJUNCT1 EL)]]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper.                                                       *)
(* ------------------------------------------------------------------------- *)

let SHA512_BLOCK_DATA_ORDER_NOHW_SUBROUTINE_CORRECT = prove
 (`!num_blocks (blocks:(int64 list) list)
    (a:int64) b c d (e:int64) f g h
    state_ptr data_ptr kptr pc stackpointer returnaddress.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    nonoverlapping (state_ptr,64)
                   (word_sub stackpointer (word 704), 704) /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,64);
              (word_sub stackpointer (word 704):int64, 704)]
             [(word pc, 0x1c8);
              (data_ptr:int64, 128 * num_blocks);
              (kptr:int64, 640)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha512_block_data_order_nohw_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           read X0 s = state_ptr /\
           read X1 s = data_ptr /\
           read X2 s = word num_blocks /\
           read X3 s = kptr /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t [a;b;c;d;e;f;g;h]) /\
           (!j t. j < num_blocks /\ t < 16 ==>
                read (memory :> bytes64
                      (word_add data_ptr (word(128 * j + 8*t)))) s =
                word_bytereverse (EL t (EL j blocks))) /\
           (!t. t < 80 ==>
                read (memory :> bytes64(word_add kptr (word(8*t)))) s =
                EL t sha512_K))
      (\s. read PC s = returnaddress /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t (sha512_hash_blocks num_blocks blocks
                        [a;b;c;d;e;f;g;h])))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(state_ptr,64);
                  memory :> bytes(word_sub stackpointer (word 704), 704)])`,
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) NOHW_EXEC
        SHA512_BLOCK_DATA_ORDER_NOHW_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26]` 704);;
