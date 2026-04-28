(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 64-round compression loop using scalar instructions.              *)
(* Validates the scalar loop structure against sha256_compress 64 W H.       *)
(* ========================================================================= *)

needs "arm/proofs/sha256_block_core.ml";;
needs "arm/proofs/sha256_1round_scalar.ml";;

(* Machine code *)

let sha256_core_scalar_mc = define_from_elf "sha256_core_scalar_mc"
  (file_on_path !load_path "arm/sha2/sha256_core_scalar.o");;

let SCALAR_CORE_EXEC = ARM_MK_EXEC_RULE sha256_core_scalar_mc;;

(* Correctness theorem *)

let SHA256_CORE_SCALAR_CORRECT = prove
 (`!W (a:int32) b c d (e:int32) f g h wptr kptr pc.
    LENGTH W = 64 /\
    nonoverlapping (word pc, 152) (wptr, 256) /\
    nonoverlapping (word pc, 152) (kptr, 256)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) sha256_core_scalar_mc /\
           read PC s = word pc /\
           read X0 s = wptr /\
           read X3 s = kptr /\
           read X4 s = word_zx (a:int32) /\
           read X5 s = word_zx (b:int32) /\
           read X6 s = word_zx (c:int32) /\
           read X7 s = word_zx (d:int32) /\
           read X8 s = word_zx (e:int32) /\
           read X9 s = word_zx (f:int32) /\
           read X10 s = word_zx (g:int32) /\
           read X11 s = word_zx (h:int32) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add wptr (word(4*t)))) s =
                EL t W) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K))
      (\s. read PC s = word(pc + 0x94) /\
           read X4 s = word_zx (EL 0 (sha256_compress 64 W [a;b;c;d;e;f;g;h])) /\
           read X5 s = word_zx (EL 1 (sha256_compress 64 W [a;b;c;d;e;f;g;h])) /\
           read X6 s = word_zx (EL 2 (sha256_compress 64 W [a;b;c;d;e;f;g;h])) /\
           read X7 s = word_zx (EL 3 (sha256_compress 64 W [a;b;c;d;e;f;g;h])) /\
           read X8 s = word_zx (EL 4 (sha256_compress 64 W [a;b;c;d;e;f;g;h])) /\
           read X9 s = word_zx (EL 5 (sha256_compress 64 W [a;b;c;d;e;f;g;h])) /\
           read X10 s = word_zx (EL 6 (sha256_compress 64 W [a;b;c;d;e;f;g;h])) /\
           read X11 s = word_zx (EL 7 (sha256_compress 64 W [a;b;c;d;e;f;g;h])))
      (MAYCHANGE [PC; X4; X5; X6; X7; X8; X9; X10; X11;
                  X12; X13; X14; X15; X16; X17] ,,
       MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])`,
  let BIC_NORM = WORD_RULE
    `word_and (x:(N)word) (word_not y) = word_and (word_not y) x` in
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst SCALAR_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC `64` `pc + 0x4` `pc + 0x94`
    `\i s. aligned_bytes_loaded s (word pc) sha256_core_scalar_mc /\
           read X0 s = wptr /\
           read X3 s = kptr /\
           read X17 s = word i /\
           read X4 s = word_zx (EL 0 (sha256_compress i W
                                      [a:int32;b;c;d;e;f;g;h])) /\
           read X5 s = word_zx (EL 1 (sha256_compress i W
                                      [a;b;c;d;e;f;g;h])) /\
           read X6 s = word_zx (EL 2 (sha256_compress i W
                                      [a;b;c;d;e;f;g;h])) /\
           read X7 s = word_zx (EL 3 (sha256_compress i W
                                      [a;b;c;d;e;f;g;h])) /\
           read X8 s = word_zx (EL 4 (sha256_compress i W
                                      [a;b;c;d;e;f;g;h])) /\
           read X9 s = word_zx (EL 5 (sha256_compress i W
                                      [a;b;c;d;e;f;g;h])) /\
           read X10 s = word_zx (EL 6 (sha256_compress i W
                                       [a;b;c;d;e;f;g;h])) /\
           read X11 s = word_zx (EL 7 (sha256_compress i W
                                       [a;b;c;d;e;f;g;h])) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add wptr (word(4*t)))) s =
                EL t W) /\
           (!t. t < 64 ==>
                read (memory :> bytes32(word_add kptr (word(4*t)))) s =
                EL t sha256_K)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL

  [(* Subgoal 1: 64 <> 0 *)
   ARITH_TAC;

   (* Subgoal 2: INIT -- precondition ==> invariant(0) at pc+4 *)
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC SCALAR_CORE_EXEC (1--1) THEN
   ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[sha256_compress] THEN
   CONV_TAC(DEPTH_CONV EL_CONV) THEN
   REWRITE_TAC[];

   (* Subgoal 3: BODY -- invariant(i) at pc+4 ==> invariant(i+1) at
      (if i+1 < 64 then pc+4 else pc+0x94). *)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   ABBREV_TAC `sc_i = sha256_compress i W [a:int32;b;c;d;e;f;g;h]` THEN
   SUBGOAL_THEN
    `sha256_compress (i+1) W [a:int32;b;c;d;e;f;g;h] =
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
     read (memory :> bytes32 (word_add wptr (word (4 * i)))) s0 = W_t`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ARM_STEPS_TAC SCALAR_CORE_EXEC (1--36) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
            WORD_ZX_TRIVIAL] THEN
   REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
   REPEAT CONJ_TAC THENL
    [(* PC conditional *)
     REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD;
                 VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
     ASM_SIMP_TAC[MOD_LT;
                  ARITH_RULE `i < 64
                    ==> i < 2 EXP 64 /\ i < 2 EXP 32 /\
                        1 < 2 EXP 32 /\ 64 < 2 EXP 32 /\
                        i + 1 < 2 EXP 32`] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     SUBGOAL_THEN `(i + 1) MOD 4294967296 = i + 1` SUBST1_TAC THENL
      [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_CASES_TAC `i + 1 = 64` THEN ASM_REWRITE_TAC[] THEN
     TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;

     (* X17 counter *)
     ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
     REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                 DIMINDEX_32; DIMINDEX_64] THEN
     SIMP_TAC[MOD_LT; ARITH_RULE `1 < 2 EXP 32`] THEN
     ASM_SIMP_TAC[MOD_LT;
                  ARITH_RULE `i < 64
                    ==> i < 2 EXP 32 /\ i + 1 < 2 EXP 32 /\
                        i + 1 < 2 EXP 64`];

     (* X4 scalar compression match *)
     REWRITE_TAC[BIC_NORM];

     (* X8 scalar compression match *)
     REWRITE_TAC[BIC_NORM]];

   (* Subgoal 4: EXIT -- invariant(64) at pc+0x94 ==> postcondition *)
   ENSURES_INIT_TAC "s0" THEN
   ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[]]);;
