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
      (if i+1 < 64 then pc+4 else pc+0x94) *)
   CHEAT_TAC;

   (* Subgoal 4: EXIT -- invariant(64) at pc+0x94 ==> postcondition *)
   ENSURES_INIT_TAC "s0" THEN
   ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[]]);;
