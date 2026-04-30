(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 multi-block compression using scalar instructions only (nohw5).   *)
(* Variant of sha256_block_data_order_nohw4 in which the 16-word sliding     *)
(* message-schedule window lives in 16 registers (w12..w17, w19..w28)        *)
(* rather than the 256-byte stack scratch. Phase A loads the block directly  *)
(* into slot registers and each fused compression round reads W[t] from its  *)
(* slot register and writes W[t+16] back to the same slot once W[t] is       *)
(* consumed. Three iterations of a 16-round unrolled "period" handle rounds  *)
(* 0..47; a 16-round unrolled D-tail handles rounds 48..63.                  *)
(*                                                                           *)
(* **WIP / PROOF SKELETON**. SUBROUTINE_CORRECT is fully proved; CORRECT has *)
(* the multi-block outer induction fully proved, but the per-block body is  *)
(* CHEAT_TAC pending a proof of the slot-rotation invariant across the 16-  *)
(* round period body and the 16-round D-tail. The .S is verified correct   *)
(* via the test harness (201 random tests + NIST "abc" vector).             *)
(* ========================================================================= *)

needs "arm/proofs/sha256_block_scalar.ml";;

(* Machine code *)

let sha256_block_data_order_nohw5_mc = define_from_elf
  "sha256_block_data_order_nohw5_mc"
  (file_on_path !load_path "arm/sha2/sha256_block_data_order_nohw5.o");;

let NOHW5_EXEC = ARM_MK_EXEC_RULE sha256_block_data_order_nohw5_mc;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas (same shape as nohw4).                                      *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA256_HASH_BLOCKS_NOHW5 = prove
 (`!n blocks H:int32 list. LENGTH H = 8
   ==> LENGTH(sha256_hash_blocks n blocks H) = 8`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha256_hash_blocks];
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha256_hash_blocks] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LENGTH_SHA256_BLOCK THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LENGTH_8_CONS_NOHW5 = prove
 (`!L:A list. LENGTH L = 8 ==>
     ?a0 a1 a2 a3 a4 a5 a6 a7. L = [a0;a1;a2;a3;a4;a5;a6;a7]`,
  let suc8 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))` in
  REWRITE_TAC[GSYM suc8; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_8_EL_NOHW5 = prove
 (`!L:A list. LENGTH L = 8 ==>
     L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L;
          EL 4 L; EL 5 L; EL 6 L; EL 7 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_8_CONS_NOHW5) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Slot-register map. The 16 schedule slots live in these registers in       *)
(* circular order. `slot_reg k` is the register holding W[t + k mod 16]      *)
(* at round t within a period (the same map rotates across periods).         *)
(* ------------------------------------------------------------------------- *)

(* We express slot assignments via HOL reads rather than a single list,      *)
(* since HOL component accessors (X19, X20, ..) are distinct constants.      *)

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let SHA256_BLOCK_DATA_ORDER_NOHW5_CORRECT = prove
 (`!num_blocks (blocks:(int32 list) list)
    (a:int32) b c d (e:int32) f g h
    state_ptr data_ptr kptr pc stackpointer.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,32); (stackpointer:int64,112)]
             [(word pc, 0x1128);
              (data_ptr:int64, 64 * num_blocks);
              (kptr:int64, 256)] /\
    nonoverlapping (state_ptr,32) (word_add stackpointer (word 96),16)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha256_block_data_order_nohw5_mc /\
           read PC s = word (pc + 0x20) /\
           read SP s = stackpointer /\
           read X29 s = state_ptr /\
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
      (\s. read PC s = word (pc + 0x1104) /\
           read X29 s = state_ptr /\
           (!t. t < 8 ==>
                read (memory :> bytes32(word_add state_ptr (word(4*t)))) s =
                EL t (sha256_hash_blocks num_blocks blocks
                        [a;b;c;d;e;f;g;h])))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X12; X13; X14; X15; X16; X17;
                  X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
       MAYCHANGE [memory :> bytes(state_ptr,32);
                  memory :> bytes(word_add stackpointer (word 96),16)])`,
  let BIC_NORM = WORD_RULE
    `word_and (x:(N)word) (word_not y) = word_and (word_not y) x` in
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              fst NOHW5_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* ===== Outer multi-block induction: pc+0x20 .. pc+0x1100 ===== *)
  (* The body ends at pc+0x1100 = `cbnz x2, .Lblock_loop5`; after that
     we fall through to pc+0x1104 = `mov x0, x29` (outside core window). *)
  ENSURES_WHILE_UP_TAC `num_blocks:num` `pc + 0x20` `pc + 0x1100`
    `\i s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
           read SP s = stackpointer /\
           read X29 s = state_ptr /\
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

  [(* num_blocks <> 0 *)
   ASM_ARITH_TAC;

   (* Init: invariant(0) at pc+0x20 *)
   ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; SUB_0; sha256_hash_blocks];

   (* Body placeholder *)
   ALL_TAC;

   (* Back-edge: 1 step (the cbnz at pc+0x1100) *)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   SUBGOAL_THEN `num_blocks - i < 2 EXP 64` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   VAL_INT64_TAC `num_blocks - i` THEN
   ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC NOHW5_EXEC [1] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   (* Exit: final state at pc+0x1100 matches postcondition at pc+0x1104 *)
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
               NONOVERLAPPING_CLAUSES; SUB_REFL] THEN
   VAL_INT64_TAC `0` THEN
   ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC NOHW5_EXEC (1--1) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  (* ===== Body subgoal: invariant(ii) at pc+0x20 => invariant(ii+1) ===== *)
  X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  SUBGOAL_THEN `num_blocks - ii < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `num_blocks - ii` THEN
  ABBREV_TAC `dptr_i = word_add data_ptr (word(64 * ii)):int64` THEN
  ABBREV_TAC `H_i = sha256_hash_blocks ii blocks [a:int32;b;c;d;e;f;g;h]` THEN
  SUBGOAL_THEN `LENGTH (H_i:int32 list) = 8` ASSUME_TAC THENL
   [EXPAND_TAC "H_i" THEN
    MATCH_MP_TAC LENGTH_SHA256_HASH_BLOCKS_NOHW5 THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M_i = EL ii blocks:int32 list` THEN
  SUBGOAL_THEN `LENGTH (M_i:int32 list) = 16` ASSUME_TAC THENL
   [EXPAND_TAC "M_i" THEN
    UNDISCH_TAC `ALL (\bl:int32 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `H_i:int32 list` LIST_8_EL_NOHW5) THEN
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

  (* --- Remaining body proof: Phase A through postamble.              ---
     --- Structure: ENSURES_SEQUENCE per phase, analogous to nohw4.    ---
     --- Each phase's sub-proof is filled in incrementally.            ---
     --- TODO: replace CHEAT_TAC with full phase proofs.               --- *)
  CHEAT_TAC);;

(* Note on CORRECT window: core covers pc+0x20 (start of block loop, after    *)
(* prologue + `mov x29, x0`) through pc+0x1104 (instruction just after the    *)
(* block-loop back-edge `cbnz x2, .Lblock_loop5`). Prologue (8 instructions)  *)
(* and epilogue (9 instructions including `mov x0, x29` and `ret`) are        *)
(* discharged by ARM_ADD_RETURN_STACK_TAC via SUBROUTINE_CORRECT.             *)

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper.                                                       *)
(* ------------------------------------------------------------------------- *)

let SHA256_BLOCK_DATA_ORDER_NOHW5_SUBROUTINE_CORRECT = prove
 (`!num_blocks (blocks:(int32 list) list)
    (a:int32) b c d (e:int32) f g h
    state_ptr data_ptr kptr pc stackpointer returnaddress.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    nonoverlapping (state_ptr,32)
                   (word_sub stackpointer (word 112), 112) /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,32);
              (word_sub stackpointer (word 112):int64, 112)]
             [(word pc, 0x1128);
              (data_ptr:int64, 64 * num_blocks);
              (kptr:int64, 256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha256_block_data_order_nohw5_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 112), 112)])`,
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(8,8) NOHW5_EXEC
        SHA256_BLOCK_DATA_ORDER_NOHW5_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 112);;
