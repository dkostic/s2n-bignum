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
(* **WIP**. Phases A, C, stash, Phase E (add-back), and Phase F+postamble   *)
(* are fully proved.  The period loop (pc+0xc8..pc+0x9d0: 3 periods ×      *)
(* 16 ROUND_SCHED) and the D-tail (pc+0x9d0..pc+0x1090: 16 ROUND_NOSCHED)   *)
(* remain CHEAT_TAC pending a proof of the slot-rotation invariant across   *)
(* the sliding schedule window.  The .S is verified correct via the test   *)
(* harness (201 random tests + NIST "abc" vector).                          *)
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

  (* ===== Phase A: pc+0x20 .. pc+0xa0 -- 16 ldr/rev pairs (32 insts). ===== *)
  (* Postcondition: slot_reg(j) = word_zx (EL j M_i) for j=0..15.          *)
  ENSURES_SEQUENCE_TAC `pc + 0xa0`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X19 s = word_zx (EL  0 M_i:int32) /\
         read X20 s = word_zx (EL  1 M_i:int32) /\
         read X21 s = word_zx (EL  2 M_i:int32) /\
         read X22 s = word_zx (EL  3 M_i:int32) /\
         read X23 s = word_zx (EL  4 M_i:int32) /\
         read X24 s = word_zx (EL  5 M_i:int32) /\
         read X25 s = word_zx (EL  6 M_i:int32) /\
         read X26 s = word_zx (EL  7 M_i:int32) /\
         read X27 s = word_zx (EL  8 M_i:int32) /\
         read X28 s = word_zx (EL  9 M_i:int32) /\
         read X12 s = word_zx (EL 10 M_i:int32) /\
         read X13 s = word_zx (EL 11 M_i:int32) /\
         read X14 s = word_zx (EL 12 M_i:int32) /\
         read X15 s = word_zx (EL 13 M_i:int32) /\
         read X16 s = word_zx (EL 14 M_i:int32) /\
         read X17 s = word_zx (EL 15 M_i:int32) /\
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
   [(* Phase A: derive 16 concrete data reads, normalize addresses, step. *)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN
      MAP_EVERY (fun k -> DISCH_THEN(fun memth ->
        MP_TAC(SPECL [`ii:num`; mk_small_numeral k] memth) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(LAND_CONV NUM_REDUCE_CONV))))
        THEN DISCH_TAC THEN
        MP_TAC memth)) (0--15) THEN
      DISCH_TAC) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ARM_STEPS_TAC NOHW5_EXEC (1--32) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_32; DIMINDEX_64;
             LE_REFL; ARITH] THEN
    REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE];

    ALL_TAC] THEN

  (* ===== Phase C: pc+0xa0 .. pc+0xc0 -- 8 ldr from [x29]. ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xc0`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
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
         read X19 s = word_zx (EL  0 M_i:int32) /\
         read X20 s = word_zx (EL  1 M_i:int32) /\
         read X21 s = word_zx (EL  2 M_i:int32) /\
         read X22 s = word_zx (EL  3 M_i:int32) /\
         read X23 s = word_zx (EL  4 M_i:int32) /\
         read X24 s = word_zx (EL  5 M_i:int32) /\
         read X25 s = word_zx (EL  6 M_i:int32) /\
         read X26 s = word_zx (EL  7 M_i:int32) /\
         read X27 s = word_zx (EL  8 M_i:int32) /\
         read X28 s = word_zx (EL  9 M_i:int32) /\
         read X12 s = word_zx (EL 10 M_i:int32) /\
         read X13 s = word_zx (EL 11 M_i:int32) /\
         read X14 s = word_zx (EL 12 M_i:int32) /\
         read X15 s = word_zx (EL 13 M_i:int32) /\
         read X16 s = word_zx (EL 14 M_i:int32) /\
         read X17 s = word_zx (EL 15 M_i:int32) /\
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
   [(* Phase C: 8 ldr from [x29] into W4..W11. *)
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
    ARM_STEPS_TAC NOHW5_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EL; HD; TL] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[HD; TL; EL];

    ALL_TAC] THEN

  (* ===== Build W abbreviation for the schedule extension ===== *)
  SUBGOAL_THEN `LENGTH (M_i:int32 list) = 16` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\bl:int32 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `W = sha256_message_schedule 48 M_i` THEN
  SUBGOAL_THEN `LENGTH (W:int32 list) = 64` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[LENGTH_SHA256_MESSAGE_SCHEDULE] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. t < 16 ==> EL t M_i = EL t (W:int32 list)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "W" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SHA256_SCHEDULE_PREFIX THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN

  (* ===== Stash + x30 counter: pc+0xc0 .. pc+0xc8 (2 insts). ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xc8`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X30 s = word 3 /\
         read X3 s = kptr /\
         read X4 s = word_zx (a_i:int32) /\
         read X5 s = word_zx (b_i:int32) /\
         read X6 s = word_zx (c_i:int32) /\
         read X7 s = word_zx (d_i:int32) /\
         read X8 s = word_zx (e_i:int32) /\
         read X9 s = word_zx (f_i:int32) /\
         read X10 s = word_zx (g_i:int32) /\
         read X11 s = word_zx (h_i:int32) /\
         read X19 s = word_zx (EL  0 M_i:int32) /\
         read X20 s = word_zx (EL  1 M_i:int32) /\
         read X21 s = word_zx (EL  2 M_i:int32) /\
         read X22 s = word_zx (EL  3 M_i:int32) /\
         read X23 s = word_zx (EL  4 M_i:int32) /\
         read X24 s = word_zx (EL  5 M_i:int32) /\
         read X25 s = word_zx (EL  6 M_i:int32) /\
         read X26 s = word_zx (EL  7 M_i:int32) /\
         read X27 s = word_zx (EL  8 M_i:int32) /\
         read X28 s = word_zx (EL  9 M_i:int32) /\
         read X12 s = word_zx (EL 10 M_i:int32) /\
         read X13 s = word_zx (EL 11 M_i:int32) /\
         read X14 s = word_zx (EL 12 M_i:int32) /\
         read X15 s = word_zx (EL 13 M_i:int32) /\
         read X16 s = word_zx (EL 14 M_i:int32) /\
         read X17 s = word_zx (EL 15 M_i:int32) /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* Stash x1,x2 to stack + mov x30, #3 *)
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC NOHW5_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (* ===== Period loop: pc+0xc8 .. pc+0x9d0 (3 periods x 16 rounds).
     At exit: slot_reg(j) = word_zx (EL (48 + j) W) (j=0..15),
              X4..X11 holds sha256_compress 48 W H_i,
              X3 = word_add kptr (word 192),
              X30 = word 0.                                                *)
  ENSURES_SEQUENCE_TAC `pc + 0x9d0`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X30 s = word 0 /\
         read X3 s = word_add kptr (word 192) /\
         read X4 s = word_zx (EL 0 (sha256_compress 48 W
                    [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X5 s = word_zx (EL 1 (sha256_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X6 s = word_zx (EL 2 (sha256_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X7 s = word_zx (EL 3 (sha256_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X8 s = word_zx (EL 4 (sha256_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X9 s = word_zx (EL 5 (sha256_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X10 s = word_zx (EL 6 (sha256_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X11 s = word_zx (EL 7 (sha256_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X19 s = word_zx (EL 48 (W:int32 list)) /\
         read X20 s = word_zx (EL 49 (W:int32 list)) /\
         read X21 s = word_zx (EL 50 (W:int32 list)) /\
         read X22 s = word_zx (EL 51 (W:int32 list)) /\
         read X23 s = word_zx (EL 52 (W:int32 list)) /\
         read X24 s = word_zx (EL 53 (W:int32 list)) /\
         read X25 s = word_zx (EL 54 (W:int32 list)) /\
         read X26 s = word_zx (EL 55 (W:int32 list)) /\
         read X27 s = word_zx (EL 56 (W:int32 list)) /\
         read X28 s = word_zx (EL 57 (W:int32 list)) /\
         read X12 s = word_zx (EL 58 (W:int32 list)) /\
         read X13 s = word_zx (EL 59 (W:int32 list)) /\
         read X14 s = word_zx (EL 60 (W:int32 list)) /\
         read X15 s = word_zx (EL 61 (W:int32 list)) /\
         read X16 s = word_zx (EL 62 (W:int32 list)) /\
         read X17 s = word_zx (EL 63 (W:int32 list)) /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* Period loop proof: period 0 round 0 via ENSURES_SEQUENCE_TAC at pc+0x158.
       Remainder (rounds 1..15 of p=0, plus periods 1..2) still CHEAT.           *)
    ENSURES_SEQUENCE_TAC `pc + 0x158`
      `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
           read SP s = stackpointer /\
           read X29 s = state_ptr /\
           read X30 s = word 3 /\
           read X3 s = word_add kptr (word 4) /\
           read X4 s = word_zx (EL 0 (sha256_compress 1 W
                      [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X5 s = word_zx (EL 1 (sha256_compress 1 W
                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X6 s = word_zx (EL 2 (sha256_compress 1 W
                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X7 s = word_zx (EL 3 (sha256_compress 1 W
                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X8 s = word_zx (EL 4 (sha256_compress 1 W
                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X9 s = word_zx (EL 5 (sha256_compress 1 W
                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X10 s = word_zx (EL 6 (sha256_compress 1 W
                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X11 s = word_zx (EL 7 (sha256_compress 1 W
                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
           read X19 s = word_zx (EL 16 (W:int32 list)) /\
           read X20 s = word_zx (EL  1 M_i:int32) /\
           read X21 s = word_zx (EL  2 M_i:int32) /\
           read X22 s = word_zx (EL  3 M_i:int32) /\
           read X23 s = word_zx (EL  4 M_i:int32) /\
           read X24 s = word_zx (EL  5 M_i:int32) /\
           read X25 s = word_zx (EL  6 M_i:int32) /\
           read X26 s = word_zx (EL  7 M_i:int32) /\
           read X27 s = word_zx (EL  8 M_i:int32) /\
           read X28 s = word_zx (EL  9 M_i:int32) /\
           read X12 s = word_zx (EL 10 M_i:int32) /\
           read X13 s = word_zx (EL 11 M_i:int32) /\
           read X14 s = word_zx (EL 12 M_i:int32) /\
           read X15 s = word_zx (EL 13 M_i:int32) /\
           read X16 s = word_zx (EL 14 M_i:int32) /\
           read X17 s = word_zx (EL 15 M_i:int32) /\
           read (memory :> bytes64 (word_add stackpointer (word 96))) s =
             dptr_i /\
           read (memory :> bytes64 (word_add stackpointer (word 104))) s =
             word(num_blocks - ii) /\
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
     [(* Round 0 body proof: pc+0xc8..pc+0x158, 36 insts (ROUND_SCHED).
         Uses SHA256_W_EXTEND at n=0 to bridge schedule step to EL 16 W.    *)
      ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN
      REWRITE_TAC[sha256_compress] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
        `read (memory :> bytes32 (word_add kptr (word 0))) s0 = EL 0 sha256_K`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
        REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
        CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0];
        ALL_TAC] THEN
      ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                  sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN
      SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
               WORD_ZX_TRIVIAL] THEN
      REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
      REPEAT CONJ_TAC THENL
       [(* T1+T2 = EL 0 compress_round: needs EL 0 M_i = EL 0 W bridge *)
        SUBGOAL_THEN `EL 0 (M_i:int32 list) = EL 0 (W:int32 list)` SUBST1_TAC
        THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
        CONV_TAC WORD_RULE;
        (* d_i + T1 = EL 4 compress_round: same M_i -> W bridge *)
        SUBGOAL_THEN `EL 0 (M_i:int32 list) = EL 0 (W:int32 list)` SUBST1_TAC
        THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
        CONV_TAC WORD_RULE;
        (* Schedule step = EL 16 W: SHA256_W_EXTEND at n=0 *)
        MP_TAC(SPECL [`0`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[sha256_message_schedule; sha256_sigma0; sha256_sigma1] THEN
        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
        DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];

      (* Round 1 body: pc+0x158..pc+0x1e8, 36 insts (ROUND_SCHED).
         Slot map: WT=X20 WT1=X21 WT9=X12 WT14=X17. Uses SHA256_W_EXTEND at n=1
         with SCHEDULE_MONO to bridge schedule(2) to schedule(48).            *)
      ENSURES_SEQUENCE_TAC `pc + 0x1e8`
        `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X30 s = word 3 /\
             read X3 s = word_add kptr (word 8) /\
             read X4 s = word_zx (EL 0 (sha256_compress 2 W
                        [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = word_zx (EL 1 (sha256_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = word_zx (EL 2 (sha256_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = word_zx (EL 3 (sha256_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = word_zx (EL 4 (sha256_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = word_zx (EL 5 (sha256_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = word_zx (EL 6 (sha256_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = word_zx (EL 7 (sha256_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = word_zx (EL 16 (W:int32 list)) /\
             read X20 s = word_zx (EL 17 (W:int32 list)) /\
             read X21 s = word_zx (EL  2 M_i:int32) /\
             read X22 s = word_zx (EL  3 M_i:int32) /\
             read X23 s = word_zx (EL  4 M_i:int32) /\
             read X24 s = word_zx (EL  5 M_i:int32) /\
             read X25 s = word_zx (EL  6 M_i:int32) /\
             read X26 s = word_zx (EL  7 M_i:int32) /\
             read X27 s = word_zx (EL  8 M_i:int32) /\
             read X28 s = word_zx (EL  9 M_i:int32) /\
             read X12 s = word_zx (EL 10 M_i:int32) /\
             read X13 s = word_zx (EL 11 M_i:int32) /\
             read X14 s = word_zx (EL 12 M_i:int32) /\
             read X15 s = word_zx (EL 13 M_i:int32) /\
             read X16 s = word_zx (EL 14 M_i:int32) /\
             read X17 s = word_zx (EL 15 M_i:int32) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
       [(* Round 1 body proof *)
        ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN
        REWRITE_TAC[sha256_compress] THEN
        ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN
          `read (memory :> bytes32 (word_add kptr (word 4))) s0 = EL 1 sha256_K`
        ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
          REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
          CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
          DISCH_THEN MATCH_ACCEPT_TAC;
          ALL_TAC] THEN
        ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                    sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
        CONV_TAC(DEPTH_CONV EL_CONV) THEN
        SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                 WORD_ZX_TRIVIAL] THEN
        REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
        REPEAT CONJ_TAC THENL
         [(* T1+T2 = EL 0 compress_round: EL 1 M_i = EL 1 W *)
          SUBGOAL_THEN `EL 1 (M_i:int32 list) = EL 1 (W:int32 list)` SUBST1_TAC
          THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
          CONV_TAC WORD_RULE;
          (* d_i + T1 = EL 4 compress_round: same bridge *)
          SUBGOAL_THEN `EL 1 (M_i:int32 list) = EL 1 (W:int32 list)` SUBST1_TAC
          THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
          CONV_TAC WORD_RULE;
          (* Schedule step: SHA256_W_EXTEND at n=1 + SCHEDULE_MONO bridge *)
          MP_TAC(SPECL [`1`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          SUBGOAL_THEN
            `!j. j < 17 ==>
                 EL j (sha256_message_schedule 1 (M_i:int32 list)) =
                 EL j (sha256_message_schedule 48 M_i)`
          MP_TAC THENL
           [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
            MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
            ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(fun th ->
            MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
              [1; 2; 10; 15]) THEN
          REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          DISCH_THEN SUBST1_TAC THEN
          SUBGOAL_THEN
            `EL 1 (M_i:int32 list) = EL 1 (W:int32 list) /\
             EL 2 M_i = EL 2 W /\
             EL 10 M_i = EL 10 W /\
             EL 15 M_i = EL 15 W`
          (fun th -> REWRITE_TAC[th]) THENL
           [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
            ALL_TAC] THEN
          CONV_TAC WORD_RULE];

        (* Round 2 body: pc+0x1e8..pc+0x278, 36 insts (ROUND_SCHED).
           Slot map: WT=X21 WT1=X22 WT9=X13 WT14=X19 (W[16] from overwritten slot).
           Needs SHA256_W_EXTEND at n=2 + SCHEDULE_MONO at indices 2,3,11,16.  *)
        ENSURES_SEQUENCE_TAC `pc + 0x278`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 12) /\
               read X4 s = word_zx (EL 0 (sha256_compress 3 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL  3 M_i:int32) /\
               read X23 s = word_zx (EL  4 M_i:int32) /\
               read X24 s = word_zx (EL  5 M_i:int32) /\
               read X25 s = word_zx (EL  6 M_i:int32) /\
               read X26 s = word_zx (EL  7 M_i:int32) /\
               read X27 s = word_zx (EL  8 M_i:int32) /\
               read X28 s = word_zx (EL  9 M_i:int32) /\
               read X12 s = word_zx (EL 10 M_i:int32) /\
               read X13 s = word_zx (EL 11 M_i:int32) /\
               read X14 s = word_zx (EL 12 M_i:int32) /\
               read X15 s = word_zx (EL 13 M_i:int32) /\
               read X16 s = word_zx (EL 14 M_i:int32) /\
               read X17 s = word_zx (EL 15 M_i:int32) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 2 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 8))) s0 =
             EL 2 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 2 (M_i:int32 list) = EL 2 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 2 (M_i:int32 list) = EL 2 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`2`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 18 ==>
                   EL j (sha256_message_schedule 2 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [2; 3; 11; 16]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 2 (M_i:int32 list) = EL 2 (W:int32 list) /\
               EL 3 M_i = EL 3 W /\
               EL 11 M_i = EL 11 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

        (* Round 3 body: pc+0x278..pc+0x308, 36 insts (ROUND_SCHED).
           Slot map: WT=X22 WT1=X23 WT9=X14 WT14=X20 (W[17] from overwritten slot 1).
           Needs SHA256_W_EXTEND at n=3 + SCHEDULE_MONO at indices 3,4,12,17.  *)
        ENSURES_SEQUENCE_TAC `pc + 0x308`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 16) /\
               read X4 s = word_zx (EL 0 (sha256_compress 4 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 4 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 4 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 4 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 4 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 4 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 4 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 4 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL  4 M_i:int32) /\
               read X24 s = word_zx (EL  5 M_i:int32) /\
               read X25 s = word_zx (EL  6 M_i:int32) /\
               read X26 s = word_zx (EL  7 M_i:int32) /\
               read X27 s = word_zx (EL  8 M_i:int32) /\
               read X28 s = word_zx (EL  9 M_i:int32) /\
               read X12 s = word_zx (EL 10 M_i:int32) /\
               read X13 s = word_zx (EL 11 M_i:int32) /\
               read X14 s = word_zx (EL 12 M_i:int32) /\
               read X15 s = word_zx (EL 13 M_i:int32) /\
               read X16 s = word_zx (EL 14 M_i:int32) /\
               read X17 s = word_zx (EL 15 M_i:int32) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 3 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 12))) s0 =
             EL 3 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `3`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 3 (M_i:int32 list) = EL 3 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 3 (M_i:int32 list) = EL 3 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`3`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 19 ==>
                   EL j (sha256_message_schedule 3 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [3; 4; 12; 17]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 3 (M_i:int32 list) = EL 3 (W:int32 list) /\
               EL 4 M_i = EL 4 W /\
               EL 12 M_i = EL 12 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

        (* Round 4 body: pc+0x308..pc+0x398, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=4 + SCHEDULE_MONO at indices [4, 5, 13, 18].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x398`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 20) /\
               read X4 s = word_zx (EL 0 (sha256_compress 5 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 5 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 5 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 5 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 5 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 5 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 5 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 5 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL  5 M_i:int32) /\
               read X25 s = word_zx (EL  6 M_i) /\
               read X26 s = word_zx (EL  7 M_i) /\
               read X27 s = word_zx (EL  8 M_i) /\
               read X28 s = word_zx (EL  9 M_i) /\
               read X12 s = word_zx (EL 10 M_i) /\
               read X13 s = word_zx (EL 11 M_i) /\
               read X14 s = word_zx (EL 12 M_i) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 4 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `5 = 4 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 16))) s0 =
             EL 4 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `4`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 4 (M_i:int32 list) = EL 4 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 4 (M_i:int32 list) = EL 4 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`4`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 20 ==>
                   EL j (sha256_message_schedule 4 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [4; 5; 13; 18]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 4 (M_i:int32 list) = EL 4 (W:int32 list) /\
               EL 5 M_i = EL 5 W /\
               EL 13 M_i = EL 13 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 5..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 5 body: pc+0x398..pc+0x428, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=5 + SCHEDULE_MONO at indices [5, 6, 14, 19].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x428`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 24) /\
               read X4 s = word_zx (EL 0 (sha256_compress 6 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 6 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 6 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 6 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 6 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 6 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 6 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 6 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL  6 M_i:int32) /\
               read X26 s = word_zx (EL  7 M_i) /\
               read X27 s = word_zx (EL  8 M_i) /\
               read X28 s = word_zx (EL  9 M_i) /\
               read X12 s = word_zx (EL 10 M_i) /\
               read X13 s = word_zx (EL 11 M_i) /\
               read X14 s = word_zx (EL 12 M_i) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 5 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `6 = 5 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 20))) s0 =
             EL 5 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `5`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 5 (M_i:int32 list) = EL 5 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 5 (M_i:int32 list) = EL 5 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`5`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 21 ==>
                   EL j (sha256_message_schedule 5 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [5; 6; 14; 19]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 5 (M_i:int32 list) = EL 5 (W:int32 list) /\
               EL 6 M_i = EL 6 W /\
               EL 14 M_i = EL 14 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 6..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 6 body: pc+0x428..pc+0x4b8, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=6 + SCHEDULE_MONO at indices [6, 7, 15, 20].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x4b8`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 28) /\
               read X4 s = word_zx (EL 0 (sha256_compress 7 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 7 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 7 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 7 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 7 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 7 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 7 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 7 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL  7 M_i:int32) /\
               read X27 s = word_zx (EL  8 M_i) /\
               read X28 s = word_zx (EL  9 M_i) /\
               read X12 s = word_zx (EL 10 M_i) /\
               read X13 s = word_zx (EL 11 M_i) /\
               read X14 s = word_zx (EL 12 M_i) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 6 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `7 = 6 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 24))) s0 =
             EL 6 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `6`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 6 (M_i:int32 list) = EL 6 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 6 (M_i:int32 list) = EL 6 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`6`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 22 ==>
                   EL j (sha256_message_schedule 6 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [6; 7; 15; 20]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 6 (M_i:int32 list) = EL 6 (W:int32 list) /\
               EL 7 M_i = EL 7 W /\
               EL 15 M_i = EL 15 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 7..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 7 body: pc+0x4b8..pc+0x548, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=7 + SCHEDULE_MONO at indices [7, 8, 16, 21].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x548`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 32) /\
               read X4 s = word_zx (EL 0 (sha256_compress 8 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 8 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 8 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 8 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 8 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 8 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 8 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 8 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL  8 M_i:int32) /\
               read X28 s = word_zx (EL  9 M_i) /\
               read X12 s = word_zx (EL 10 M_i) /\
               read X13 s = word_zx (EL 11 M_i) /\
               read X14 s = word_zx (EL 12 M_i) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 7 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `8 = 7 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 28))) s0 =
             EL 7 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `7`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 7 (M_i:int32 list) = EL 7 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 7 (M_i:int32 list) = EL 7 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`7`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 23 ==>
                   EL j (sha256_message_schedule 7 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [7; 8; 16; 21]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 7 (M_i:int32 list) = EL 7 (W:int32 list) /\
               EL 8 M_i = EL 8 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 8..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 8 body: pc+0x548..pc+0x5d8, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=8 + SCHEDULE_MONO at indices [8, 9, 17, 22].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x5d8`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 36) /\
               read X4 s = word_zx (EL 0 (sha256_compress 9 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 9 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 9 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 9 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 9 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 9 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 9 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 9 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL  9 M_i:int32) /\
               read X12 s = word_zx (EL 10 M_i) /\
               read X13 s = word_zx (EL 11 M_i) /\
               read X14 s = word_zx (EL 12 M_i) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 8 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `9 = 8 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 32))) s0 =
             EL 8 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `8`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 8 (M_i:int32 list) = EL 8 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 8 (M_i:int32 list) = EL 8 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`8`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 24 ==>
                   EL j (sha256_message_schedule 8 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [8; 9; 17; 22]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 8 (M_i:int32 list) = EL 8 (W:int32 list) /\
               EL 9 M_i = EL 9 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 9..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 9 body: pc+0x5d8..pc+0x668, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=9 + SCHEDULE_MONO at indices [9, 10, 18, 23].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x668`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 40) /\
               read X4 s = word_zx (EL 0 (sha256_compress 10 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 10 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 10 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 10 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 10 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 10 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 10 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 10 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL 25 (W:int32 list)) /\
               read X12 s = word_zx (EL 10 M_i:int32) /\
               read X13 s = word_zx (EL 11 M_i) /\
               read X14 s = word_zx (EL 12 M_i) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 9 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `10 = 9 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 36))) s0 =
             EL 9 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `9`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 9 (M_i:int32 list) = EL 9 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 9 (M_i:int32 list) = EL 9 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`9`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 25 ==>
                   EL j (sha256_message_schedule 9 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [9; 10; 18; 23]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 9 (M_i:int32 list) = EL 9 (W:int32 list) /\
               EL 10 M_i = EL 10 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 10..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 10 body: pc+0x668..pc+0x6f8, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=10 + SCHEDULE_MONO at indices [10, 11, 19, 24].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x6f8`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 44) /\
               read X4 s = word_zx (EL 0 (sha256_compress 11 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 11 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 11 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 11 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 11 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 11 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 11 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 11 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL 25 (W:int32 list)) /\
               read X12 s = word_zx (EL 26 (W:int32 list)) /\
               read X13 s = word_zx (EL 11 M_i:int32) /\
               read X14 s = word_zx (EL 12 M_i) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 10 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `11 = 10 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 40))) s0 =
             EL 10 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `10`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 10 (M_i:int32 list) = EL 10 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 10 (M_i:int32 list) = EL 10 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`10`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 26 ==>
                   EL j (sha256_message_schedule 10 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [10; 11; 19; 24]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 10 (M_i:int32 list) = EL 10 (W:int32 list) /\
               EL 11 M_i = EL 11 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 11..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 11 body: pc+0x6f8..pc+0x788, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=11 + SCHEDULE_MONO at indices [11, 12, 20, 25].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x788`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 48) /\
               read X4 s = word_zx (EL 0 (sha256_compress 12 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 12 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 12 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 12 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 12 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 12 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 12 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 12 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL 25 (W:int32 list)) /\
               read X12 s = word_zx (EL 26 (W:int32 list)) /\
               read X13 s = word_zx (EL 27 (W:int32 list)) /\
               read X14 s = word_zx (EL 12 M_i:int32) /\
               read X15 s = word_zx (EL 13 M_i) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 11 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `12 = 11 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 44))) s0 =
             EL 11 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `11`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 11 (M_i:int32 list) = EL 11 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 11 (M_i:int32 list) = EL 11 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`11`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 27 ==>
                   EL j (sha256_message_schedule 11 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [11; 12; 20; 25]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 11 (M_i:int32 list) = EL 11 (W:int32 list) /\
               EL 12 M_i = EL 12 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 12..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 12 body: pc+0x788..pc+0x818, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=12 + SCHEDULE_MONO at indices [12, 13, 21, 26].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x818`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 52) /\
               read X4 s = word_zx (EL 0 (sha256_compress 13 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 13 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 13 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 13 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 13 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 13 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 13 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 13 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL 25 (W:int32 list)) /\
               read X12 s = word_zx (EL 26 (W:int32 list)) /\
               read X13 s = word_zx (EL 27 (W:int32 list)) /\
               read X14 s = word_zx (EL 28 (W:int32 list)) /\
               read X15 s = word_zx (EL 13 M_i:int32) /\
               read X16 s = word_zx (EL 14 M_i) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 12 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `13 = 12 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 48))) s0 =
             EL 12 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `12`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 12 (M_i:int32 list) = EL 12 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 12 (M_i:int32 list) = EL 12 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`12`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 28 ==>
                   EL j (sha256_message_schedule 12 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [12; 13; 21; 26]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 12 (M_i:int32 list) = EL 12 (W:int32 list) /\
               EL 13 M_i = EL 13 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 13..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 13 body: pc+0x818..pc+0x8a8, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=13 + SCHEDULE_MONO at indices [13, 14, 22, 27].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x8a8`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 56) /\
               read X4 s = word_zx (EL 0 (sha256_compress 14 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 14 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 14 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 14 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 14 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 14 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 14 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 14 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL 25 (W:int32 list)) /\
               read X12 s = word_zx (EL 26 (W:int32 list)) /\
               read X13 s = word_zx (EL 27 (W:int32 list)) /\
               read X14 s = word_zx (EL 28 (W:int32 list)) /\
               read X15 s = word_zx (EL 29 (W:int32 list)) /\
               read X16 s = word_zx (EL 14 M_i:int32) /\
               read X17 s = word_zx (EL 15 M_i) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 13 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `14 = 13 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 52))) s0 =
             EL 13 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `13`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 13 (M_i:int32 list) = EL 13 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 13 (M_i:int32 list) = EL 13 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`13`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 29 ==>
                   EL j (sha256_message_schedule 13 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [13; 14; 22; 27]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 13 (M_i:int32 list) = EL 13 (W:int32 list) /\
               EL 14 M_i = EL 14 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 14..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 14 body: pc+0x8a8..pc+0x938, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=14 + SCHEDULE_MONO at indices [14, 15, 23, 28].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x938`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 60) /\
               read X4 s = word_zx (EL 0 (sha256_compress 15 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 15 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 15 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 15 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 15 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 15 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 15 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 15 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL 25 (W:int32 list)) /\
               read X12 s = word_zx (EL 26 (W:int32 list)) /\
               read X13 s = word_zx (EL 27 (W:int32 list)) /\
               read X14 s = word_zx (EL 28 (W:int32 list)) /\
               read X15 s = word_zx (EL 29 (W:int32 list)) /\
               read X16 s = word_zx (EL 30 (W:int32 list)) /\
               read X17 s = word_zx (EL 15 M_i:int32) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 14 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `15 = 14 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 56))) s0 =
             EL 14 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `14`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 14 (M_i:int32 list) = EL 14 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 14 (M_i:int32 list) = EL 14 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`14`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 30 ==>
                   EL j (sha256_message_schedule 14 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [14; 15; 23; 28]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 14 (M_i:int32 list) = EL 14 (W:int32 list) /\
               EL 15 M_i = EL 15 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Rounds 15..15 of p=0 + periods 1,2 still CHEAT *)
        (* Round 15 body: pc+0x938..pc+0x9c8, 36 insts (ROUND_SCHED).
           SHA256_W_EXTEND at n=15 + SCHEDULE_MONO at indices [15, 16, 24, 29].  *)
        ENSURES_SEQUENCE_TAC `pc + 0x9c8`
          `\s. aligned_bytes_loaded s (word pc)
                 sha256_block_data_order_nohw5_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 3 /\
               read X3 s = word_add kptr (word 64) /\
               read X4 s = word_zx (EL 0 (sha256_compress 16 W
                          [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = word_zx (EL 1 (sha256_compress 16 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = word_zx (EL 2 (sha256_compress 16 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = word_zx (EL 3 (sha256_compress 16 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = word_zx (EL 4 (sha256_compress 16 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X9 s = word_zx (EL 5 (sha256_compress 16 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = word_zx (EL 6 (sha256_compress 16 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = word_zx (EL 7 (sha256_compress 16 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = word_zx (EL 16 (W:int32 list)) /\
               read X20 s = word_zx (EL 17 (W:int32 list)) /\
               read X21 s = word_zx (EL 18 (W:int32 list)) /\
               read X22 s = word_zx (EL 19 (W:int32 list)) /\
               read X23 s = word_zx (EL 20 (W:int32 list)) /\
               read X24 s = word_zx (EL 21 (W:int32 list)) /\
               read X25 s = word_zx (EL 22 (W:int32 list)) /\
               read X26 s = word_zx (EL 23 (W:int32 list)) /\
               read X27 s = word_zx (EL 24 (W:int32 list)) /\
               read X28 s = word_zx (EL 25 (W:int32 list)) /\
               read X12 s = word_zx (EL 26 (W:int32 list)) /\
               read X13 s = word_zx (EL 27 (W:int32 list)) /\
               read X14 s = word_zx (EL 28 (W:int32 list)) /\
               read X15 s = word_zx (EL 29 (W:int32 list)) /\
               read X16 s = word_zx (EL 30 (W:int32 list)) /\
               read X17 s = word_zx (EL 31 (W:int32 list)) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 15 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `16 = 15 + 1`] THEN
          REWRITE_TAC[sha256_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes32 (word_add kptr (word 60))) s0 =
             EL 15 sha256_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `15`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW5_EXEC (1--36) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
                      sha256_Ch; sha256_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 15 (M_i:int32 list) = EL 15 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 15 (M_i:int32 list) = EL 15 (W:int32 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`15`; `M_i:int32 list`] SHA256_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 31 ==>
                   EL j (sha256_message_schedule 15 (M_i:int32 list)) =
                   EL j (sha256_message_schedule 48 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA256_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [15; 16; 24; 29]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha256_sigma0; sha256_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 15 (M_i:int32 list) = EL 15 (W:int32 list)`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* Back-edge + periods 1,2 still CHEAT *)
          CHEAT_TAC]]]]]]]]]]]]]]]];

    ALL_TAC] THEN

  (* ===== D-tail: pc+0x9d0 .. pc+0x1090, 16 compression-only rounds. ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x1090`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X3 s = word_add kptr (word 256) /\
         read X4 s = word_zx (EL 0 (sha256_compress 64 W
                    [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X5 s = word_zx (EL 1 (sha256_compress 64 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X6 s = word_zx (EL 2 (sha256_compress 64 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X7 s = word_zx (EL 3 (sha256_compress 64 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X8 s = word_zx (EL 4 (sha256_compress 64 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X9 s = word_zx (EL 5 (sha256_compress 64 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X10 s = word_zx (EL 6 (sha256_compress 64 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X11 s = word_zx (EL 7 (sha256_compress 64 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* D-tail proof *) CHEAT_TAC; ALL_TAC] THEN

  (* ===== Phase E: add-back (pc+0x1090 .. pc+0x10d0, 16 insts). ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0x10d0`
    `\s. aligned_bytes_loaded s (word pc) sha256_block_data_order_nohw5_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X3 s = word_add kptr (word 256) /\
         read X4 s = word_zx (word_add
            (EL 0 (sha256_compress 64 W
                   [a_i:int32;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) a_i) /\
         read X5 s = word_zx (word_add
            (EL 1 (sha256_compress 64 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) b_i) /\
         read X6 s = word_zx (word_add
            (EL 2 (sha256_compress 64 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) c_i) /\
         read X7 s = word_zx (word_add
            (EL 3 (sha256_compress 64 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) d_i) /\
         read X8 s = word_zx (word_add
            (EL 4 (sha256_compress 64 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) e_i) /\
         read X9 s = word_zx (word_add
            (EL 5 (sha256_compress 64 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) f_i) /\
         read X10 s = word_zx (word_add
            (EL 6 (sha256_compress 64 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) g_i) /\
         read X11 s = word_zx (word_add
            (EL 7 (sha256_compress 64 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) h_i) /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* Phase E: 8 (ldr + add) pairs.  At pc+0x1090 each wK is
       word_zx(EL (K-4) sha256_compress 64 W [a_i;..;h_i]); loading the
       initial state element EL (K-4) [a_i;..;h_i] from [x29, #4*(K-4)]
       and adding gives the add-back value.                               *)
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
    ARM_STEPS_TAC NOHW5_EXEC (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
             WORD_ZX_TRIVIAL] THEN
    REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
    REWRITE_TAC[EL; HD; TL] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[];

    ALL_TAC] THEN

  (* ===== Phase F + postamble: pc+0x10d0 .. pc+0x1100 (12 insts body +
     cbnz at pc+0x1100 handled by outer ENSURES_WHILE_UP_TAC back-edge).
     12 insts: 8 str (Phase F) + ldp + add + sub + sub.                   *)
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC NOHW5_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [(* X1 = word_add data_ptr (word (64 * (ii+1))) *)
    REWRITE_TAC[ARITH_RULE `64 * (ii+1) = 64 * ii + 64`] THEN
    UNDISCH_TAC `word_add data_ptr (word (64 * ii):int64) = dptr_i` THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* X2 = word (num_blocks - (ii+1)) *)
    SUBGOAL_THEN `num_blocks - ii = (num_blocks - (ii + 1)) + 1` ASSUME_TAC THENL
     [UNDISCH_TAC `ii < num_blocks` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* state memory: EL t (sha256_hash_blocks (ii+1) blocks H0) for t<8 *)
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
  REWRITE_TAC[GSYM(CONJUNCT1 EL)]);;

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
