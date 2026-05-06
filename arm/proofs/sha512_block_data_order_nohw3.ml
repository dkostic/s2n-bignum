(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-512 multi-block compression using scalar instructions only (nohw3).   *)
(* Direct 64-bit port of sha512_block_data_order_nohw3: a..h state positions *)
(* rotate through a fixed cycle of eight x-registers (x4..x11). At           *)
(* round t with t mod 8 = k, position j lives in register                    *)
(* x[4 + ((j - k) mod 8)]. Each round writes only new_e (into the slot that *)
(* held d) and new_a (into the slot that held h), eliminating the six       *)
(* state-rotation MOVs per round that nohw5 executes. State returns to       *)
(* canonical x4..x11 = a..h at every 8-round boundary, and in particular    *)
(* at every period boundary (rounds 0, 16, 32, 48, 64) and at round 80, so the  *)
(* per-period and D-tail entry invariants are identical to nohw5's.         *)
(*                                                                           *)
(* The schedule window layout, period structure (4 fused iterations then   *)
(* a 16-round D-tail), K-pointer handling, and stack frame are unchanged   *)
(* from nohw2.                                                               *)
(*                                                                           *)
(* Proof status: fully cheat-free. axioms() = 3 (HOL axioms only).          *)
(* ========================================================================= *)

needs "arm/proofs/utils/sha512_bridge.ml";;

(* Machine code *)

let sha512_block_data_order_nohw3_mc = define_from_elf
  "sha512_block_data_order_nohw3_mc"
  (file_on_path !load_path "arm/sha2/sha512_block_data_order_nohw3.o");;

let NOHW3_EXEC = ARM_MK_EXEC_RULE sha512_block_data_order_nohw3_mc;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas (same shape as nohw5).                                      *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA512_HASH_BLOCKS_NOHW3 = prove
 (`!n blocks H:int64 list. LENGTH H = 8
   ==> LENGTH(sha512_hash_blocks n blocks H) = 8`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha512_hash_blocks];
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha512_hash_blocks] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LENGTH_SHA512_BLOCK THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LENGTH_8_CONS_NOHW3_64 = prove
 (`!L:A list. LENGTH L = 8 ==>
     ?a0 a1 a2 a3 a4 a5 a6 a7. L = [a0;a1;a2;a3;a4;a5;a6;a7]`,
  let suc8 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))` in
  REWRITE_TAC[GSYM suc8; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_8_EL_NOHW3_64 = prove
 (`!L:A list. LENGTH L = 8 ==>
     L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L;
          EL 4 L; EL 5 L; EL 6 L; EL 7 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_8_CONS_NOHW3_64) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let LIST_8_COMPRESS_NOHW3_64 = prove
 (`!n W H:int64 list. LENGTH H = 8
   ==> ?a b c d e f g h. sha512_compress n W H = [a;b;c;d;e;f;g;h]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sha512_compress n W (H:int64 list)`] LIST_8_EL_NOHW3_64) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LENGTH_SHA512_COMPRESS THEN ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let SHA512_BLOCK_DATA_ORDER_NOHW3_CORRECT = prove
 (`!num_blocks (blocks:(int64 list) list)
    (a:int64) b c d (e:int64) f g h
    state_ptr data_ptr kptr pc stackpointer.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,64); (stackpointer:int64,112)]
             [(word pc, 0xe28);
              (data_ptr:int64, 64 * num_blocks);
              (kptr:int64, 640)] /\
    nonoverlapping (state_ptr,32) (word_add stackpointer (word 96),16)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha512_block_data_order_nohw3_mc /\
           read PC s = word (pc + 0x20) /\
           read SP s = stackpointer /\
           read X29 s = state_ptr /\
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
      (\s. read PC s = word (pc + 0xe04) /\
           read X29 s = state_ptr /\
           (!t. t < 8 ==>
                read (memory :> bytes64(word_add state_ptr (word(8*t)))) s =
                EL t (sha512_hash_blocks num_blocks blocks
                        [a;b;c;d;e;f;g;h])))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X12; X13; X14; X15; X16; X17;
                  X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
       MAYCHANGE [memory :> bytes(state_ptr,64);
                  memory :> bytes(word_add stackpointer (word 96),16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              fst NOHW3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* ===== Outer multi-block induction: pc+0x20 .. pc+0xe00 ===== *)
  ENSURES_WHILE_UP_TAC `num_blocks:num` `pc + 0x20` `pc + 0xe00`
    `\i s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
           read SP s = stackpointer /\
           read X29 s = state_ptr /\
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

  [(* num_blocks <> 0 *)
   ASM_ARITH_TAC;

   (* Init: invariant(0) at pc+0x20 *)
   ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; SUB_0; sha512_hash_blocks];

   (* Body placeholder *)
   ALL_TAC;

   (* Back-edge: 1 step (the cbnz at pc+0xe00) *)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   SUBGOAL_THEN `num_blocks - i < 2 EXP 64` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   VAL_INT64_TAC `num_blocks - i` THEN
   ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC NOHW3_EXEC [1] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   (* Exit: final state at pc+0xe00 matches postcondition at pc+0xe04 *)
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
               NONOVERLAPPING_CLAUSES; SUB_REFL] THEN
   VAL_INT64_TAC `0` THEN
   ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC NOHW3_EXEC (1--1) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  (* ===== Body subgoal: invariant(ii) at pc+0x20 => invariant(ii+1) ===== *)
  X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  SUBGOAL_THEN `num_blocks - ii < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `num_blocks - ii` THEN
  ABBREV_TAC `dptr_i = word_add data_ptr (word(128 * ii)):int64` THEN
  ABBREV_TAC `H_i = sha512_hash_blocks ii blocks [a:int64;b;c;d;e;f;g;h]` THEN
  SUBGOAL_THEN `LENGTH (H_i:int64 list) = 8` ASSUME_TAC THENL
   [EXPAND_TAC "H_i" THEN
    MATCH_MP_TAC LENGTH_SHA512_HASH_BLOCKS_NOHW3 THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M_i = EL ii blocks:int64 list` THEN
  SUBGOAL_THEN `LENGTH (M_i:int64 list) = 16` ASSUME_TAC THENL
   [EXPAND_TAC "M_i" THEN
    UNDISCH_TAC `ALL (\bl:int64 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `H_i:int64 list` LIST_8_EL_NOHW3_64) THEN
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
    `!t. word_add data_ptr (word(128 * ii + 8*t):int64) =
         word_add dptr_i (word(8*t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "dptr_i" THEN
    REWRITE_TAC[WORD_RULE
      `word_add (word_add d (word x:int64)) (word y) =
       word_add d (word (x + y))`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (* ===== Phase A: pc+0x20 .. pc+0xa0 -- 16 ldr/rev pairs (32 insts). ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xa0`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X19 s = EL  0 M_i:int64 /\
         read X20 s = EL  1 M_i:int64 /\
         read X21 s = EL  2 M_i:int64 /\
         read X22 s = EL  3 M_i:int64 /\
         read X23 s = EL  4 M_i:int64 /\
         read X24 s = EL  5 M_i:int64 /\
         read X25 s = EL  6 M_i:int64 /\
         read X26 s = EL  7 M_i:int64 /\
         read X27 s = EL  8 M_i:int64 /\
         read X28 s = EL  9 M_i:int64 /\
         read X12 s = (EL 10 M_i:int64) /\
         read X13 s = (EL 11 M_i:int64) /\
         read X14 s = (EL 12 M_i:int64) /\
         read X15 s = (EL 13 M_i:int64) /\
         read X16 s = (EL 14 M_i:int64) /\
         read X17 s = (EL 15 M_i:int64) /\
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
    ARM_STEPS_TAC NOHW3_EXEC (1--32) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_64; DIMINDEX_64;
             LE_REFL; ARITH] THEN
    REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE];

    ALL_TAC] THEN

  (* ===== Phase C: pc+0xa0 .. pc+0xc0 -- 8 ldr from [x29]. ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xc0`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X1 s = dptr_i /\
         read X2 s = word(num_blocks - ii) /\
         read X3 s = kptr /\
         read X4 s = a_i /\
         read X5 s = b_i /\
         read X6 s = c_i /\
         read X7 s = d_i /\
         read X8 s = e_i /\
         read X9 s = f_i /\
         read X10 s = g_i /\
         read X11 s = h_i /\
         read X19 s = EL  0 M_i:int64 /\
         read X20 s = EL  1 M_i:int64 /\
         read X21 s = EL  2 M_i:int64 /\
         read X22 s = EL  3 M_i:int64 /\
         read X23 s = EL  4 M_i:int64 /\
         read X24 s = EL  5 M_i:int64 /\
         read X25 s = EL  6 M_i:int64 /\
         read X26 s = EL  7 M_i:int64 /\
         read X27 s = EL  8 M_i:int64 /\
         read X28 s = EL  9 M_i:int64 /\
         read X12 s = (EL 10 M_i:int64) /\
         read X13 s = (EL 11 M_i:int64) /\
         read X14 s = (EL 12 M_i:int64) /\
         read X15 s = (EL 13 M_i:int64) /\
         read X16 s = (EL 14 M_i:int64) /\
         read X17 s = (EL 15 M_i:int64) /\
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
   [(* Phase C: 8 ldr from [x29] into W4..W11. *)
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun k ->
     let th = SPECL [k] (ASSUME
      `forall t.
           t < 8
           ==> read (memory :> bytes64 (word_add state_ptr (word(8*t)))) s0 =
               EL t [a_i:int64; b_i; c_i; d_i; e_i; f_i; g_i; h_i]`) in
     MP_TAC th THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH; EL; HD; TL] THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     REWRITE_TAC[WORD_ADD_0] THEN
     DISCH_TAC)
    [`0`; `1`; `2`; `3`; `4`; `5`; `6`; `7`] THEN
    ARM_STEPS_TAC NOHW3_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EL; HD; TL] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[HD; TL; EL];

    ALL_TAC] THEN

  (* ===== Build W abbreviation for the schedule extension ===== *)
  SUBGOAL_THEN `LENGTH (M_i:int64 list) = 16` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\bl:int64 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `W = sha512_message_schedule 64 M_i` THEN
  SUBGOAL_THEN `LENGTH (W:int64 list) = 64` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[LENGTH_SHA512_MESSAGE_SCHEDULE] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. t < 16 ==> EL t M_i = EL t (W:int64 list)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "W" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SHA512_SCHEDULE_PREFIX THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN

  (* ===== Stash + x30 counter: pc+0xc0 .. pc+0xc8 (2 insts). ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xc8`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X30 s = word 4 /\
         read X3 s = kptr /\
         read X4 s = a_i /\
         read X5 s = b_i /\
         read X6 s = c_i /\
         read X7 s = d_i /\
         read X8 s = e_i /\
         read X9 s = f_i /\
         read X10 s = g_i /\
         read X11 s = h_i /\
         read X19 s = EL  0 M_i:int64 /\
         read X20 s = EL  1 M_i:int64 /\
         read X21 s = EL  2 M_i:int64 /\
         read X22 s = EL  3 M_i:int64 /\
         read X23 s = EL  4 M_i:int64 /\
         read X24 s = EL  5 M_i:int64 /\
         read X25 s = EL  6 M_i:int64 /\
         read X26 s = EL  7 M_i:int64 /\
         read X27 s = EL  8 M_i:int64 /\
         read X28 s = EL  9 M_i:int64 /\
         read X12 s = (EL 10 M_i:int64) /\
         read X13 s = (EL 11 M_i:int64) /\
         read X14 s = (EL 12 M_i:int64) /\
         read X15 s = (EL 13 M_i:int64) /\
         read X16 s = (EL 14 M_i:int64) /\
         read X17 s = (EL 15 M_i:int64) /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* Stash x1,x2 to stack + mov x30, #3 *)
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC NOHW3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (* ===== Period loop: pc+0xc8 .. pc+0x850 (3 periods x 16 rounds).          *)
  ENSURES_SEQUENCE_TAC `pc + 0x850`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X30 s = word 0 /\
         read X3 s = word_add kptr (word 384) /\
         read X4 s = (EL 0 (sha512_compress 48 W
                    [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X5 s = (EL 1 (sha512_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X6 s = (EL 2 (sha512_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X7 s = (EL 3 (sha512_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X8 s = (EL 4 (sha512_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X9 s = (EL 5 (sha512_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X10 s = (EL 6 (sha512_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X11 s = (EL 7 (sha512_compress 48 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X19 s = (EL 48 (W:int64 list)) /\
         read X20 s = (EL 49 (W:int64 list)) /\
         read X21 s = (EL 50 (W:int64 list)) /\
         read X22 s = (EL 51 (W:int64 list)) /\
         read X23 s = (EL 52 (W:int64 list)) /\
         read X24 s = (EL 53 (W:int64 list)) /\
         read X25 s = (EL 54 (W:int64 list)) /\
         read X26 s = (EL 55 (W:int64 list)) /\
         read X27 s = (EL 56 (W:int64 list)) /\
         read X28 s = (EL 57 (W:int64 list)) /\
         read X12 s = (EL 58 (W:int64 list)) /\
         read X13 s = (EL 59 (W:int64 list)) /\
         read X14 s = (EL 60 (W:int64 list)) /\
         read X15 s = (EL 61 (W:int64 list)) /\
         read X16 s = (EL 62 (W:int64 list)) /\
         read X17 s = (EL 63 (W:int64 list)) /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* Period loop body proof:
        - Period 0 round 0 proved inline.
        - Remaining rounds (p=0 r=1..15, p=1,2) still CHEAT.                   *)
    ENSURES_SEQUENCE_TAC `pc + 0x140`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X30 s = word 4 /\
             read X3 s = word_add kptr (word 8) /\
             read X11 s = (EL 0 (sha512_compress 1 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X4 s = (EL 1 (sha512_compress 1 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 2 (sha512_compress 1 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 3 (sha512_compress 1 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 4 (sha512_compress 1 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 5 (sha512_compress 1 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 6 (sha512_compress 1 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 7 (sha512_compress 1 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 16 (W:int64 list)) /\
             read X20 s = EL  1 M_i:int64 /\
             read X21 s = EL  2 M_i:int64 /\
             read X22 s = EL  3 M_i:int64 /\
             read X23 s = EL  4 M_i:int64 /\
             read X24 s = EL  5 M_i:int64 /\
             read X25 s = EL  6 M_i:int64 /\
             read X26 s = EL  7 M_i:int64 /\
             read X27 s = EL  8 M_i:int64 /\
             read X28 s = EL  9 M_i:int64 /\
             read X12 s = (EL 10 M_i:int64) /\
             read X13 s = (EL 11 M_i:int64) /\
             read X14 s = (EL 12 M_i:int64) /\
             read X15 s = (EL 13 M_i:int64) /\
             read X16 s = (EL 14 M_i:int64) /\
             read X17 s = (EL 15 M_i:int64) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- Period 0 round 0: pc+0xc8..pc+0x140, 30 insts (ROUND_SCHED_K0). ----- *)
      ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN
      REWRITE_TAC[sha512_compress] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
        `read (memory :> bytes64 (word_add kptr (word 0))) s0 = EL 0 sha512_K`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
        REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
        CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0];
        ALL_TAC] THEN
      ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                  sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN
      SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
               WORD_ZX_TRIVIAL] THEN
      REWRITE_TAC[EQ_REFL] THEN
      REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `EL 0 (M_i:int64 list) = EL 0 (W:int64 list)` SUBST1_TAC
        THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
        CONV_TAC WORD_RULE;
        SUBGOAL_THEN `EL 0 (M_i:int64 list) = EL 0 (W:int64 list)` SUBST1_TAC
        THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
        CONV_TAC WORD_RULE;
        MP_TAC(SPECL [`0`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[sha512_message_schedule; sha512_sigma0; sha512_sigma1] THEN
        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
        DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];

      (* ----- Period 0 round 1: pc+0x140..pc+0x1b8, 30 insts (ROUND_SCHED_K1).
         Cyclic rotation k=1 entry: X11=a, X4=b, X5=c, X6=d, X7=e, X8=f,
         X9=g, X10=h. Slot map: WT=X20 WT1=X21 WT9=X12 WT14=X17 (slots 1,2,10,15).
         Exit rotation 2: X10=a, X11=b, X4=c, X5=d, X6=e, X7=f, X8=g, X9=h.
         X20 overwritten with EL 17 W. Uses SHA512_W_EXTEND at n=1 with
         SCHEDULE_MONO at slot indices {1, 2, 10, 15}.                          *)
      ENSURES_SEQUENCE_TAC `pc + 0x1b8`
        `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X30 s = word 4 /\
             read X3 s = word_add kptr (word 16) /\
             read X10 s = (EL 0 (sha512_compress 2 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 1 (sha512_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X4 s = (EL 2 (sha512_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 3 (sha512_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 4 (sha512_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 5 (sha512_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 6 (sha512_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 7 (sha512_compress 2 W
                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 16 (W:int64 list)) /\
             read X20 s = (EL 17 (W:int64 list)) /\
             read X21 s = EL  2 M_i:int64 /\
             read X22 s = EL  3 M_i:int64 /\
             read X23 s = EL  4 M_i:int64 /\
             read X24 s = EL  5 M_i:int64 /\
             read X25 s = EL  6 M_i:int64 /\
             read X26 s = EL  7 M_i:int64 /\
             read X27 s = EL  8 M_i:int64 /\
             read X28 s = EL  9 M_i:int64 /\
             read X12 s = (EL 10 M_i:int64) /\
             read X13 s = (EL 11 M_i:int64) /\
             read X14 s = (EL 12 M_i:int64) /\
             read X15 s = (EL 13 M_i:int64) /\
             read X16 s = (EL 14 M_i:int64) /\
             read X17 s = (EL 15 M_i:int64) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
       [(* Round 1 body proof *)
        ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN
        REWRITE_TAC[sha512_compress] THEN
        ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN
          `read (memory :> bytes64 (word_add kptr (word 8))) s0 = EL 1 sha512_K`
        ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
          REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
          CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
          DISCH_THEN MATCH_ACCEPT_TAC;
          ALL_TAC] THEN
        ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                    sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
        CONV_TAC(DEPTH_CONV EL_CONV) THEN
        SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                 WORD_ZX_TRIVIAL] THEN
        REWRITE_TAC[EQ_REFL] THEN
        REPEAT CONJ_TAC THENL
         [(* T1+T2 = EL 0 compress_round: needs EL 1 M_i = EL 1 W bridge *)
          SUBGOAL_THEN `EL 1 (M_i:int64 list) = EL 1 (W:int64 list)` SUBST1_TAC
          THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
          CONV_TAC WORD_RULE;
          (* d_i + T1 = EL 4 compress_round: same bridge *)
          SUBGOAL_THEN `EL 1 (M_i:int64 list) = EL 1 (W:int64 list)` SUBST1_TAC
          THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
          CONV_TAC WORD_RULE;
          (* Schedule step: SHA512_W_EXTEND at n=1 + SCHEDULE_MONO bridge *)
          MP_TAC(SPECL [`1`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          SUBGOAL_THEN
            `!j. j < 17 ==>
                 EL j (sha512_message_schedule 1 (M_i:int64 list)) =
                 EL j (sha512_message_schedule 64 M_i)`
          MP_TAC THENL
           [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
            MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
            ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(fun th ->
            MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
              [1; 2; 10; 15]) THEN
          REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          DISCH_THEN SUBST1_TAC THEN
          SUBGOAL_THEN
            `EL 1 (M_i:int64 list) = EL 1 (W:int64 list) /\
             EL 2 M_i = EL 2 W /\
             EL 10 M_i = EL 10 W /\
             EL 15 M_i = EL 15 W`
          (fun th -> REWRITE_TAC[th]) THENL
           [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
            ALL_TAC] THEN
          CONV_TAC WORD_RULE];

        (* ----- Period 0 round 2: pc+0x1b8..pc+0x230, 30 insts (ROUND_SCHED_K2).
           Cyclic rotation k=2 entry (X10=a,X11=b,X4=c,X5=d,X6=e,X7=f,X8=g,X9=h).
           Slot map: WT=X21 WT1=X22 WT9=X13 WT14=X19 (slots 2,3,11,16 of ring).
           Note: slot at ring index 16 wraps to ring[0] = X19 (W[16]).
           SHA512_W_EXTEND at n=2 + SCHEDULE_MONO at slot indices {2,3,11,16}.  *)
        ENSURES_SEQUENCE_TAC `pc + 0x230`
          `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
               read SP s = stackpointer /\
               read X29 s = state_ptr /\
               read X30 s = word 4 /\
               read X3 s = word_add kptr (word 24) /\
               read X9 s = (EL 0 (sha512_compress 3 W
                          [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X10 s = (EL 1 (sha512_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X11 s = (EL 2 (sha512_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X4 s = (EL 3 (sha512_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X5 s = (EL 4 (sha512_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X6 s = (EL 5 (sha512_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X7 s = (EL 6 (sha512_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X8 s = (EL 7 (sha512_compress 3 W
                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
               read X19 s = (EL 16 (W:int64 list)) /\
               read X20 s = (EL 17 (W:int64 list)) /\
               read X21 s = (EL 18 (W:int64 list)) /\
               read X22 s = EL  3 M_i:int64 /\
               read X23 s = EL  4 M_i:int64 /\
               read X24 s = EL  5 M_i:int64 /\
               read X25 s = EL  6 M_i:int64 /\
               read X26 s = EL  7 M_i:int64 /\
               read X27 s = EL  8 M_i:int64 /\
               read X28 s = EL  9 M_i:int64 /\
               read X12 s = (EL 10 M_i:int64) /\
               read X13 s = (EL 11 M_i:int64) /\
               read X14 s = (EL 12 M_i:int64) /\
               read X15 s = (EL 13 M_i:int64) /\
               read X16 s = (EL 14 M_i:int64) /\
               read X17 s = (EL 15 M_i:int64) /\
               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                 dptr_i /\
               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                 word(num_blocks - ii) /\
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
         [(* Round 2 body proof *)
          ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
            `read (memory :> bytes64 (word_add kptr (word 16))) s0 =
             EL 2 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN MATCH_ACCEPT_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [SUBGOAL_THEN `EL 2 (M_i:int64 list) = EL 2 (W:int64 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            SUBGOAL_THEN `EL 2 (M_i:int64 list) = EL 2 (W:int64 list)`
            SUBST1_TAC
            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
            CONV_TAC WORD_RULE;
            MP_TAC(SPECL [`2`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            SUBGOAL_THEN
              `!j. j < 18 ==>
                   EL j (sha512_message_schedule 2 (M_i:int64 list)) =
                   EL j (sha512_message_schedule 64 M_i)`
            MP_TAC THENL
             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
              MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
              ASM_ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th ->
              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                [2; 3; 11; 16]) THEN
            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
            DISCH_THEN SUBST1_TAC THEN
            SUBGOAL_THEN
              `EL 2 (M_i:int64 list) = EL 2 (W:int64 list) /\
               EL 3 M_i = EL 3 W /\
               EL 11 M_i = EL 11 W`
            (fun th -> REWRITE_TAC[th]) THENL
             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC] THEN
            CONV_TAC WORD_RULE];

          (* ----- Period 0 round 3: pc+0x230..pc+0x2a8, 30 insts (ROUND_SCHED_K3).
             SHA512_W_EXTEND at n=3 + SCHEDULE_MONO at slot indices {3,4,12,17}.  *)
          ENSURES_SEQUENCE_TAC `pc + 0x2a8`
            `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                 read SP s = stackpointer /\
                 read X29 s = state_ptr /\
                 read X30 s = word 4 /\
                 read X3 s = word_add kptr (word 32) /\
                 read X8 s = (EL 0 (sha512_compress 4 W
                            [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X9 s = (EL 1 (sha512_compress 4 W
                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X10 s = (EL 2 (sha512_compress 4 W
                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X11 s = (EL 3 (sha512_compress 4 W
                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X4 s = (EL 4 (sha512_compress 4 W
                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X5 s = (EL 5 (sha512_compress 4 W
                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X6 s = (EL 6 (sha512_compress 4 W
                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X7 s = (EL 7 (sha512_compress 4 W
                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                 read X19 s = (EL 16 (W:int64 list)) /\
                 read X20 s = (EL 17 (W:int64 list)) /\
                 read X21 s = (EL 18 (W:int64 list)) /\
                 read X22 s = (EL 19 (W:int64 list)) /\
                 read X23 s = EL  4 M_i:int64 /\
                 read X24 s = EL  5 M_i:int64 /\
                 read X25 s = EL  6 M_i:int64 /\
                 read X26 s = EL  7 M_i:int64 /\
                 read X27 s = EL  8 M_i:int64 /\
                 read X28 s = EL  9 M_i:int64 /\
                 read X12 s = (EL 10 M_i:int64) /\
                 read X13 s = (EL 11 M_i:int64) /\
                 read X14 s = (EL 12 M_i:int64) /\
                 read X15 s = (EL 13 M_i:int64) /\
                 read X16 s = (EL 14 M_i:int64) /\
                 read X17 s = (EL 15 M_i:int64) /\
                 read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                   dptr_i /\
                 read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                   word(num_blocks - ii) /\
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
           [(* Round 3 body proof *)
            ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN
            REWRITE_TAC[sha512_compress] THEN
            ENSURES_INIT_TAC "s0" THEN
            SUBGOAL_THEN
              `read (memory :> bytes64 (word_add kptr (word 24))) s0 =
               EL 3 sha512_K`
            ASSUME_TAC THENL
             [FIRST_X_ASSUM(MP_TAC o SPEC `3`) THEN
              REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
              CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
              DISCH_THEN MATCH_ACCEPT_TAC;
              ALL_TAC] THEN
            ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
            ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                        sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
            CONV_TAC(DEPTH_CONV EL_CONV) THEN
            SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                     WORD_ZX_TRIVIAL] THEN
            REWRITE_TAC[EQ_REFL] THEN
            REPEAT CONJ_TAC THENL
             [SUBGOAL_THEN `EL 3 (M_i:int64 list) = EL 3 (W:int64 list)`
              SUBST1_TAC
              THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
              CONV_TAC WORD_RULE;
              SUBGOAL_THEN `EL 3 (M_i:int64 list) = EL 3 (W:int64 list)`
              SUBST1_TAC
              THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
              CONV_TAC WORD_RULE;
              MP_TAC(SPECL [`3`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
              EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
              CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
              SUBGOAL_THEN
                `!j. j < 19 ==>
                     EL j (sha512_message_schedule 3 (M_i:int64 list)) =
                     EL j (sha512_message_schedule 64 M_i)`
              MP_TAC THENL
               [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN(fun th ->
                MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                  [3; 4; 12; 17]) THEN
              REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
              ASM_REWRITE_TAC[] THEN
              REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
              DISCH_THEN SUBST1_TAC THEN
              SUBGOAL_THEN
                `EL 3 (M_i:int64 list) = EL 3 (W:int64 list) /\
                 EL 4 M_i = EL 4 W /\
                 EL 12 M_i = EL 12 W`
              (fun th -> REWRITE_TAC[th]) THENL
               [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                ALL_TAC] THEN
              CONV_TAC WORD_RULE];

            (* ----- Period 0 round 4: pc+0x2a8..pc+0x320, 30 insts (ROUND_SCHED_K4).
               SHA512_W_EXTEND at n=4 + SCHEDULE_MONO at slot indices {4,5,13,18}.  *)
            ENSURES_SEQUENCE_TAC `pc + 0x320`
              `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                   read SP s = stackpointer /\
                   read X29 s = state_ptr /\
                   read X30 s = word 4 /\
                   read X3 s = word_add kptr (word 40) /\
                   read X7 s = (EL 0 (sha512_compress 5 W
                              [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X8 s = (EL 1 (sha512_compress 5 W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X9 s = (EL 2 (sha512_compress 5 W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X10 s = (EL 3 (sha512_compress 5 W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X11 s = (EL 4 (sha512_compress 5 W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X4 s = (EL 5 (sha512_compress 5 W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X5 s = (EL 6 (sha512_compress 5 W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X6 s = (EL 7 (sha512_compress 5 W
                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                   read X19 s = (EL 16 (W:int64 list)) /\
                   read X20 s = (EL 17 (W:int64 list)) /\
                   read X21 s = (EL 18 (W:int64 list)) /\
                   read X22 s = (EL 19 (W:int64 list)) /\
                   read X23 s = (EL 20 (W:int64 list)) /\
                   read X24 s = EL  5 M_i:int64 /\
                   read X25 s = EL  6 M_i:int64 /\
                   read X26 s = EL  7 M_i:int64 /\
                   read X27 s = EL  8 M_i:int64 /\
                   read X28 s = EL  9 M_i:int64 /\
                   read X12 s = (EL 10 M_i:int64) /\
                   read X13 s = (EL 11 M_i:int64) /\
                   read X14 s = (EL 12 M_i:int64) /\
                   read X15 s = (EL 13 M_i:int64) /\
                   read X16 s = (EL 14 M_i:int64) /\
                   read X17 s = (EL 15 M_i:int64) /\
                   read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                     dptr_i /\
                   read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                     word(num_blocks - ii) /\
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
             [(* Round 4 body proof *)
              ONCE_REWRITE_TAC[ARITH_RULE `5 = 4 + 1`] THEN
              REWRITE_TAC[sha512_compress] THEN
              ENSURES_INIT_TAC "s0" THEN
              SUBGOAL_THEN
                `read (memory :> bytes64 (word_add kptr (word 32))) s0 =
                 EL 4 sha512_K`
              ASSUME_TAC THENL
               [FIRST_X_ASSUM(MP_TAC o SPEC `4`) THEN
                REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                DISCH_THEN MATCH_ACCEPT_TAC;
                ALL_TAC] THEN
              ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
              ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
              REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                          sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
              CONV_TAC(DEPTH_CONV EL_CONV) THEN
              SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                       WORD_ZX_TRIVIAL] THEN
              REWRITE_TAC[EQ_REFL] THEN
              REPEAT CONJ_TAC THENL
               [SUBGOAL_THEN `EL 4 (M_i:int64 list) = EL 4 (W:int64 list)`
                SUBST1_TAC
                THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                CONV_TAC WORD_RULE;
                SUBGOAL_THEN `EL 4 (M_i:int64 list) = EL 4 (W:int64 list)`
                SUBST1_TAC
                THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                CONV_TAC WORD_RULE;
                MP_TAC(SPECL [`4`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                SUBGOAL_THEN
                  `!j. j < 20 ==>
                       EL j (sha512_message_schedule 4 (M_i:int64 list)) =
                       EL j (sha512_message_schedule 64 M_i)`
                MP_TAC THENL
                 [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                  MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                  ASM_ARITH_TAC; ALL_TAC] THEN
                DISCH_THEN(fun th ->
                  MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                    [4; 5; 13; 18]) THEN
                REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                DISCH_THEN SUBST1_TAC THEN
                SUBGOAL_THEN
                  `EL 4 (M_i:int64 list) = EL 4 (W:int64 list) /\
                   EL 5 M_i = EL 5 W /\
                   EL 13 M_i = EL 13 W`
                (fun th -> REWRITE_TAC[th]) THENL
                 [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                  ALL_TAC] THEN
                CONV_TAC WORD_RULE];

              (* ----- Period 0 round 5: pc+0x320..pc+0x398, 30 insts (ROUND_SCHED_K5).
                 SHA512_W_EXTEND at n=5 + SCHEDULE_MONO at slot indices {5,6,14,19}.  *)
              ENSURES_SEQUENCE_TAC `pc + 0x398`
                `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                     read SP s = stackpointer /\
                     read X29 s = state_ptr /\
                     read X30 s = word 4 /\
                     read X3 s = word_add kptr (word 48) /\
                     read X6 s = (EL 0 (sha512_compress 6 W
                                [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X7 s = (EL 1 (sha512_compress 6 W
                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X8 s = (EL 2 (sha512_compress 6 W
                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X9 s = (EL 3 (sha512_compress 6 W
                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X10 s = (EL 4 (sha512_compress 6 W
                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X11 s = (EL 5 (sha512_compress 6 W
                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X4 s = (EL 6 (sha512_compress 6 W
                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X5 s = (EL 7 (sha512_compress 6 W
                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                     read X19 s = (EL 16 (W:int64 list)) /\
                     read X20 s = (EL 17 (W:int64 list)) /\
                     read X21 s = (EL 18 (W:int64 list)) /\
                     read X22 s = (EL 19 (W:int64 list)) /\
                     read X23 s = (EL 20 (W:int64 list)) /\
                     read X24 s = (EL 21 (W:int64 list)) /\
                     read X25 s = EL  6 M_i:int64 /\
                     read X26 s = EL  7 M_i:int64 /\
                     read X27 s = EL  8 M_i:int64 /\
                     read X28 s = EL  9 M_i:int64 /\
                     read X12 s = (EL 10 M_i:int64) /\
                     read X13 s = (EL 11 M_i:int64) /\
                     read X14 s = (EL 12 M_i:int64) /\
                     read X15 s = (EL 13 M_i:int64) /\
                     read X16 s = (EL 14 M_i:int64) /\
                     read X17 s = (EL 15 M_i:int64) /\
                     read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                       dptr_i /\
                     read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                       word(num_blocks - ii) /\
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
               [(* Round 5 body proof *)
                ONCE_REWRITE_TAC[ARITH_RULE `6 = 5 + 1`] THEN
                REWRITE_TAC[sha512_compress] THEN
                ENSURES_INIT_TAC "s0" THEN
                SUBGOAL_THEN
                  `read (memory :> bytes64 (word_add kptr (word 40))) s0 =
                   EL 5 sha512_K`
                ASSUME_TAC THENL
                 [FIRST_X_ASSUM(MP_TAC o SPEC `5`) THEN
                  REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                  DISCH_THEN MATCH_ACCEPT_TAC;
                  ALL_TAC] THEN
                ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                            sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                CONV_TAC(DEPTH_CONV EL_CONV) THEN
                SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                         WORD_ZX_TRIVIAL] THEN
                REWRITE_TAC[EQ_REFL] THEN
                REPEAT CONJ_TAC THENL
                 [SUBGOAL_THEN `EL 5 (M_i:int64 list) = EL 5 (W:int64 list)`
                  SUBST1_TAC
                  THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                  CONV_TAC WORD_RULE;
                  SUBGOAL_THEN `EL 5 (M_i:int64 list) = EL 5 (W:int64 list)`
                  SUBST1_TAC
                  THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                  CONV_TAC WORD_RULE;
                  MP_TAC(SPECL [`5`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                  EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                  SUBGOAL_THEN
                    `!j. j < 21 ==>
                         EL j (sha512_message_schedule 5 (M_i:int64 list)) =
                         EL j (sha512_message_schedule 64 M_i)`
                  MP_TAC THENL
                   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                    MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                    ASM_ARITH_TAC; ALL_TAC] THEN
                  DISCH_THEN(fun th ->
                    MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                      [5; 6; 14; 19]) THEN
                  REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                  ASM_REWRITE_TAC[] THEN
                  REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                  DISCH_THEN SUBST1_TAC THEN
                  SUBGOAL_THEN
                    `EL 5 (M_i:int64 list) = EL 5 (W:int64 list) /\
                     EL 6 M_i = EL 6 W /\
                     EL 14 M_i = EL 14 W`
                  (fun th -> REWRITE_TAC[th]) THENL
                   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                    ALL_TAC] THEN
                  CONV_TAC WORD_RULE];

                (* ----- Period 0 round 6: pc+0x398..pc+0x410, 30 insts (ROUND_SCHED_K6).
                   SHA512_W_EXTEND at n=6 + SCHEDULE_MONO at slot indices {6,7,15,20}.  *)
                ENSURES_SEQUENCE_TAC `pc + 0x410`
                  `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                       read SP s = stackpointer /\
                       read X29 s = state_ptr /\
                       read X30 s = word 4 /\
                       read X3 s = word_add kptr (word 56) /\
                       read X5 s = (EL 0 (sha512_compress 7 W
                                  [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X6 s = (EL 1 (sha512_compress 7 W
                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X7 s = (EL 2 (sha512_compress 7 W
                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X8 s = (EL 3 (sha512_compress 7 W
                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X9 s = (EL 4 (sha512_compress 7 W
                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X10 s = (EL 5 (sha512_compress 7 W
                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X11 s = (EL 6 (sha512_compress 7 W
                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X4 s = (EL 7 (sha512_compress 7 W
                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                       read X19 s = (EL 16 (W:int64 list)) /\
                       read X20 s = (EL 17 (W:int64 list)) /\
                       read X21 s = (EL 18 (W:int64 list)) /\
                       read X22 s = (EL 19 (W:int64 list)) /\
                       read X23 s = (EL 20 (W:int64 list)) /\
                       read X24 s = (EL 21 (W:int64 list)) /\
                       read X25 s = (EL 22 (W:int64 list)) /\
                       read X26 s = EL  7 M_i:int64 /\
                       read X27 s = EL  8 M_i:int64 /\
                       read X28 s = EL  9 M_i:int64 /\
                       read X12 s = (EL 10 M_i:int64) /\
                       read X13 s = (EL 11 M_i:int64) /\
                       read X14 s = (EL 12 M_i:int64) /\
                       read X15 s = (EL 13 M_i:int64) /\
                       read X16 s = (EL 14 M_i:int64) /\
                       read X17 s = (EL 15 M_i:int64) /\
                       read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                         dptr_i /\
                       read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                         word(num_blocks - ii) /\
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
                 [(* Round 6 body proof *)
                  ONCE_REWRITE_TAC[ARITH_RULE `7 = 6 + 1`] THEN
                  REWRITE_TAC[sha512_compress] THEN
                  ENSURES_INIT_TAC "s0" THEN
                  SUBGOAL_THEN
                    `read (memory :> bytes64 (word_add kptr (word 48))) s0 =
                     EL 6 sha512_K`
                  ASSUME_TAC THENL
                   [FIRST_X_ASSUM(MP_TAC o SPEC `6`) THEN
                    REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                    DISCH_THEN MATCH_ACCEPT_TAC;
                    ALL_TAC] THEN
                  ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                  REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                              sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                  CONV_TAC(DEPTH_CONV EL_CONV) THEN
                  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                           WORD_ZX_TRIVIAL] THEN
                  REWRITE_TAC[EQ_REFL] THEN
                  REPEAT CONJ_TAC THENL
                   [SUBGOAL_THEN `EL 6 (M_i:int64 list) = EL 6 (W:int64 list)`
                    SUBST1_TAC
                    THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                    CONV_TAC WORD_RULE;
                    SUBGOAL_THEN `EL 6 (M_i:int64 list) = EL 6 (W:int64 list)`
                    SUBST1_TAC
                    THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                    CONV_TAC WORD_RULE;
                    MP_TAC(SPECL [`6`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                    EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                    SUBGOAL_THEN
                      `!j. j < 22 ==>
                           EL j (sha512_message_schedule 6 (M_i:int64 list)) =
                           EL j (sha512_message_schedule 64 M_i)`
                    MP_TAC THENL
                     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                      MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                      ASM_ARITH_TAC; ALL_TAC] THEN
                    DISCH_THEN(fun th ->
                      MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                        [6; 7; 15; 20]) THEN
                    REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                    ASM_REWRITE_TAC[] THEN
                    REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                    DISCH_THEN SUBST1_TAC THEN
                    SUBGOAL_THEN
                      `EL 6 (M_i:int64 list) = EL 6 (W:int64 list) /\
                       EL 7 M_i = EL 7 W /\
                       EL 15 M_i = EL 15 W`
                    (fun th -> REWRITE_TAC[th]) THENL
                     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                      ALL_TAC] THEN
                    CONV_TAC WORD_RULE];

                  (* ----- Period 0 round 7: pc+0x410..pc+0x488, 30 insts (ROUND_SCHED_K7).
                     SHA512_W_EXTEND at n=7 + SCHEDULE_MONO at slot indices {7,8,16,21}.  *)
                  ENSURES_SEQUENCE_TAC `pc + 0x488`
                    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                         read SP s = stackpointer /\
                         read X29 s = state_ptr /\
                         read X30 s = word 4 /\
                         read X3 s = word_add kptr (word 64) /\
                         read X4 s = (EL 0 (sha512_compress 8 W
                                    [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X5 s = (EL 1 (sha512_compress 8 W
                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X6 s = (EL 2 (sha512_compress 8 W
                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X7 s = (EL 3 (sha512_compress 8 W
                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X8 s = (EL 4 (sha512_compress 8 W
                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X9 s = (EL 5 (sha512_compress 8 W
                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X10 s = (EL 6 (sha512_compress 8 W
                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X11 s = (EL 7 (sha512_compress 8 W
                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                         read X19 s = (EL 16 (W:int64 list)) /\
                         read X20 s = (EL 17 (W:int64 list)) /\
                         read X21 s = (EL 18 (W:int64 list)) /\
                         read X22 s = (EL 19 (W:int64 list)) /\
                         read X23 s = (EL 20 (W:int64 list)) /\
                         read X24 s = (EL 21 (W:int64 list)) /\
                         read X25 s = (EL 22 (W:int64 list)) /\
                         read X26 s = (EL 23 (W:int64 list)) /\
                         read X27 s = EL  8 M_i:int64 /\
                         read X28 s = EL  9 M_i:int64 /\
                         read X12 s = (EL 10 M_i:int64) /\
                         read X13 s = (EL 11 M_i:int64) /\
                         read X14 s = (EL 12 M_i:int64) /\
                         read X15 s = (EL 13 M_i:int64) /\
                         read X16 s = (EL 14 M_i:int64) /\
                         read X17 s = (EL 15 M_i:int64) /\
                         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                           dptr_i /\
                         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                           word(num_blocks - ii) /\
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
                   [(* Round 7 body proof *)
                    ONCE_REWRITE_TAC[ARITH_RULE `8 = 7 + 1`] THEN
                    REWRITE_TAC[sha512_compress] THEN
                    ENSURES_INIT_TAC "s0" THEN
                    SUBGOAL_THEN
                      `read (memory :> bytes64 (word_add kptr (word 56))) s0 =
                       EL 7 sha512_K`
                    ASSUME_TAC THENL
                     [FIRST_X_ASSUM(MP_TAC o SPEC `7`) THEN
                      REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                      CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                      DISCH_THEN MATCH_ACCEPT_TAC;
                      ALL_TAC] THEN
                    ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                    REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                    CONV_TAC(DEPTH_CONV EL_CONV) THEN
                    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                             WORD_ZX_TRIVIAL] THEN
                    REWRITE_TAC[EQ_REFL] THEN
                    REPEAT CONJ_TAC THENL
                     [SUBGOAL_THEN `EL 7 (M_i:int64 list) = EL 7 (W:int64 list)`
                      SUBST1_TAC
                      THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                      CONV_TAC WORD_RULE;
                      SUBGOAL_THEN `EL 7 (M_i:int64 list) = EL 7 (W:int64 list)`
                      SUBST1_TAC
                      THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                      CONV_TAC WORD_RULE;
                      MP_TAC(SPECL [`7`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                      EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                      SUBGOAL_THEN
                        `!j. j < 23 ==>
                             EL j (sha512_message_schedule 7 (M_i:int64 list)) =
                             EL j (sha512_message_schedule 64 M_i)`
                      MP_TAC THENL
                       [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                        MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                        ASM_ARITH_TAC; ALL_TAC] THEN
                      DISCH_THEN(fun th ->
                        MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                          [7; 8; 16; 21]) THEN
                      REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                      ASM_REWRITE_TAC[] THEN
                      REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                      DISCH_THEN SUBST1_TAC THEN
                      SUBGOAL_THEN
                        `EL 7 (M_i:int64 list) = EL 7 (W:int64 list) /\
                         EL 8 M_i = EL 8 W`
                      (fun th -> REWRITE_TAC[th]) THENL
                       [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                        ALL_TAC] THEN
                      CONV_TAC WORD_RULE];

                    (* ----- Period 0 round 8: pc+0x488..pc+0x500, 30 insts (ROUND_SCHED_K0).
                       SHA512_W_EXTEND at n=8 + SCHEDULE_MONO at slot indices {8,9,17,22}.  *)
                    ENSURES_SEQUENCE_TAC `pc + 0x500`
                      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                           read SP s = stackpointer /\
                           read X29 s = state_ptr /\
                           read X30 s = word 4 /\
                           read X3 s = word_add kptr (word 72) /\
                           read X11 s = (EL 0 (sha512_compress 9 W
                                      [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X4 s = (EL 1 (sha512_compress 9 W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X5 s = (EL 2 (sha512_compress 9 W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X6 s = (EL 3 (sha512_compress 9 W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X7 s = (EL 4 (sha512_compress 9 W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X8 s = (EL 5 (sha512_compress 9 W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X9 s = (EL 6 (sha512_compress 9 W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X10 s = (EL 7 (sha512_compress 9 W
                                      [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                           read X19 s = (EL 16 (W:int64 list)) /\
                           read X20 s = (EL 17 (W:int64 list)) /\
                           read X21 s = (EL 18 (W:int64 list)) /\
                           read X22 s = (EL 19 (W:int64 list)) /\
                           read X23 s = (EL 20 (W:int64 list)) /\
                           read X24 s = (EL 21 (W:int64 list)) /\
                           read X25 s = (EL 22 (W:int64 list)) /\
                           read X26 s = (EL 23 (W:int64 list)) /\
                           read X27 s = (EL 24 (W:int64 list)) /\
                           read X28 s = EL  9 M_i:int64 /\
                           read X12 s = (EL 10 M_i:int64) /\
                           read X13 s = (EL 11 M_i:int64) /\
                           read X14 s = (EL 12 M_i:int64) /\
                           read X15 s = (EL 13 M_i:int64) /\
                           read X16 s = (EL 14 M_i:int64) /\
                           read X17 s = (EL 15 M_i:int64) /\
                           read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                             dptr_i /\
                           read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                             word(num_blocks - ii) /\
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
                     [(* Round 8 body proof *)
                      ONCE_REWRITE_TAC[ARITH_RULE `9 = 8 + 1`] THEN
                      REWRITE_TAC[sha512_compress] THEN
                      ENSURES_INIT_TAC "s0" THEN
                      SUBGOAL_THEN
                        `read (memory :> bytes64 (word_add kptr (word 64))) s0 =
                         EL 8 sha512_K`
                      ASSUME_TAC THENL
                       [FIRST_X_ASSUM(MP_TAC o SPEC `8`) THEN
                        REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                        CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                        DISCH_THEN MATCH_ACCEPT_TAC;
                        ALL_TAC] THEN
                      ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                      REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                  sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                      CONV_TAC(DEPTH_CONV EL_CONV) THEN
                      SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                               WORD_ZX_TRIVIAL] THEN
                      REWRITE_TAC[EQ_REFL] THEN
                      REPEAT CONJ_TAC THENL
                       [SUBGOAL_THEN `EL 8 (M_i:int64 list) = EL 8 (W:int64 list)`
                        SUBST1_TAC
                        THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                        CONV_TAC WORD_RULE;
                        SUBGOAL_THEN `EL 8 (M_i:int64 list) = EL 8 (W:int64 list)`
                        SUBST1_TAC
                        THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                        CONV_TAC WORD_RULE;
                        MP_TAC(SPECL [`8`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                        EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                        SUBGOAL_THEN
                          `!j. j < 24 ==>
                               EL j (sha512_message_schedule 8 (M_i:int64 list)) =
                               EL j (sha512_message_schedule 64 M_i)`
                        MP_TAC THENL
                         [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                          MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                          ASM_ARITH_TAC; ALL_TAC] THEN
                        DISCH_THEN(fun th ->
                          MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                            [8; 9; 17; 22]) THEN
                        REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                        ASM_REWRITE_TAC[] THEN
                        REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                        DISCH_THEN SUBST1_TAC THEN
                        SUBGOAL_THEN
                          `EL 8 (M_i:int64 list) = EL 8 (W:int64 list) /\
                           EL 9 M_i = EL 9 W`
                        (fun th -> REWRITE_TAC[th]) THENL
                         [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                          ALL_TAC] THEN
                        CONV_TAC WORD_RULE];

                      (* ----- Period 0 round 9: pc+0x500..pc+0x578, 30 insts (ROUND_SCHED_K1).
                         SHA512_W_EXTEND at n=9 + SCHEDULE_MONO at slot indices {9,10,18,23}.  *)
                      ENSURES_SEQUENCE_TAC `pc + 0x578`
                        `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                             read SP s = stackpointer /\
                             read X29 s = state_ptr /\
                             read X30 s = word 4 /\
                             read X3 s = word_add kptr (word 80) /\
                             read X10 s = (EL 0 (sha512_compress 10 W
                                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X11 s = (EL 1 (sha512_compress 10 W
                                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X4 s = (EL 2 (sha512_compress 10 W
                                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X5 s = (EL 3 (sha512_compress 10 W
                                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X6 s = (EL 4 (sha512_compress 10 W
                                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X7 s = (EL 5 (sha512_compress 10 W
                                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X8 s = (EL 6 (sha512_compress 10 W
                                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X9 s = (EL 7 (sha512_compress 10 W
                                        [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                             read X19 s = (EL 16 (W:int64 list)) /\
                             read X20 s = (EL 17 (W:int64 list)) /\
                             read X21 s = (EL 18 (W:int64 list)) /\
                             read X22 s = (EL 19 (W:int64 list)) /\
                             read X23 s = (EL 20 (W:int64 list)) /\
                             read X24 s = (EL 21 (W:int64 list)) /\
                             read X25 s = (EL 22 (W:int64 list)) /\
                             read X26 s = (EL 23 (W:int64 list)) /\
                             read X27 s = (EL 24 (W:int64 list)) /\
                             read X28 s = (EL 25 (W:int64 list)) /\
                             read X12 s = (EL 10 M_i:int64) /\
                             read X13 s = (EL 11 M_i:int64) /\
                             read X14 s = (EL 12 M_i:int64) /\
                             read X15 s = (EL 13 M_i:int64) /\
                             read X16 s = (EL 14 M_i:int64) /\
                             read X17 s = (EL 15 M_i:int64) /\
                             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                               dptr_i /\
                             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                               word(num_blocks - ii) /\
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
                       [(* Round 9 body proof *)
                        ONCE_REWRITE_TAC[ARITH_RULE `10 = 9 + 1`] THEN
                        REWRITE_TAC[sha512_compress] THEN
                        ENSURES_INIT_TAC "s0" THEN
                        SUBGOAL_THEN
                          `read (memory :> bytes64 (word_add kptr (word 72))) s0 =
                           EL 9 sha512_K`
                        ASSUME_TAC THENL
                         [FIRST_X_ASSUM(MP_TAC o SPEC `9`) THEN
                          REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                          CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                          DISCH_THEN MATCH_ACCEPT_TAC;
                          ALL_TAC] THEN
                        ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                        REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                    sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                        CONV_TAC(DEPTH_CONV EL_CONV) THEN
                        SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                 WORD_ZX_TRIVIAL] THEN
                        REWRITE_TAC[EQ_REFL] THEN
                        REPEAT CONJ_TAC THENL
                         [SUBGOAL_THEN `EL 9 (M_i:int64 list) = EL 9 (W:int64 list)`
                          SUBST1_TAC
                          THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                          CONV_TAC WORD_RULE;
                          SUBGOAL_THEN `EL 9 (M_i:int64 list) = EL 9 (W:int64 list)`
                          SUBST1_TAC
                          THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                          CONV_TAC WORD_RULE;
                          MP_TAC(SPECL [`9`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                          EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                          SUBGOAL_THEN
                            `!j. j < 25 ==>
                                 EL j (sha512_message_schedule 9 (M_i:int64 list)) =
                                 EL j (sha512_message_schedule 64 M_i)`
                          MP_TAC THENL
                           [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                            MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                            ASM_ARITH_TAC; ALL_TAC] THEN
                          DISCH_THEN(fun th ->
                            MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                              [9; 10; 18; 23]) THEN
                          REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                          ASM_REWRITE_TAC[] THEN
                          REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                          DISCH_THEN SUBST1_TAC THEN
                          SUBGOAL_THEN
                            `EL 9 (M_i:int64 list) = EL 9 (W:int64 list) /\
                             EL 10 M_i = EL 10 W`
                          (fun th -> REWRITE_TAC[th]) THENL
                           [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                            ALL_TAC] THEN
                          CONV_TAC WORD_RULE];

                        (* ----- Period 0 round 10: pc+0x578..pc+0x5f0, 30 insts (ROUND_SCHED_K2).
                           SHA512_W_EXTEND at n=10 + SCHEDULE_MONO at slot indices {10,11,19,24}.  *)
                        ENSURES_SEQUENCE_TAC `pc + 0x5f0`
                          `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                               read SP s = stackpointer /\
                               read X29 s = state_ptr /\
                               read X30 s = word 4 /\
                               read X3 s = word_add kptr (word 88) /\
                               read X9 s = (EL 0 (sha512_compress 11 W
                                          [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X10 s = (EL 1 (sha512_compress 11 W
                                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X11 s = (EL 2 (sha512_compress 11 W
                                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X4 s = (EL 3 (sha512_compress 11 W
                                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X5 s = (EL 4 (sha512_compress 11 W
                                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X6 s = (EL 5 (sha512_compress 11 W
                                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X7 s = (EL 6 (sha512_compress 11 W
                                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X8 s = (EL 7 (sha512_compress 11 W
                                          [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                               read X19 s = (EL 16 (W:int64 list)) /\
                               read X20 s = (EL 17 (W:int64 list)) /\
                               read X21 s = (EL 18 (W:int64 list)) /\
                               read X22 s = (EL 19 (W:int64 list)) /\
                               read X23 s = (EL 20 (W:int64 list)) /\
                               read X24 s = (EL 21 (W:int64 list)) /\
                               read X25 s = (EL 22 (W:int64 list)) /\
                               read X26 s = (EL 23 (W:int64 list)) /\
                               read X27 s = (EL 24 (W:int64 list)) /\
                               read X28 s = (EL 25 (W:int64 list)) /\
                               read X12 s = (EL 26 (W:int64 list)) /\
                               read X13 s = (EL 11 M_i:int64) /\
                               read X14 s = (EL 12 M_i:int64) /\
                               read X15 s = (EL 13 M_i:int64) /\
                               read X16 s = (EL 14 M_i:int64) /\
                               read X17 s = (EL 15 M_i:int64) /\
                               read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                                 dptr_i /\
                               read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                                 word(num_blocks - ii) /\
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
                         [(* Round 10 body proof *)
                          ONCE_REWRITE_TAC[ARITH_RULE `11 = 10 + 1`] THEN
                          REWRITE_TAC[sha512_compress] THEN
                          ENSURES_INIT_TAC "s0" THEN
                          SUBGOAL_THEN
                            `read (memory :> bytes64 (word_add kptr (word 80))) s0 =
                             EL 10 sha512_K`
                          ASSUME_TAC THENL
                           [FIRST_X_ASSUM(MP_TAC o SPEC `10`) THEN
                            REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                            CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                            DISCH_THEN MATCH_ACCEPT_TAC;
                            ALL_TAC] THEN
                          ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                          CONV_TAC(DEPTH_CONV EL_CONV) THEN
                          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                   WORD_ZX_TRIVIAL] THEN
                          REWRITE_TAC[EQ_REFL] THEN
                          REPEAT CONJ_TAC THENL
                           [SUBGOAL_THEN `EL 10 (M_i:int64 list) = EL 10 (W:int64 list)`
                            SUBST1_TAC
                            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                            CONV_TAC WORD_RULE;
                            SUBGOAL_THEN `EL 10 (M_i:int64 list) = EL 10 (W:int64 list)`
                            SUBST1_TAC
                            THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                            CONV_TAC WORD_RULE;
                            MP_TAC(SPECL [`10`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                            EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                            SUBGOAL_THEN
                              `!j. j < 26 ==>
                                   EL j (sha512_message_schedule 10 (M_i:int64 list)) =
                                   EL j (sha512_message_schedule 64 M_i)`
                            MP_TAC THENL
                             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                              MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                              ASM_ARITH_TAC; ALL_TAC] THEN
                            DISCH_THEN(fun th ->
                              MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                                [10; 11; 19; 24]) THEN
                            REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                            ASM_REWRITE_TAC[] THEN
                            REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                            DISCH_THEN SUBST1_TAC THEN
                            SUBGOAL_THEN
                              `EL 10 (M_i:int64 list) = EL 10 (W:int64 list) /\
                               EL 11 M_i = EL 11 W`
                            (fun th -> REWRITE_TAC[th]) THENL
                             [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                              ALL_TAC] THEN
                            CONV_TAC WORD_RULE];

                          (* ----- Period 0 round 11: pc+0x5f0..pc+0x668, 30 insts (ROUND_SCHED_K3).
                             SHA512_W_EXTEND at n=11 + SCHEDULE_MONO at slot indices {11,12,20,25}.  *)
                          ENSURES_SEQUENCE_TAC `pc + 0x668`
                            `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                 read SP s = stackpointer /\
                                 read X29 s = state_ptr /\
                                 read X30 s = word 4 /\
                                 read X3 s = word_add kptr (word 96) /\
                                 read X8 s = (EL 0 (sha512_compress 12 W
                                            [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X9 s = (EL 1 (sha512_compress 12 W
                                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X10 s = (EL 2 (sha512_compress 12 W
                                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X11 s = (EL 3 (sha512_compress 12 W
                                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X4 s = (EL 4 (sha512_compress 12 W
                                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X5 s = (EL 5 (sha512_compress 12 W
                                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X6 s = (EL 6 (sha512_compress 12 W
                                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X7 s = (EL 7 (sha512_compress 12 W
                                            [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                 read X19 s = (EL 16 (W:int64 list)) /\
                                 read X20 s = (EL 17 (W:int64 list)) /\
                                 read X21 s = (EL 18 (W:int64 list)) /\
                                 read X22 s = (EL 19 (W:int64 list)) /\
                                 read X23 s = (EL 20 (W:int64 list)) /\
                                 read X24 s = (EL 21 (W:int64 list)) /\
                                 read X25 s = (EL 22 (W:int64 list)) /\
                                 read X26 s = (EL 23 (W:int64 list)) /\
                                 read X27 s = (EL 24 (W:int64 list)) /\
                                 read X28 s = (EL 25 (W:int64 list)) /\
                                 read X12 s = (EL 26 (W:int64 list)) /\
                                 read X13 s = (EL 27 (W:int64 list)) /\
                                 read X14 s = (EL 12 M_i:int64) /\
                                 read X15 s = (EL 13 M_i:int64) /\
                                 read X16 s = (EL 14 M_i:int64) /\
                                 read X17 s = (EL 15 M_i:int64) /\
                                 read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                                   dptr_i /\
                                 read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                                   word(num_blocks - ii) /\
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
                           [(* Round 11 body proof *)
                            ONCE_REWRITE_TAC[ARITH_RULE `12 = 11 + 1`] THEN
                            REWRITE_TAC[sha512_compress] THEN
                            ENSURES_INIT_TAC "s0" THEN
                            SUBGOAL_THEN
                              `read (memory :> bytes64 (word_add kptr (word 88))) s0 =
                               EL 11 sha512_K`
                            ASSUME_TAC THENL
                             [FIRST_X_ASSUM(MP_TAC o SPEC `11`) THEN
                              REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                              CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                              DISCH_THEN MATCH_ACCEPT_TAC;
                              ALL_TAC] THEN
                            ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                            ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                            REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                        sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                            CONV_TAC(DEPTH_CONV EL_CONV) THEN
                            SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                     WORD_ZX_TRIVIAL] THEN
                            REWRITE_TAC[EQ_REFL] THEN
                            REPEAT CONJ_TAC THENL
                             [SUBGOAL_THEN `EL 11 (M_i:int64 list) = EL 11 (W:int64 list)`
                              SUBST1_TAC
                              THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                              CONV_TAC WORD_RULE;
                              SUBGOAL_THEN `EL 11 (M_i:int64 list) = EL 11 (W:int64 list)`
                              SUBST1_TAC
                              THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                              CONV_TAC WORD_RULE;
                              MP_TAC(SPECL [`11`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                              EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                              CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                              SUBGOAL_THEN
                                `!j. j < 27 ==>
                                     EL j (sha512_message_schedule 11 (M_i:int64 list)) =
                                     EL j (sha512_message_schedule 64 M_i)`
                              MP_TAC THENL
                               [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                ASM_ARITH_TAC; ALL_TAC] THEN
                              DISCH_THEN(fun th ->
                                MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                                  [11; 12; 20; 25]) THEN
                              REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                              ASM_REWRITE_TAC[] THEN
                              REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                              DISCH_THEN SUBST1_TAC THEN
                              SUBGOAL_THEN
                                `EL 11 (M_i:int64 list) = EL 11 (W:int64 list) /\
                                 EL 12 M_i = EL 12 W`
                              (fun th -> REWRITE_TAC[th]) THENL
                               [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                                ALL_TAC] THEN
                              CONV_TAC WORD_RULE];

                            (* ----- Period 0 round 12: pc+0x668..pc+0x6e0, 30 insts (ROUND_SCHED_K4).
                               SHA512_W_EXTEND at n=12 + SCHEDULE_MONO at slot indices {12,13,21,26}.  *)
                            ENSURES_SEQUENCE_TAC `pc + 0x6e0`
                              `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                   read SP s = stackpointer /\
                                   read X29 s = state_ptr /\
                                   read X30 s = word 4 /\
                                   read X3 s = word_add kptr (word 104) /\
                                   read X7 s = (EL 0 (sha512_compress 13 W
                                              [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X8 s = (EL 1 (sha512_compress 13 W
                                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X9 s = (EL 2 (sha512_compress 13 W
                                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X10 s = (EL 3 (sha512_compress 13 W
                                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X11 s = (EL 4 (sha512_compress 13 W
                                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X4 s = (EL 5 (sha512_compress 13 W
                                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X5 s = (EL 6 (sha512_compress 13 W
                                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X6 s = (EL 7 (sha512_compress 13 W
                                              [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                   read X19 s = (EL 16 (W:int64 list)) /\
                                   read X20 s = (EL 17 (W:int64 list)) /\
                                   read X21 s = (EL 18 (W:int64 list)) /\
                                   read X22 s = (EL 19 (W:int64 list)) /\
                                   read X23 s = (EL 20 (W:int64 list)) /\
                                   read X24 s = (EL 21 (W:int64 list)) /\
                                   read X25 s = (EL 22 (W:int64 list)) /\
                                   read X26 s = (EL 23 (W:int64 list)) /\
                                   read X27 s = (EL 24 (W:int64 list)) /\
                                   read X28 s = (EL 25 (W:int64 list)) /\
                                   read X12 s = (EL 26 (W:int64 list)) /\
                                   read X13 s = (EL 27 (W:int64 list)) /\
                                   read X14 s = (EL 28 (W:int64 list)) /\
                                   read X15 s = (EL 13 M_i:int64) /\
                                   read X16 s = (EL 14 M_i:int64) /\
                                   read X17 s = (EL 15 M_i:int64) /\
                                   read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                                     dptr_i /\
                                   read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                                     word(num_blocks - ii) /\
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
                             [(* Round 12 body proof *)
                              ONCE_REWRITE_TAC[ARITH_RULE `13 = 12 + 1`] THEN
                              REWRITE_TAC[sha512_compress] THEN
                              ENSURES_INIT_TAC "s0" THEN
                              SUBGOAL_THEN
                                `read (memory :> bytes64 (word_add kptr (word 96))) s0 =
                                 EL 12 sha512_K`
                              ASSUME_TAC THENL
                               [FIRST_X_ASSUM(MP_TAC o SPEC `12`) THEN
                                REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                                CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                                DISCH_THEN MATCH_ACCEPT_TAC;
                                ALL_TAC] THEN
                              ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                              ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                              REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                          sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                              CONV_TAC(DEPTH_CONV EL_CONV) THEN
                              SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                       WORD_ZX_TRIVIAL] THEN
                              REWRITE_TAC[EQ_REFL] THEN
                              REPEAT CONJ_TAC THENL
                               [SUBGOAL_THEN `EL 12 (M_i:int64 list) = EL 12 (W:int64 list)`
                                SUBST1_TAC
                                THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                CONV_TAC WORD_RULE;
                                SUBGOAL_THEN `EL 12 (M_i:int64 list) = EL 12 (W:int64 list)`
                                SUBST1_TAC
                                THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                CONV_TAC WORD_RULE;
                                MP_TAC(SPECL [`12`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                                EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                                CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                SUBGOAL_THEN
                                  `!j. j < 28 ==>
                                       EL j (sha512_message_schedule 12 (M_i:int64 list)) =
                                       EL j (sha512_message_schedule 64 M_i)`
                                MP_TAC THENL
                                 [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                  MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                  ASM_ARITH_TAC; ALL_TAC] THEN
                                DISCH_THEN(fun th ->
                                  MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                                    [12; 13; 21; 26]) THEN
                                REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                                ASM_REWRITE_TAC[] THEN
                                REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                DISCH_THEN SUBST1_TAC THEN
                                SUBGOAL_THEN
                                  `EL 12 (M_i:int64 list) = EL 12 (W:int64 list) /\
                                             EL 13 M_i = EL 13 W`
                                (fun th -> REWRITE_TAC[th]) THENL
                                 [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                                  ALL_TAC] THEN
                                CONV_TAC WORD_RULE];

                              (* ----- Period 0 round 13: pc+0x6e0..pc+0x758, 30 insts (ROUND_SCHED_K5).
                                 SHA512_W_EXTEND at n=13 + SCHEDULE_MONO at slot indices {13,14,22,27}.  *)
                              ENSURES_SEQUENCE_TAC `pc + 0x758`
                                `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                     read SP s = stackpointer /\
                                     read X29 s = state_ptr /\
                                     read X30 s = word 4 /\
                                     read X3 s = word_add kptr (word 112) /\
                                     read X6 s = (EL 0 (sha512_compress 14 W
                                                [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X7 s = (EL 1 (sha512_compress 14 W
                                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X8 s = (EL 2 (sha512_compress 14 W
                                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X9 s = (EL 3 (sha512_compress 14 W
                                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X10 s = (EL 4 (sha512_compress 14 W
                                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X11 s = (EL 5 (sha512_compress 14 W
                                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X4 s = (EL 6 (sha512_compress 14 W
                                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X5 s = (EL 7 (sha512_compress 14 W
                                                [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                     read X19 s = (EL 16 (W:int64 list)) /\
                                     read X20 s = (EL 17 (W:int64 list)) /\
                                     read X21 s = (EL 18 (W:int64 list)) /\
                                     read X22 s = (EL 19 (W:int64 list)) /\
                                     read X23 s = (EL 20 (W:int64 list)) /\
                                     read X24 s = (EL 21 (W:int64 list)) /\
                                     read X25 s = (EL 22 (W:int64 list)) /\
                                     read X26 s = (EL 23 (W:int64 list)) /\
                                     read X27 s = (EL 24 (W:int64 list)) /\
                                     read X28 s = (EL 25 (W:int64 list)) /\
                                     read X12 s = (EL 26 (W:int64 list)) /\
                                     read X13 s = (EL 27 (W:int64 list)) /\
                                     read X14 s = (EL 28 (W:int64 list)) /\
                                     read X15 s = (EL 29 (W:int64 list)) /\
                                     read X16 s = (EL 14 M_i:int64) /\
                                     read X17 s = (EL 15 M_i:int64) /\
                                     read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                                       dptr_i /\
                                     read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                                       word(num_blocks - ii) /\
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
                               [(* Round 13 body proof *)
                                ONCE_REWRITE_TAC[ARITH_RULE `14 = 13 + 1`] THEN
                                REWRITE_TAC[sha512_compress] THEN
                                ENSURES_INIT_TAC "s0" THEN
                                SUBGOAL_THEN
                                  `read (memory :> bytes64 (word_add kptr (word 104))) s0 =
                                   EL 13 sha512_K`
                                ASSUME_TAC THENL
                                 [FIRST_X_ASSUM(MP_TAC o SPEC `13`) THEN
                                  REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                                  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                                  DISCH_THEN MATCH_ACCEPT_TAC;
                                  ALL_TAC] THEN
                                ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                            sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                         WORD_ZX_TRIVIAL] THEN
                                REWRITE_TAC[EQ_REFL] THEN
                                REPEAT CONJ_TAC THENL
                                 [SUBGOAL_THEN `EL 13 (M_i:int64 list) = EL 13 (W:int64 list)`
                                  SUBST1_TAC
                                  THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                  CONV_TAC WORD_RULE;
                                  SUBGOAL_THEN `EL 13 (M_i:int64 list) = EL 13 (W:int64 list)`
                                  SUBST1_TAC
                                  THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                  CONV_TAC WORD_RULE;
                                  MP_TAC(SPECL [`13`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                                  EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                                  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                  SUBGOAL_THEN
                                    `!j. j < 29 ==>
                                         EL j (sha512_message_schedule 13 (M_i:int64 list)) =
                                         EL j (sha512_message_schedule 64 M_i)`
                                  MP_TAC THENL
                                   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                    MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                    ASM_ARITH_TAC; ALL_TAC] THEN
                                  DISCH_THEN(fun th ->
                                    MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                                      [13; 14; 22; 27]) THEN
                                  REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                                  ASM_REWRITE_TAC[] THEN
                                  REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                  DISCH_THEN SUBST1_TAC THEN
                                  SUBGOAL_THEN
                                    `EL 13 (M_i:int64 list) = EL 13 (W:int64 list) /\
                                               EL 14 M_i = EL 14 W`
                                  (fun th -> REWRITE_TAC[th]) THENL
                                   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                                    ALL_TAC] THEN
                                  CONV_TAC WORD_RULE];

                                (* ----- Period 0 round 14: pc+0x758..pc+0x7d0, 30 insts (ROUND_SCHED_K6).
                                   SHA512_W_EXTEND at n=14 + SCHEDULE_MONO at slot indices {14,15,23,28}.  *)
                                ENSURES_SEQUENCE_TAC `pc + 0x7d0`
                                  `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                       read SP s = stackpointer /\
                                       read X29 s = state_ptr /\
                                       read X30 s = word 4 /\
                                       read X3 s = word_add kptr (word 120) /\
                                       read X5 s = (EL 0 (sha512_compress 15 W
                                                  [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X6 s = (EL 1 (sha512_compress 15 W
                                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X7 s = (EL 2 (sha512_compress 15 W
                                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X8 s = (EL 3 (sha512_compress 15 W
                                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X9 s = (EL 4 (sha512_compress 15 W
                                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X10 s = (EL 5 (sha512_compress 15 W
                                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X11 s = (EL 6 (sha512_compress 15 W
                                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X4 s = (EL 7 (sha512_compress 15 W
                                                  [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                       read X19 s = (EL 16 (W:int64 list)) /\
                                       read X20 s = (EL 17 (W:int64 list)) /\
                                       read X21 s = (EL 18 (W:int64 list)) /\
                                       read X22 s = (EL 19 (W:int64 list)) /\
                                       read X23 s = (EL 20 (W:int64 list)) /\
                                       read X24 s = (EL 21 (W:int64 list)) /\
                                       read X25 s = (EL 22 (W:int64 list)) /\
                                       read X26 s = (EL 23 (W:int64 list)) /\
                                       read X27 s = (EL 24 (W:int64 list)) /\
                                       read X28 s = (EL 25 (W:int64 list)) /\
                                       read X12 s = (EL 26 (W:int64 list)) /\
                                       read X13 s = (EL 27 (W:int64 list)) /\
                                       read X14 s = (EL 28 (W:int64 list)) /\
                                       read X15 s = (EL 29 (W:int64 list)) /\
                                       read X16 s = (EL 30 (W:int64 list)) /\
                                       read X17 s = (EL 15 M_i:int64) /\
                                       read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                                         dptr_i /\
                                       read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                                         word(num_blocks - ii) /\
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
                                 [(* Round 14 body proof *)
                                  ONCE_REWRITE_TAC[ARITH_RULE `15 = 14 + 1`] THEN
                                  REWRITE_TAC[sha512_compress] THEN
                                  ENSURES_INIT_TAC "s0" THEN
                                  SUBGOAL_THEN
                                    `read (memory :> bytes64 (word_add kptr (word 112))) s0 =
                                     EL 14 sha512_K`
                                  ASSUME_TAC THENL
                                   [FIRST_X_ASSUM(MP_TAC o SPEC `14`) THEN
                                    REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                                    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                                    DISCH_THEN MATCH_ACCEPT_TAC;
                                    ALL_TAC] THEN
                                  ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                  REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                              sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                  CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                           WORD_ZX_TRIVIAL] THEN
                                  REWRITE_TAC[EQ_REFL] THEN
                                  REPEAT CONJ_TAC THENL
                                   [SUBGOAL_THEN `EL 14 (M_i:int64 list) = EL 14 (W:int64 list)`
                                    SUBST1_TAC
                                    THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                    CONV_TAC WORD_RULE;
                                    SUBGOAL_THEN `EL 14 (M_i:int64 list) = EL 14 (W:int64 list)`
                                    SUBST1_TAC
                                    THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                    CONV_TAC WORD_RULE;
                                    MP_TAC(SPECL [`14`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                                    EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                                    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                    SUBGOAL_THEN
                                      `!j. j < 30 ==>
                                           EL j (sha512_message_schedule 14 (M_i:int64 list)) =
                                           EL j (sha512_message_schedule 64 M_i)`
                                    MP_TAC THENL
                                     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                      MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                      ASM_ARITH_TAC; ALL_TAC] THEN
                                    DISCH_THEN(fun th ->
                                      MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                                        [14; 15; 23; 28]) THEN
                                    REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                                    ASM_REWRITE_TAC[] THEN
                                    REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                    DISCH_THEN SUBST1_TAC THEN
                                    SUBGOAL_THEN
                                      `EL 14 (M_i:int64 list) = EL 14 (W:int64 list) /\
                                                 EL 15 M_i = EL 15 W`
                                    (fun th -> REWRITE_TAC[th]) THENL
                                     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                                      ALL_TAC] THEN
                                    CONV_TAC WORD_RULE];

                                  (* ----- Period 0 round 15: pc+0x7d0..pc+0x848, 30 insts (ROUND_SCHED_K7).
                                     SHA512_W_EXTEND at n=15 + SCHEDULE_MONO at slot indices {15,16,24,29}.  *)
                                  ENSURES_SEQUENCE_TAC `pc + 0x848`
                                    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                         read SP s = stackpointer /\
                                         read X29 s = state_ptr /\
                                         read X30 s = word 4 /\
                                         read X3 s = word_add kptr (word 128) /\
                                         read X4 s = (EL 0 (sha512_compress 16 W
                                                    [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X5 s = (EL 1 (sha512_compress 16 W
                                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X6 s = (EL 2 (sha512_compress 16 W
                                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X7 s = (EL 3 (sha512_compress 16 W
                                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X8 s = (EL 4 (sha512_compress 16 W
                                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X9 s = (EL 5 (sha512_compress 16 W
                                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X10 s = (EL 6 (sha512_compress 16 W
                                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X11 s = (EL 7 (sha512_compress 16 W
                                                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                         read X19 s = (EL 16 (W:int64 list)) /\
                                         read X20 s = (EL 17 (W:int64 list)) /\
                                         read X21 s = (EL 18 (W:int64 list)) /\
                                         read X22 s = (EL 19 (W:int64 list)) /\
                                         read X23 s = (EL 20 (W:int64 list)) /\
                                         read X24 s = (EL 21 (W:int64 list)) /\
                                         read X25 s = (EL 22 (W:int64 list)) /\
                                         read X26 s = (EL 23 (W:int64 list)) /\
                                         read X27 s = (EL 24 (W:int64 list)) /\
                                         read X28 s = (EL 25 (W:int64 list)) /\
                                         read X12 s = (EL 26 (W:int64 list)) /\
                                         read X13 s = (EL 27 (W:int64 list)) /\
                                         read X14 s = (EL 28 (W:int64 list)) /\
                                         read X15 s = (EL 29 (W:int64 list)) /\
                                         read X16 s = (EL 30 (W:int64 list)) /\
                                         read X17 s = (EL 31 (W:int64 list)) /\
                                         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
                                           dptr_i /\
                                         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
                                           word(num_blocks - ii) /\
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
                                   [(* Round 15 body proof *)
                                    ONCE_REWRITE_TAC[ARITH_RULE `16 = 15 + 1`] THEN
                                    REWRITE_TAC[sha512_compress] THEN
                                    ENSURES_INIT_TAC "s0" THEN
                                    SUBGOAL_THEN
                                      `read (memory :> bytes64 (word_add kptr (word 120))) s0 =
                                       EL 15 sha512_K`
                                    ASSUME_TAC THENL
                                     [FIRST_X_ASSUM(MP_TAC o SPEC `15`) THEN
                                      REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
                                      CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                                      DISCH_THEN MATCH_ACCEPT_TAC;
                                      ALL_TAC] THEN
                                    ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                    REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                    CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                             WORD_ZX_TRIVIAL] THEN
                                    REWRITE_TAC[EQ_REFL] THEN
                                    REPEAT CONJ_TAC THENL
                                     [SUBGOAL_THEN `EL 15 (M_i:int64 list) = EL 15 (W:int64 list)`
                                      SUBST1_TAC
                                      THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                      CONV_TAC WORD_RULE;
                                      SUBGOAL_THEN `EL 15 (M_i:int64 list) = EL 15 (W:int64 list)`
                                      SUBST1_TAC
                                      THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                      CONV_TAC WORD_RULE;
                                      MP_TAC(SPECL [`15`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
                                      EXPAND_TAC "W" THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
                                      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                      SUBGOAL_THEN
                                        `!j. j < 31 ==>
                                             EL j (sha512_message_schedule 15 (M_i:int64 list)) =
                                             EL j (sha512_message_schedule 64 M_i)`
                                      MP_TAC THENL
                                       [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                        MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                        ASM_ARITH_TAC; ALL_TAC] THEN
                                      DISCH_THEN(fun th ->
                                        MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th))
                                          [15; 16; 24; 29]) THEN
                                      REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
                                      ASM_REWRITE_TAC[] THEN
                                      REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                      DISCH_THEN SUBST1_TAC THEN
                                      SUBGOAL_THEN
                                        `EL 15 (M_i:int64 list) = EL 15 (W:int64 list)`
                                      (fun th -> REWRITE_TAC[th]) THENL
                                       [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
                                        ALL_TAC] THEN
                                      CONV_TAC WORD_RULE];

                                    (* ===== Periods 1, 2 via ENSURES_WHILE_UP_TAC.
                                       Runs 2 iterations from pc+0xc8 to pc+0x84c.
                                       After p=0 round 15 (at pc+0x848): X30=word 3,
                                       compress(16), slots[0..15] = W[16..31].  *)
                                    ENSURES_WHILE_UP_TAC `3:num` `pc + 0xc8` `pc + 0x84c`
                                      `\i s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                             read SP s = stackpointer /\
                                             read X29 s = state_ptr /\
                                             read X30 s = word (3 - i) /\
                                             read X3 s = word_add kptr (word(128 * (i+1))) /\
                                             read X4 s = (EL 0 (sha512_compress (16 * (i + 1)) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X5 s = (EL 1 (sha512_compress (16 * (i + 1)) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X6 s = (EL 2 (sha512_compress (16 * (i + 1)) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X7 s = (EL 3 (sha512_compress (16 * (i + 1)) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X8 s = (EL 4 (sha512_compress (16 * (i + 1)) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X9 s = (EL 5 (sha512_compress (16 * (i + 1)) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X10 s = (EL 6 (sha512_compress (16 * (i + 1)) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X11 s = (EL 7 (sha512_compress (16 * (i + 1)) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X19 s = EL (16 * (i + 1) + 0) (W:int64 list) /\
                                             read X20 s = EL (16 * (i + 1) + 1) (W:int64 list) /\
                                             read X21 s = EL (16 * (i + 1) + 2) (W:int64 list) /\
                                             read X22 s = EL (16 * (i + 1) + 3) (W:int64 list) /\
                                             read X23 s = EL (16 * (i + 1) + 4) (W:int64 list) /\
                                             read X24 s = EL (16 * (i + 1) + 5) (W:int64 list) /\
                                             read X25 s = EL (16 * (i + 1) + 6) (W:int64 list) /\
                                             read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                             read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                             read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                             read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                             read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                             read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                             read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                             read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                             read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                             read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                             read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
                                     [ARITH_TAC;   (* k != 0 *)

                                      (* ENTRY: sub + cbnz taken from pc+0x848 to pc+0xc8.
                                         At entry: X30=word 3, compress=16, slots=W[16..31].
                                         After sub: X30=word 2. After cbnz taken: PC=pc+0xc8.
                                         invariant(0) says: X30=word(2-0)=word 2, compress=16,
                                         slots=W[16..]. *)
                                      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
                                      SUBGOAL_THEN `(4:num) < 2 EXP 64` ASSUME_TAC THENL
                                       [ARITH_TAC; ALL_TAC] THEN
                                      VAL_INT64_TAC `4:num` THEN
                                      ENSURES_INIT_TAC "s0" THEN
                                      ARM_STEPS_TAC NOHW3_EXEC (1--2) THEN
                                      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                      REWRITE_TAC[ARITH_RULE `3 - 0 = 3`;
                                                  ARITH_RULE `16 * (0 + 1) = 16`;
                                                  ARITH_RULE `16 * (0 + 1) + 0 = 16`;
                                                  ARITH_RULE `16 * (0 + 1) + 1 = 17`;
                                                  ARITH_RULE `16 * (0 + 1) + 2 = 18`;
                                                  ARITH_RULE `16 * (0 + 1) + 3 = 19`;
                                                  ARITH_RULE `16 * (0 + 1) + 4 = 20`;
                                                  ARITH_RULE `16 * (0 + 1) + 5 = 21`;
                                                  ARITH_RULE `16 * (0 + 1) + 6 = 22`;
                                                  ARITH_RULE `16 * (0 + 1) + 7 = 23`;
                                                  ARITH_RULE `16 * (0 + 1) + 8 = 24`;
                                                  ARITH_RULE `16 * (0 + 1) + 9 = 25`;
                                                  ARITH_RULE `16 * (0 + 1) + 10 = 26`;
                                                  ARITH_RULE `16 * (0 + 1) + 11 = 27`;
                                                  ARITH_RULE `16 * (0 + 1) + 12 = 28`;
                                                  ARITH_RULE `16 * (0 + 1) + 13 = 29`;
                                                  ARITH_RULE `16 * (0 + 1) + 14 = 30`;
                                                  ARITH_RULE `16 * (0 + 1) + 15 = 31`;
                                                  ARITH_RULE `64 * (0 + 1) = 64`] THEN
                                      REWRITE_TAC[ADD_CLAUSES] THEN
                                      REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;

                                      (* BODY i (0 or 1): invariant(i) at pc+0xc8 -> invariant(i+1) at pc+0x84c.
                                         16 ROUND_SCHED rounds (30 insts each) + sub at pc+0x848. *)
                                      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
                                      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
                                      ENSURES_SEQUENCE_TAC `pc + 0x140`
                                        `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                             read SP s = stackpointer /\
                                             read X29 s = state_ptr /\
                                             read X30 s = word (3 - i) /\
                                             read X3 s = word_add kptr (word (64 * (i + 1) + 4)) /\
                                             read X11 s = (EL 0 (sha512_compress (16 * (i + 1) + 1) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X4 s = (EL 1 (sha512_compress (16 * (i + 1) + 1) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X5 s = (EL 2 (sha512_compress (16 * (i + 1) + 1) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X6 s = (EL 3 (sha512_compress (16 * (i + 1) + 1) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X7 s = (EL 4 (sha512_compress (16 * (i + 1) + 1) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X8 s = (EL 5 (sha512_compress (16 * (i + 1) + 1) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X9 s = (EL 6 (sha512_compress (16 * (i + 1) + 1) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X10 s = (EL 7 (sha512_compress (16 * (i + 1) + 1) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                             read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                             read X20 s = EL (16 * (i + 1) + 1) (W:int64 list) /\
                                             read X21 s = EL (16 * (i + 1) + 2) (W:int64 list) /\
                                             read X22 s = EL (16 * (i + 1) + 3) (W:int64 list) /\
                                             read X23 s = EL (16 * (i + 1) + 4) (W:int64 list) /\
                                             read X24 s = EL (16 * (i + 1) + 5) (W:int64 list) /\
                                             read X25 s = EL (16 * (i + 1) + 6) (W:int64 list) /\
                                             read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                             read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                             read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                             read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                             read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                             read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                             read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                             read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                             read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                             read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                             read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                       [(* ----- BODY round 0 at rotation k=0: pc+0xc8..pc+0x140, 30 insts ----- *)
                                        ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 1 = (16 * (i + 1)) + 1`] THEN
                                        REWRITE_TAC[sha512_compress] THEN
                                        SUBGOAL_THEN `word_add kptr (word(128 * (i+1))):int64 =
                                                      word_add kptr (word (4 * (16 * (i + 1))))` SUBST_ALL_TAC THENL
                                         [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                        ENSURES_INIT_TAC "s0" THEN
                                        SUBGOAL_THEN
                                           `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1)))))) s0 =
                                            EL (16 * (i + 1)) sha512_K`
                                        ASSUME_TAC THENL
                                         [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1):num`) THEN
                                          ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                          DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                        ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                        REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                    sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                        MP_TAC(SPECL [`16 * (i + 1):num`;
                                                      `W:int64 list`;
                                                      `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                     LIST_8_COMPRESS_NOHW3_64) THEN
                                        ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                        DISCH_THEN(X_CHOOSE_THEN `a_bk0:int64`
                                          (X_CHOOSE_THEN `b_bk0:int64` (X_CHOOSE_THEN `c_bk0:int64`
                                          (X_CHOOSE_THEN `d_bk0:int64` (X_CHOOSE_THEN `e_bk0:int64`
                                          (X_CHOOSE_THEN `f_bk0:int64` (X_CHOOSE_THEN `g_bk0:int64`
                                          (X_CHOOSE_THEN `h_bk0:int64` ASSUME_TAC)))))))) THEN
                                        ASM_REWRITE_TAC[] THEN
                                        CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                        SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                 WORD_ZX_TRIVIAL] THEN
                                        REWRITE_TAC[EQ_REFL] THEN
                                        REWRITE_TAC[ADD_CLAUSES] THEN
                                        REPEAT CONJ_TAC THENL
                                         [CONV_TAC WORD_RULE;
                                          CONV_TAC WORD_RULE;
                                          CONV_TAC WORD_RULE;
                                          MP_TAC(SPECL [`16 * (i + 1):num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                          ANTS_TAC THENL
                                           [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                          SUBGOAL_THEN
                                           `!j. j < 16 + 16 * (i + 1) ==>
                                                EL j (sha512_message_schedule (16 * (i + 1)) (M_i:int64 list)) =
                                                EL j (sha512_message_schedule 64 M_i)`
                                          MP_TAC THENL
                                           [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                            MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                            UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1)` THEN ARITH_TAC;
                                            ALL_TAC] THEN
                                          DISCH_THEN(fun th ->
                                            MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                              [`16 * (i + 1):num`; `16 * (i + 1) + 1`;
                                               `16 * (i + 1) + 9`; `16 * (i + 1) + 14`]) THEN
                                          REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                          ASM_REWRITE_TAC[] THEN
                                          REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                          DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                        (* ----- BODY round 1 at rotation k=1: pc+0x140..pc+0x1b8 ----- *)
                                        ENSURES_SEQUENCE_TAC `pc + 0x1b8`
                                          `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                               read SP s = stackpointer /\
                                               read X29 s = state_ptr /\
                                               read X30 s = word (3 - i) /\
                                               read X3 s = word_add kptr (word (64 * (i + 1) + 8)) /\
                                               read X10 s = (EL 0 (sha512_compress (16 * (i + 1) + 2) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X11 s = (EL 1 (sha512_compress (16 * (i + 1) + 2) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X4 s = (EL 2 (sha512_compress (16 * (i + 1) + 2) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X5 s = (EL 3 (sha512_compress (16 * (i + 1) + 2) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X6 s = (EL 4 (sha512_compress (16 * (i + 1) + 2) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X7 s = (EL 5 (sha512_compress (16 * (i + 1) + 2) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X8 s = (EL 6 (sha512_compress (16 * (i + 1) + 2) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X9 s = (EL 7 (sha512_compress (16 * (i + 1) + 2) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                               read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                               read X21 s = EL (16 * (i + 1) + 2) (W:int64 list) /\
                                               read X22 s = EL (16 * (i + 1) + 3) (W:int64 list) /\
                                               read X23 s = EL (16 * (i + 1) + 4) (W:int64 list) /\
                                               read X24 s = EL (16 * (i + 1) + 5) (W:int64 list) /\
                                               read X25 s = EL (16 * (i + 1) + 6) (W:int64 list) /\
                                               read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                               read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                               read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                               read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                               read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                               read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                               read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                               read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                               read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                               read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                               read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                         [(* BODY round 1: rotation k=1, WT=X20 WT1=X21 WT9=X12 WT14=X17 *)
                                          ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 2 = (16 * (i + 1) + 1) + 1`] THEN
                                          REWRITE_TAC[sha512_compress] THEN
                                          SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 4)):int64 =
                                                        word_add kptr (word (4 * (16 * (i + 1) + 1)))` SUBST_ALL_TAC THENL
                                           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                          ENSURES_INIT_TAC "s0" THEN
                                          SUBGOAL_THEN
                                             `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 1))))) s0 =
                                              EL (16 * (i + 1) + 1) sha512_K`
                                          ASSUME_TAC THENL
                                           [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 1:num`) THEN
                                            ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                          ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                          MP_TAC(SPECL [`16 * (i + 1) + 1:num`;
                                                        `W:int64 list`;
                                                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                       LIST_8_COMPRESS_NOHW3_64) THEN
                                          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                          DISCH_THEN(X_CHOOSE_THEN `a_bk1:int64`
                                            (X_CHOOSE_THEN `b_bk1:int64` (X_CHOOSE_THEN `c_bk1:int64`
                                            (X_CHOOSE_THEN `d_bk1:int64` (X_CHOOSE_THEN `e_bk1:int64`
                                            (X_CHOOSE_THEN `f_bk1:int64` (X_CHOOSE_THEN `g_bk1:int64`
                                            (X_CHOOSE_THEN `h_bk1:int64` ASSUME_TAC)))))))) THEN
                                          ASM_REWRITE_TAC[] THEN
                                          CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                   WORD_ZX_TRIVIAL] THEN
                                          REWRITE_TAC[EQ_REFL] THEN
                                          REWRITE_TAC[ADD_CLAUSES] THEN
                                          REPEAT CONJ_TAC THENL
                                           [CONV_TAC WORD_RULE;
                                            CONV_TAC WORD_RULE;
                                            CONV_TAC WORD_RULE;
                                            MP_TAC(SPECL [`16 * (i + 1) + 1:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                            ANTS_TAC THENL
                                             [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                              REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 1) + 16 = 16 * (i + 1) + 17`;
                                                          ARITH_RULE `(16 * (i + 1) + 1) + 14 = 16 * (i + 1) + 15`;
                                                          ARITH_RULE `(16 * (i + 1) + 1) + 9 = 16 * (i + 1) + 10`;
                                                          ARITH_RULE `(16 * (i + 1) + 1) + 1 = 16 * (i + 1) + 2`] THEN
                                            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                            SUBGOAL_THEN
                                             `!j. j < 16 + 16 * (i + 1) + 1 ==>
                                                  EL j (sha512_message_schedule (16 * (i + 1) + 1) (M_i:int64 list)) =
                                                  EL j (sha512_message_schedule 64 M_i)`
                                            MP_TAC THENL
                                             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                              MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                              UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 1` THEN ARITH_TAC;
                                              ALL_TAC] THEN
                                            DISCH_THEN(fun th ->
                                              MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                [`16 * (i + 1) + 1:num`; `16 * (i + 1) + 2`;
                                                 `16 * (i + 1) + 10`; `16 * (i + 1) + 15`]) THEN
                                            REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                            ASM_REWRITE_TAC[] THEN
                                            REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                            DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                                                  (* ----- BODY round 2 at rotation k=2: pc+0x1b8..pc+0x230 ----- *)
                                        ENSURES_SEQUENCE_TAC `pc + 0x230`
                                          `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                               read SP s = stackpointer /\
                                               read X29 s = state_ptr /\
                                               read X30 s = word (3 - i) /\
                                               read X3 s = word_add kptr (word (64 * (i + 1) + 12)) /\
                                               read X9 s = (EL 0 (sha512_compress (16 * (i + 1) + 3) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X10 s = (EL 1 (sha512_compress (16 * (i + 1) + 3) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X11 s = (EL 2 (sha512_compress (16 * (i + 1) + 3) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X4 s = (EL 3 (sha512_compress (16 * (i + 1) + 3) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X5 s = (EL 4 (sha512_compress (16 * (i + 1) + 3) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X6 s = (EL 5 (sha512_compress (16 * (i + 1) + 3) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X7 s = (EL 6 (sha512_compress (16 * (i + 1) + 3) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X8 s = (EL 7 (sha512_compress (16 * (i + 1) + 3) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                               read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                               read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                               read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                               read X22 s = EL (16 * (i + 1) + 3) (W:int64 list) /\
                                               read X23 s = EL (16 * (i + 1) + 4) (W:int64 list) /\
                                               read X24 s = EL (16 * (i + 1) + 5) (W:int64 list) /\
                                               read X25 s = EL (16 * (i + 1) + 6) (W:int64 list) /\
                                               read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                               read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                               read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                               read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                               read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                               read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                               read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                               read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                               read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                               read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                               read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                         [
                                          (* BODY round 2: rotation k=2, WT=X21 WT1=X22 WT9=X13 WT14=X19 *)
                                          ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 3 = (16 * (i + 1) + 2) + 1`] THEN
                                          REWRITE_TAC[sha512_compress] THEN
                                          SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 8)):int64 =
                                                        word_add kptr (word (4 * (16 * (i + 1) + 2)))` SUBST_ALL_TAC THENL
                                           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                          ENSURES_INIT_TAC "s0" THEN
                                          SUBGOAL_THEN
                                             `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 2))))) s0 =
                                              EL (16 * (i + 1) + 2) sha512_K`
                                          ASSUME_TAC THENL
                                           [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 2:num`) THEN
                                            ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                          ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                          MP_TAC(SPECL [`16 * (i + 1) + 2:num`;
                                                        `W:int64 list`;
                                                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                       LIST_8_COMPRESS_NOHW3_64) THEN
                                          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                          DISCH_THEN(X_CHOOSE_THEN `a_bk2:int64`
                                            (X_CHOOSE_THEN `b_bk2:int64` (X_CHOOSE_THEN `c_bk2:int64`
                                            (X_CHOOSE_THEN `d_bk2:int64` (X_CHOOSE_THEN `e_bk2:int64`
                                            (X_CHOOSE_THEN `f_bk2:int64` (X_CHOOSE_THEN `g_bk2:int64`
                                            (X_CHOOSE_THEN `h_bk2:int64` ASSUME_TAC)))))))) THEN
                                          ASM_REWRITE_TAC[] THEN
                                          CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                   WORD_ZX_TRIVIAL] THEN
                                          REWRITE_TAC[EQ_REFL] THEN
                                          REWRITE_TAC[ADD_CLAUSES] THEN
                                          REPEAT CONJ_TAC THENL
                                           [CONV_TAC WORD_RULE;
                                            CONV_TAC WORD_RULE;
                                            CONV_TAC WORD_RULE;
                                            MP_TAC(SPECL [`16 * (i + 1) + 2:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                            ANTS_TAC THENL
                                             [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                              REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 2) + 16 = 16 * (i + 1) + 18`;
                                                          ARITH_RULE `(16 * (i + 1) + 2) + 14 = 16 * (i + 1) + 16`;
                                                          ARITH_RULE `(16 * (i + 1) + 2) + 9 = 16 * (i + 1) + 11`;
                                                          ARITH_RULE `(16 * (i + 1) + 2) + 1 = 16 * (i + 1) + 3`] THEN
                                            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                            SUBGOAL_THEN
                                             `!j. j < 16 + 16 * (i + 1) + 2 ==>
                                                  EL j (sha512_message_schedule (16 * (i + 1) + 2) (M_i:int64 list)) =
                                                  EL j (sha512_message_schedule 64 M_i)`
                                            MP_TAC THENL
                                             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                              MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                              UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 2` THEN ARITH_TAC;
                                              ALL_TAC] THEN
                                            DISCH_THEN(fun th ->
                                              MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                [`16 * (i + 1) + 2:num`; `16 * (i + 1) + 3`;
                                                 `16 * (i + 1) + 11`; `16 * (i + 1) + 16`]) THEN
                                            REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                            ASM_REWRITE_TAC[] THEN
                                            REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                            DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                          (* ----- BODY round 3 at rotation k=3: pc+0x230..pc+0x2a8 ----- *)
                                          ENSURES_SEQUENCE_TAC `pc + 0x2a8`
                                            `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                 read SP s = stackpointer /\
                                                 read X29 s = state_ptr /\
                                                 read X30 s = word (3 - i) /\
                                                 read X3 s = word_add kptr (word (64 * (i + 1) + 16)) /\
                                                 read X8 s = (EL 0 (sha512_compress (16 * (i + 1) + 4) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X9 s = (EL 1 (sha512_compress (16 * (i + 1) + 4) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X10 s = (EL 2 (sha512_compress (16 * (i + 1) + 4) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X11 s = (EL 3 (sha512_compress (16 * (i + 1) + 4) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X4 s = (EL 4 (sha512_compress (16 * (i + 1) + 4) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X5 s = (EL 5 (sha512_compress (16 * (i + 1) + 4) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X6 s = (EL 6 (sha512_compress (16 * (i + 1) + 4) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X7 s = (EL 7 (sha512_compress (16 * (i + 1) + 4) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                 read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                 read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                 read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                 read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                 read X23 s = EL (16 * (i + 1) + 4) (W:int64 list) /\
                                                 read X24 s = EL (16 * (i + 1) + 5) (W:int64 list) /\
                                                 read X25 s = EL (16 * (i + 1) + 6) (W:int64 list) /\
                                                 read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                                 read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                                 read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                                 read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                                 read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                 read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                 read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                 read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                 read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                 read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                 read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                           [
                                            (* BODY round 3: rotation k=3, WT=X22 WT1=X23 WT9=X14 WT14=X20 *)
                                            ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 4 = (16 * (i + 1) + 3) + 1`] THEN
                                            REWRITE_TAC[sha512_compress] THEN
                                            SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 12)):int64 =
                                                          word_add kptr (word (4 * (16 * (i + 1) + 3)))` SUBST_ALL_TAC THENL
                                             [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                            ENSURES_INIT_TAC "s0" THEN
                                            SUBGOAL_THEN
                                               `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 3))))) s0 =
                                                EL (16 * (i + 1) + 3) sha512_K`
                                            ASSUME_TAC THENL
                                             [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 3:num`) THEN
                                              ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                              DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                            ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                            ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                            REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                        sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                            MP_TAC(SPECL [`16 * (i + 1) + 3:num`;
                                                          `W:int64 list`;
                                                          `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                         LIST_8_COMPRESS_NOHW3_64) THEN
                                            ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                            DISCH_THEN(X_CHOOSE_THEN `a_bk3:int64`
                                              (X_CHOOSE_THEN `b_bk3:int64` (X_CHOOSE_THEN `c_bk3:int64`
                                              (X_CHOOSE_THEN `d_bk3:int64` (X_CHOOSE_THEN `e_bk3:int64`
                                              (X_CHOOSE_THEN `f_bk3:int64` (X_CHOOSE_THEN `g_bk3:int64`
                                              (X_CHOOSE_THEN `h_bk3:int64` ASSUME_TAC)))))))) THEN
                                            ASM_REWRITE_TAC[] THEN
                                            CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                            SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                     WORD_ZX_TRIVIAL] THEN
                                            REWRITE_TAC[EQ_REFL] THEN
                                            REWRITE_TAC[ADD_CLAUSES] THEN
                                            REPEAT CONJ_TAC THENL
                                             [CONV_TAC WORD_RULE;
                                              CONV_TAC WORD_RULE;
                                              CONV_TAC WORD_RULE;
                                              MP_TAC(SPECL [`16 * (i + 1) + 3:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                              ANTS_TAC THENL
                                               [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 3) + 16 = 16 * (i + 1) + 19`;
                                                            ARITH_RULE `(16 * (i + 1) + 3) + 14 = 16 * (i + 1) + 17`;
                                                            ARITH_RULE `(16 * (i + 1) + 3) + 9 = 16 * (i + 1) + 12`;
                                                            ARITH_RULE `(16 * (i + 1) + 3) + 1 = 16 * (i + 1) + 4`] THEN
                                              CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                              SUBGOAL_THEN
                                               `!j. j < 16 + 16 * (i + 1) + 3 ==>
                                                    EL j (sha512_message_schedule (16 * (i + 1) + 3) (M_i:int64 list)) =
                                                    EL j (sha512_message_schedule 64 M_i)`
                                              MP_TAC THENL
                                               [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 3` THEN ARITH_TAC;
                                                ALL_TAC] THEN
                                              DISCH_THEN(fun th ->
                                                MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                  [`16 * (i + 1) + 3:num`; `16 * (i + 1) + 4`;
                                                   `16 * (i + 1) + 12`; `16 * (i + 1) + 17`]) THEN
                                              REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                              ASM_REWRITE_TAC[] THEN
                                              REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                              DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                            (* ----- BODY round 4 at rotation k=4: pc+0x2a8..pc+0x320 ----- *)
                                            ENSURES_SEQUENCE_TAC `pc + 0x320`
                                              `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                   read SP s = stackpointer /\
                                                   read X29 s = state_ptr /\
                                                   read X30 s = word (3 - i) /\
                                                   read X3 s = word_add kptr (word (64 * (i + 1) + 20)) /\
                                                   read X7 s = (EL 0 (sha512_compress (16 * (i + 1) + 5) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X8 s = (EL 1 (sha512_compress (16 * (i + 1) + 5) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X9 s = (EL 2 (sha512_compress (16 * (i + 1) + 5) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X10 s = (EL 3 (sha512_compress (16 * (i + 1) + 5) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X11 s = (EL 4 (sha512_compress (16 * (i + 1) + 5) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X4 s = (EL 5 (sha512_compress (16 * (i + 1) + 5) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X5 s = (EL 6 (sha512_compress (16 * (i + 1) + 5) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X6 s = (EL 7 (sha512_compress (16 * (i + 1) + 5) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                   read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                   read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                   read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                   read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                   read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                   read X24 s = EL (16 * (i + 1) + 5) (W:int64 list) /\
                                                   read X25 s = EL (16 * (i + 1) + 6) (W:int64 list) /\
                                                   read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                                   read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                                   read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                                   read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                                   read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                   read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                   read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                   read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                   read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                   read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                   read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                             [
                                              (* BODY round 4: rotation k=4, WT=X23 WT1=X24 WT9=X15 WT14=X21 *)
                                              ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 5 = (16 * (i + 1) + 4) + 1`] THEN
                                              REWRITE_TAC[sha512_compress] THEN
                                              SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 16)):int64 =
                                                            word_add kptr (word (4 * (16 * (i + 1) + 4)))` SUBST_ALL_TAC THENL
                                               [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                              ENSURES_INIT_TAC "s0" THEN
                                              SUBGOAL_THEN
                                                 `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 4))))) s0 =
                                                  EL (16 * (i + 1) + 4) sha512_K`
                                              ASSUME_TAC THENL
                                               [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 4:num`) THEN
                                                ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                              ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                              ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                              REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                          sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                              MP_TAC(SPECL [`16 * (i + 1) + 4:num`;
                                                            `W:int64 list`;
                                                            `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                           LIST_8_COMPRESS_NOHW3_64) THEN
                                              ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                              DISCH_THEN(X_CHOOSE_THEN `a_bk4:int64`
                                                (X_CHOOSE_THEN `b_bk4:int64` (X_CHOOSE_THEN `c_bk4:int64`
                                                (X_CHOOSE_THEN `d_bk4:int64` (X_CHOOSE_THEN `e_bk4:int64`
                                                (X_CHOOSE_THEN `f_bk4:int64` (X_CHOOSE_THEN `g_bk4:int64`
                                                (X_CHOOSE_THEN `h_bk4:int64` ASSUME_TAC)))))))) THEN
                                              ASM_REWRITE_TAC[] THEN
                                              CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                              SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                       WORD_ZX_TRIVIAL] THEN
                                              REWRITE_TAC[EQ_REFL] THEN
                                              REWRITE_TAC[ADD_CLAUSES] THEN
                                              REPEAT CONJ_TAC THENL
                                               [CONV_TAC WORD_RULE;
                                                CONV_TAC WORD_RULE;
                                                CONV_TAC WORD_RULE;
                                                MP_TAC(SPECL [`16 * (i + 1) + 4:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                ANTS_TAC THENL
                                                 [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                  REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 4) + 16 = 16 * (i + 1) + 20`;
                                                              ARITH_RULE `(16 * (i + 1) + 4) + 14 = 16 * (i + 1) + 18`;
                                                              ARITH_RULE `(16 * (i + 1) + 4) + 9 = 16 * (i + 1) + 13`;
                                                              ARITH_RULE `(16 * (i + 1) + 4) + 1 = 16 * (i + 1) + 5`] THEN
                                                CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                SUBGOAL_THEN
                                                 `!j. j < 16 + 16 * (i + 1) + 4 ==>
                                                      EL j (sha512_message_schedule (16 * (i + 1) + 4) (M_i:int64 list)) =
                                                      EL j (sha512_message_schedule 64 M_i)`
                                                MP_TAC THENL
                                                 [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                  MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                  UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 4` THEN ARITH_TAC;
                                                  ALL_TAC] THEN
                                                DISCH_THEN(fun th ->
                                                  MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                    [`16 * (i + 1) + 4:num`; `16 * (i + 1) + 5`;
                                                     `16 * (i + 1) + 13`; `16 * (i + 1) + 18`]) THEN
                                                REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                ASM_REWRITE_TAC[] THEN
                                                REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                              (* ----- BODY round 5 at rotation k=5: pc+0x320..pc+0x398 ----- *)
                                              ENSURES_SEQUENCE_TAC `pc + 0x398`
                                                `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                     read SP s = stackpointer /\
                                                     read X29 s = state_ptr /\
                                                     read X30 s = word (3 - i) /\
                                                     read X3 s = word_add kptr (word (64 * (i + 1) + 24)) /\
                                                     read X6 s = (EL 0 (sha512_compress (16 * (i + 1) + 6) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X7 s = (EL 1 (sha512_compress (16 * (i + 1) + 6) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X8 s = (EL 2 (sha512_compress (16 * (i + 1) + 6) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X9 s = (EL 3 (sha512_compress (16 * (i + 1) + 6) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X10 s = (EL 4 (sha512_compress (16 * (i + 1) + 6) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X11 s = (EL 5 (sha512_compress (16 * (i + 1) + 6) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X4 s = (EL 6 (sha512_compress (16 * (i + 1) + 6) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X5 s = (EL 7 (sha512_compress (16 * (i + 1) + 6) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                     read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                     read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                     read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                     read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                     read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                     read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                     read X25 s = EL (16 * (i + 1) + 6) (W:int64 list) /\
                                                     read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                                     read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                                     read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                                     read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                                     read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                     read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                     read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                     read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                     read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                     read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                     read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                               [
                                                (* BODY round 5: rotation k=5, WT=X24 WT1=X25 WT9=X16 WT14=X22 *)
                                                ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 6 = (16 * (i + 1) + 5) + 1`] THEN
                                                REWRITE_TAC[sha512_compress] THEN
                                                SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 20)):int64 =
                                                              word_add kptr (word (4 * (16 * (i + 1) + 5)))` SUBST_ALL_TAC THENL
                                                 [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                ENSURES_INIT_TAC "s0" THEN
                                                SUBGOAL_THEN
                                                   `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 5))))) s0 =
                                                    EL (16 * (i + 1) + 5) sha512_K`
                                                ASSUME_TAC THENL
                                                 [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 5:num`) THEN
                                                  ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                  DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                            sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                MP_TAC(SPECL [`16 * (i + 1) + 5:num`;
                                                              `W:int64 list`;
                                                              `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                             LIST_8_COMPRESS_NOHW3_64) THEN
                                                ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                DISCH_THEN(X_CHOOSE_THEN `a_bk5:int64`
                                                  (X_CHOOSE_THEN `b_bk5:int64` (X_CHOOSE_THEN `c_bk5:int64`
                                                  (X_CHOOSE_THEN `d_bk5:int64` (X_CHOOSE_THEN `e_bk5:int64`
                                                  (X_CHOOSE_THEN `f_bk5:int64` (X_CHOOSE_THEN `g_bk5:int64`
                                                  (X_CHOOSE_THEN `h_bk5:int64` ASSUME_TAC)))))))) THEN
                                                ASM_REWRITE_TAC[] THEN
                                                CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                         WORD_ZX_TRIVIAL] THEN
                                                REWRITE_TAC[EQ_REFL] THEN
                                                REWRITE_TAC[ADD_CLAUSES] THEN
                                                REPEAT CONJ_TAC THENL
                                                 [CONV_TAC WORD_RULE;
                                                  CONV_TAC WORD_RULE;
                                                  CONV_TAC WORD_RULE;
                                                  MP_TAC(SPECL [`16 * (i + 1) + 5:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                  ANTS_TAC THENL
                                                   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                    REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 5) + 16 = 16 * (i + 1) + 21`;
                                                                ARITH_RULE `(16 * (i + 1) + 5) + 14 = 16 * (i + 1) + 19`;
                                                                ARITH_RULE `(16 * (i + 1) + 5) + 9 = 16 * (i + 1) + 14`;
                                                                ARITH_RULE `(16 * (i + 1) + 5) + 1 = 16 * (i + 1) + 6`] THEN
                                                  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                  SUBGOAL_THEN
                                                   `!j. j < 16 + 16 * (i + 1) + 5 ==>
                                                        EL j (sha512_message_schedule (16 * (i + 1) + 5) (M_i:int64 list)) =
                                                        EL j (sha512_message_schedule 64 M_i)`
                                                  MP_TAC THENL
                                                   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                    MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                    UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 5` THEN ARITH_TAC;
                                                    ALL_TAC] THEN
                                                  DISCH_THEN(fun th ->
                                                    MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                      [`16 * (i + 1) + 5:num`; `16 * (i + 1) + 6`;
                                                       `16 * (i + 1) + 14`; `16 * (i + 1) + 19`]) THEN
                                                  REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                  ASM_REWRITE_TAC[] THEN
                                                  REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                  DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                (* ----- BODY round 6 at rotation k=6: pc+0x398..pc+0x410 ----- *)
                                                ENSURES_SEQUENCE_TAC `pc + 0x410`
                                                  `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                       read SP s = stackpointer /\
                                                       read X29 s = state_ptr /\
                                                       read X30 s = word (3 - i) /\
                                                       read X3 s = word_add kptr (word (64 * (i + 1) + 28)) /\
                                                       read X5 s = (EL 0 (sha512_compress (16 * (i + 1) + 7) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X6 s = (EL 1 (sha512_compress (16 * (i + 1) + 7) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X7 s = (EL 2 (sha512_compress (16 * (i + 1) + 7) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X8 s = (EL 3 (sha512_compress (16 * (i + 1) + 7) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X9 s = (EL 4 (sha512_compress (16 * (i + 1) + 7) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X10 s = (EL 5 (sha512_compress (16 * (i + 1) + 7) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X11 s = (EL 6 (sha512_compress (16 * (i + 1) + 7) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X4 s = (EL 7 (sha512_compress (16 * (i + 1) + 7) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                       read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                       read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                       read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                       read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                       read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                       read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                       read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                       read X26 s = EL (16 * (i + 1) + 7) (W:int64 list) /\
                                                       read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                                       read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                                       read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                                       read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                       read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                       read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                       read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                       read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                       read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                       read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                 [
                                                  (* BODY round 6: rotation k=6, WT=X25 WT1=X26 WT9=X17 WT14=X23 *)
                                                  ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 7 = (16 * (i + 1) + 6) + 1`] THEN
                                                  REWRITE_TAC[sha512_compress] THEN
                                                  SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 24)):int64 =
                                                                word_add kptr (word (4 * (16 * (i + 1) + 6)))` SUBST_ALL_TAC THENL
                                                   [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                  ENSURES_INIT_TAC "s0" THEN
                                                  SUBGOAL_THEN
                                                     `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 6))))) s0 =
                                                      EL (16 * (i + 1) + 6) sha512_K`
                                                  ASSUME_TAC THENL
                                                   [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 6:num`) THEN
                                                    ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                    DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                  ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                  REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                              sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                  MP_TAC(SPECL [`16 * (i + 1) + 6:num`;
                                                                `W:int64 list`;
                                                                `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                               LIST_8_COMPRESS_NOHW3_64) THEN
                                                  ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                  DISCH_THEN(X_CHOOSE_THEN `a_bk6:int64`
                                                    (X_CHOOSE_THEN `b_bk6:int64` (X_CHOOSE_THEN `c_bk6:int64`
                                                    (X_CHOOSE_THEN `d_bk6:int64` (X_CHOOSE_THEN `e_bk6:int64`
                                                    (X_CHOOSE_THEN `f_bk6:int64` (X_CHOOSE_THEN `g_bk6:int64`
                                                    (X_CHOOSE_THEN `h_bk6:int64` ASSUME_TAC)))))))) THEN
                                                  ASM_REWRITE_TAC[] THEN
                                                  CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                           WORD_ZX_TRIVIAL] THEN
                                                  REWRITE_TAC[EQ_REFL] THEN
                                                  REWRITE_TAC[ADD_CLAUSES] THEN
                                                  REPEAT CONJ_TAC THENL
                                                   [CONV_TAC WORD_RULE;
                                                    CONV_TAC WORD_RULE;
                                                    CONV_TAC WORD_RULE;
                                                    MP_TAC(SPECL [`16 * (i + 1) + 6:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                    ANTS_TAC THENL
                                                     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                      REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 6) + 16 = 16 * (i + 1) + 22`;
                                                                  ARITH_RULE `(16 * (i + 1) + 6) + 14 = 16 * (i + 1) + 20`;
                                                                  ARITH_RULE `(16 * (i + 1) + 6) + 9 = 16 * (i + 1) + 15`;
                                                                  ARITH_RULE `(16 * (i + 1) + 6) + 1 = 16 * (i + 1) + 7`] THEN
                                                    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                    SUBGOAL_THEN
                                                     `!j. j < 16 + 16 * (i + 1) + 6 ==>
                                                          EL j (sha512_message_schedule (16 * (i + 1) + 6) (M_i:int64 list)) =
                                                          EL j (sha512_message_schedule 64 M_i)`
                                                    MP_TAC THENL
                                                     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                      MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                      UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 6` THEN ARITH_TAC;
                                                      ALL_TAC] THEN
                                                    DISCH_THEN(fun th ->
                                                      MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                        [`16 * (i + 1) + 6:num`; `16 * (i + 1) + 7`;
                                                         `16 * (i + 1) + 15`; `16 * (i + 1) + 20`]) THEN
                                                    REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                    ASM_REWRITE_TAC[] THEN
                                                    REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                    DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                  (* ----- BODY round 7 at rotation k=7: pc+0x410..pc+0x488 ----- *)
                                                  ENSURES_SEQUENCE_TAC `pc + 0x488`
                                                    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                         read SP s = stackpointer /\
                                                         read X29 s = state_ptr /\
                                                         read X30 s = word (3 - i) /\
                                                         read X3 s = word_add kptr (word (64 * (i + 1) + 32)) /\
                                                         read X4 s = (EL 0 (sha512_compress (16 * (i + 1) + 8) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X5 s = (EL 1 (sha512_compress (16 * (i + 1) + 8) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X6 s = (EL 2 (sha512_compress (16 * (i + 1) + 8) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X7 s = (EL 3 (sha512_compress (16 * (i + 1) + 8) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X8 s = (EL 4 (sha512_compress (16 * (i + 1) + 8) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X9 s = (EL 5 (sha512_compress (16 * (i + 1) + 8) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X10 s = (EL 6 (sha512_compress (16 * (i + 1) + 8) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X11 s = (EL 7 (sha512_compress (16 * (i + 1) + 8) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                         read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                         read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                         read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                         read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                         read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                         read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                         read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                         read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                         read X27 s = EL (16 * (i + 1) + 8) (W:int64 list) /\
                                                         read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                                         read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                                         read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                         read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                         read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                         read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                         read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                         read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                         read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                   [
                                                    (* BODY round 7: rotation k=7, WT=X26 WT1=X27 WT9=X19 WT14=X24 *)
                                                    ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 8 = (16 * (i + 1) + 7) + 1`] THEN
                                                    REWRITE_TAC[sha512_compress] THEN
                                                    SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 28)):int64 =
                                                                  word_add kptr (word (4 * (16 * (i + 1) + 7)))` SUBST_ALL_TAC THENL
                                                     [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                    ENSURES_INIT_TAC "s0" THEN
                                                    SUBGOAL_THEN
                                                       `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 7))))) s0 =
                                                        EL (16 * (i + 1) + 7) sha512_K`
                                                    ASSUME_TAC THENL
                                                     [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 7:num`) THEN
                                                      ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                      DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                    ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                    REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                    MP_TAC(SPECL [`16 * (i + 1) + 7:num`;
                                                                  `W:int64 list`;
                                                                  `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                 LIST_8_COMPRESS_NOHW3_64) THEN
                                                    ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                    DISCH_THEN(X_CHOOSE_THEN `a_bk7:int64`
                                                      (X_CHOOSE_THEN `b_bk7:int64` (X_CHOOSE_THEN `c_bk7:int64`
                                                      (X_CHOOSE_THEN `d_bk7:int64` (X_CHOOSE_THEN `e_bk7:int64`
                                                      (X_CHOOSE_THEN `f_bk7:int64` (X_CHOOSE_THEN `g_bk7:int64`
                                                      (X_CHOOSE_THEN `h_bk7:int64` ASSUME_TAC)))))))) THEN
                                                    ASM_REWRITE_TAC[] THEN
                                                    CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                             WORD_ZX_TRIVIAL] THEN
                                                    REWRITE_TAC[EQ_REFL] THEN
                                                    REWRITE_TAC[ADD_CLAUSES] THEN
                                                    REPEAT CONJ_TAC THENL
                                                     [CONV_TAC WORD_RULE;
                                                      CONV_TAC WORD_RULE;
                                                      CONV_TAC WORD_RULE;
                                                      MP_TAC(SPECL [`16 * (i + 1) + 7:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                      ANTS_TAC THENL
                                                       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                        REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 7) + 16 = 16 * (i + 1) + 23`;
                                                                    ARITH_RULE `(16 * (i + 1) + 7) + 14 = 16 * (i + 1) + 21`;
                                                                    ARITH_RULE `(16 * (i + 1) + 7) + 9 = 16 * (i + 1) + 16`;
                                                                    ARITH_RULE `(16 * (i + 1) + 7) + 1 = 16 * (i + 1) + 8`] THEN
                                                      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                      SUBGOAL_THEN
                                                       `!j. j < 16 + 16 * (i + 1) + 7 ==>
                                                            EL j (sha512_message_schedule (16 * (i + 1) + 7) (M_i:int64 list)) =
                                                            EL j (sha512_message_schedule 64 M_i)`
                                                      MP_TAC THENL
                                                       [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                        MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                        UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 7` THEN ARITH_TAC;
                                                        ALL_TAC] THEN
                                                      DISCH_THEN(fun th ->
                                                        MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                          [`16 * (i + 1) + 7:num`; `16 * (i + 1) + 8`;
                                                           `16 * (i + 1) + 16`; `16 * (i + 1) + 21`]) THEN
                                                      REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                      ASM_REWRITE_TAC[] THEN
                                                      REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                      DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                    (* ----- BODY round 8 at rotation k=0: pc+0x488..pc+0x500 ----- *)
                                                    ENSURES_SEQUENCE_TAC `pc + 0x500`
                                                      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                           read SP s = stackpointer /\
                                                           read X29 s = state_ptr /\
                                                           read X30 s = word (3 - i) /\
                                                           read X3 s = word_add kptr (word (64 * (i + 1) + 36)) /\
                                                           read X11 s = (EL 0 (sha512_compress (16 * (i + 1) + 9) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X4 s = (EL 1 (sha512_compress (16 * (i + 1) + 9) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X5 s = (EL 2 (sha512_compress (16 * (i + 1) + 9) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X6 s = (EL 3 (sha512_compress (16 * (i + 1) + 9) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X7 s = (EL 4 (sha512_compress (16 * (i + 1) + 9) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X8 s = (EL 5 (sha512_compress (16 * (i + 1) + 9) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X9 s = (EL 6 (sha512_compress (16 * (i + 1) + 9) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X10 s = (EL 7 (sha512_compress (16 * (i + 1) + 9) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                           read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                           read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                           read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                           read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                           read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                           read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                           read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                           read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                           read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                           read X28 s = EL (16 * (i + 1) + 9) (W:int64 list) /\
                                                           read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                                           read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                           read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                           read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                           read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                           read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                           read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                           read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                     [
                                                      (* BODY round 8: rotation k=0, WT=X27 WT1=X28 WT9=X20 WT14=X25 *)
                                                      ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 9 = (16 * (i + 1) + 8) + 1`] THEN
                                                      REWRITE_TAC[sha512_compress] THEN
                                                      SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 32)):int64 =
                                                                    word_add kptr (word (4 * (16 * (i + 1) + 8)))` SUBST_ALL_TAC THENL
                                                       [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                      ENSURES_INIT_TAC "s0" THEN
                                                      SUBGOAL_THEN
                                                         `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 8))))) s0 =
                                                          EL (16 * (i + 1) + 8) sha512_K`
                                                      ASSUME_TAC THENL
                                                       [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 8:num`) THEN
                                                        ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                        DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                      ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                      REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                  sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                      MP_TAC(SPECL [`16 * (i + 1) + 8:num`;
                                                                    `W:int64 list`;
                                                                    `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                   LIST_8_COMPRESS_NOHW3_64) THEN
                                                      ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                      DISCH_THEN(X_CHOOSE_THEN `a_bk8:int64`
                                                        (X_CHOOSE_THEN `b_bk8:int64` (X_CHOOSE_THEN `c_bk8:int64`
                                                        (X_CHOOSE_THEN `d_bk8:int64` (X_CHOOSE_THEN `e_bk8:int64`
                                                        (X_CHOOSE_THEN `f_bk8:int64` (X_CHOOSE_THEN `g_bk8:int64`
                                                        (X_CHOOSE_THEN `h_bk8:int64` ASSUME_TAC)))))))) THEN
                                                      ASM_REWRITE_TAC[] THEN
                                                      CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                      SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                               WORD_ZX_TRIVIAL] THEN
                                                      REWRITE_TAC[EQ_REFL] THEN
                                                      REWRITE_TAC[ADD_CLAUSES] THEN
                                                      REPEAT CONJ_TAC THENL
                                                       [CONV_TAC WORD_RULE;
                                                        CONV_TAC WORD_RULE;
                                                        CONV_TAC WORD_RULE;
                                                        MP_TAC(SPECL [`16 * (i + 1) + 8:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                        ANTS_TAC THENL
                                                         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                          REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 8) + 16 = 16 * (i + 1) + 24`;
                                                                      ARITH_RULE `(16 * (i + 1) + 8) + 14 = 16 * (i + 1) + 22`;
                                                                      ARITH_RULE `(16 * (i + 1) + 8) + 9 = 16 * (i + 1) + 17`;
                                                                      ARITH_RULE `(16 * (i + 1) + 8) + 1 = 16 * (i + 1) + 9`] THEN
                                                        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                        SUBGOAL_THEN
                                                         `!j. j < 16 + 16 * (i + 1) + 8 ==>
                                                              EL j (sha512_message_schedule (16 * (i + 1) + 8) (M_i:int64 list)) =
                                                              EL j (sha512_message_schedule 64 M_i)`
                                                        MP_TAC THENL
                                                         [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                          MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                          UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 8` THEN ARITH_TAC;
                                                          ALL_TAC] THEN
                                                        DISCH_THEN(fun th ->
                                                          MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                            [`16 * (i + 1) + 8:num`; `16 * (i + 1) + 9`;
                                                             `16 * (i + 1) + 17`; `16 * (i + 1) + 22`]) THEN
                                                        REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                        ASM_REWRITE_TAC[] THEN
                                                        REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                        DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                      (* ----- BODY round 9 at rotation k=1: pc+0x500..pc+0x578 ----- *)
                                                      ENSURES_SEQUENCE_TAC `pc + 0x578`
                                                        `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                             read SP s = stackpointer /\
                                                             read X29 s = state_ptr /\
                                                             read X30 s = word (3 - i) /\
                                                             read X3 s = word_add kptr (word (64 * (i + 1) + 40)) /\
                                                             read X10 s = (EL 0 (sha512_compress (16 * (i + 1) + 10) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X11 s = (EL 1 (sha512_compress (16 * (i + 1) + 10) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X4 s = (EL 2 (sha512_compress (16 * (i + 1) + 10) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X5 s = (EL 3 (sha512_compress (16 * (i + 1) + 10) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X6 s = (EL 4 (sha512_compress (16 * (i + 1) + 10) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X7 s = (EL 5 (sha512_compress (16 * (i + 1) + 10) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X8 s = (EL 6 (sha512_compress (16 * (i + 1) + 10) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X9 s = (EL 7 (sha512_compress (16 * (i + 1) + 10) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                             read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                             read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                             read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                             read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                             read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                             read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                             read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                             read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                             read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                             read X28 s = EL (16 * (i + 1) + 25) (W:int64 list) /\
                                                             read X12 s = EL (16 * (i + 1) + 10) (W:int64 list) /\
                                                             read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                             read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                             read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                             read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                             read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                             read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                             read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                       [
                                                        (* BODY round 9: rotation k=1, WT=X28 WT1=X12 WT9=X21 WT14=X26 *)
                                                        ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 10 = (16 * (i + 1) + 9) + 1`] THEN
                                                        REWRITE_TAC[sha512_compress] THEN
                                                        SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 36)):int64 =
                                                                      word_add kptr (word (4 * (16 * (i + 1) + 9)))` SUBST_ALL_TAC THENL
                                                         [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                        ENSURES_INIT_TAC "s0" THEN
                                                        SUBGOAL_THEN
                                                           `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 9))))) s0 =
                                                            EL (16 * (i + 1) + 9) sha512_K`
                                                        ASSUME_TAC THENL
                                                         [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 9:num`) THEN
                                                          ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                          DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                        ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                        REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                    sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                        SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                        MP_TAC(SPECL [`16 * (i + 1) + 9:num`;
                                                                      `W:int64 list`;
                                                                      `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                     LIST_8_COMPRESS_NOHW3_64) THEN
                                                        ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                        DISCH_THEN(X_CHOOSE_THEN `a_bk9:int64`
                                                          (X_CHOOSE_THEN `b_bk9:int64` (X_CHOOSE_THEN `c_bk9:int64`
                                                          (X_CHOOSE_THEN `d_bk9:int64` (X_CHOOSE_THEN `e_bk9:int64`
                                                          (X_CHOOSE_THEN `f_bk9:int64` (X_CHOOSE_THEN `g_bk9:int64`
                                                          (X_CHOOSE_THEN `h_bk9:int64` ASSUME_TAC)))))))) THEN
                                                        ASM_REWRITE_TAC[] THEN
                                                        CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                        SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                                 WORD_ZX_TRIVIAL] THEN
                                                        REWRITE_TAC[EQ_REFL] THEN
                                                        REWRITE_TAC[ADD_CLAUSES] THEN
                                                        REPEAT CONJ_TAC THENL
                                                         [CONV_TAC WORD_RULE;
                                                          CONV_TAC WORD_RULE;
                                                          CONV_TAC WORD_RULE;
                                                          MP_TAC(SPECL [`16 * (i + 1) + 9:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                          ANTS_TAC THENL
                                                           [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                            REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 9) + 16 = 16 * (i + 1) + 25`;
                                                                        ARITH_RULE `(16 * (i + 1) + 9) + 14 = 16 * (i + 1) + 23`;
                                                                        ARITH_RULE `(16 * (i + 1) + 9) + 9 = 16 * (i + 1) + 18`;
                                                                        ARITH_RULE `(16 * (i + 1) + 9) + 1 = 16 * (i + 1) + 10`] THEN
                                                          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                          SUBGOAL_THEN
                                                           `!j. j < 16 + 16 * (i + 1) + 9 ==>
                                                                EL j (sha512_message_schedule (16 * (i + 1) + 9) (M_i:int64 list)) =
                                                                EL j (sha512_message_schedule 64 M_i)`
                                                          MP_TAC THENL
                                                           [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                            MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                            UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 9` THEN ARITH_TAC;
                                                            ALL_TAC] THEN
                                                          DISCH_THEN(fun th ->
                                                            MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                              [`16 * (i + 1) + 9:num`; `16 * (i + 1) + 10`;
                                                               `16 * (i + 1) + 18`; `16 * (i + 1) + 23`]) THEN
                                                          REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                          ASM_REWRITE_TAC[] THEN
                                                          REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                          DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                        (* ----- BODY round 10 at rotation k=2: pc+0x578..pc+0x5f0 ----- *)
                                                        ENSURES_SEQUENCE_TAC `pc + 0x5f0`
                                                          `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                               read SP s = stackpointer /\
                                                               read X29 s = state_ptr /\
                                                               read X30 s = word (3 - i) /\
                                                               read X3 s = word_add kptr (word (64 * (i + 1) + 44)) /\
                                                               read X9 s = (EL 0 (sha512_compress (16 * (i + 1) + 11) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X10 s = (EL 1 (sha512_compress (16 * (i + 1) + 11) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X11 s = (EL 2 (sha512_compress (16 * (i + 1) + 11) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X4 s = (EL 3 (sha512_compress (16 * (i + 1) + 11) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X5 s = (EL 4 (sha512_compress (16 * (i + 1) + 11) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X6 s = (EL 5 (sha512_compress (16 * (i + 1) + 11) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X7 s = (EL 6 (sha512_compress (16 * (i + 1) + 11) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X8 s = (EL 7 (sha512_compress (16 * (i + 1) + 11) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                               read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                               read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                               read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                               read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                               read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                               read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                               read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                               read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                               read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                               read X28 s = EL (16 * (i + 1) + 25) (W:int64 list) /\
                                                               read X12 s = EL (16 * (i + 1) + 26) (W:int64 list) /\
                                                               read X13 s = EL (16 * (i + 1) + 11) (W:int64 list) /\
                                                               read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                               read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                               read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                               read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                               read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                               read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                         [
                                                          (* BODY round 10: rotation k=2, WT=X12 WT1=X13 WT9=X22 WT14=X27 *)
                                                          ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 11 = (16 * (i + 1) + 10) + 1`] THEN
                                                          REWRITE_TAC[sha512_compress] THEN
                                                          SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 40)):int64 =
                                                                        word_add kptr (word (4 * (16 * (i + 1) + 10)))` SUBST_ALL_TAC THENL
                                                           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                          ENSURES_INIT_TAC "s0" THEN
                                                          SUBGOAL_THEN
                                                             `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 10))))) s0 =
                                                              EL (16 * (i + 1) + 10) sha512_K`
                                                          ASSUME_TAC THENL
                                                           [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 10:num`) THEN
                                                            ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                          ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                          MP_TAC(SPECL [`16 * (i + 1) + 10:num`;
                                                                        `W:int64 list`;
                                                                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                       LIST_8_COMPRESS_NOHW3_64) THEN
                                                          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                          DISCH_THEN(X_CHOOSE_THEN `a_bk10:int64`
                                                            (X_CHOOSE_THEN `b_bk10:int64` (X_CHOOSE_THEN `c_bk10:int64`
                                                            (X_CHOOSE_THEN `d_bk10:int64` (X_CHOOSE_THEN `e_bk10:int64`
                                                            (X_CHOOSE_THEN `f_bk10:int64` (X_CHOOSE_THEN `g_bk10:int64`
                                                            (X_CHOOSE_THEN `h_bk10:int64` ASSUME_TAC)))))))) THEN
                                                          ASM_REWRITE_TAC[] THEN
                                                          CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                                   WORD_ZX_TRIVIAL] THEN
                                                          REWRITE_TAC[EQ_REFL] THEN
                                                          REWRITE_TAC[ADD_CLAUSES] THEN
                                                          REPEAT CONJ_TAC THENL
                                                           [CONV_TAC WORD_RULE;
                                                            CONV_TAC WORD_RULE;
                                                            CONV_TAC WORD_RULE;
                                                            MP_TAC(SPECL [`16 * (i + 1) + 10:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                            ANTS_TAC THENL
                                                             [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                              REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 10) + 16 = 16 * (i + 1) + 26`;
                                                                          ARITH_RULE `(16 * (i + 1) + 10) + 14 = 16 * (i + 1) + 24`;
                                                                          ARITH_RULE `(16 * (i + 1) + 10) + 9 = 16 * (i + 1) + 19`;
                                                                          ARITH_RULE `(16 * (i + 1) + 10) + 1 = 16 * (i + 1) + 11`] THEN
                                                            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                            SUBGOAL_THEN
                                                             `!j. j < 16 + 16 * (i + 1) + 10 ==>
                                                                  EL j (sha512_message_schedule (16 * (i + 1) + 10) (M_i:int64 list)) =
                                                                  EL j (sha512_message_schedule 64 M_i)`
                                                            MP_TAC THENL
                                                             [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                              MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                              UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 10` THEN ARITH_TAC;
                                                              ALL_TAC] THEN
                                                            DISCH_THEN(fun th ->
                                                              MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                                [`16 * (i + 1) + 10:num`; `16 * (i + 1) + 11`;
                                                                 `16 * (i + 1) + 19`; `16 * (i + 1) + 24`]) THEN
                                                            REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                            ASM_REWRITE_TAC[] THEN
                                                            REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                            DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                          (* ----- BODY round 11 at rotation k=3: pc+0x5f0..pc+0x668 ----- *)
                                                          ENSURES_SEQUENCE_TAC `pc + 0x668`
                                                            `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                                 read SP s = stackpointer /\
                                                                 read X29 s = state_ptr /\
                                                                 read X30 s = word (3 - i) /\
                                                                 read X3 s = word_add kptr (word (64 * (i + 1) + 48)) /\
                                                                 read X8 s = (EL 0 (sha512_compress (16 * (i + 1) + 12) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X9 s = (EL 1 (sha512_compress (16 * (i + 1) + 12) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X10 s = (EL 2 (sha512_compress (16 * (i + 1) + 12) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X11 s = (EL 3 (sha512_compress (16 * (i + 1) + 12) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X4 s = (EL 4 (sha512_compress (16 * (i + 1) + 12) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X5 s = (EL 5 (sha512_compress (16 * (i + 1) + 12) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X6 s = (EL 6 (sha512_compress (16 * (i + 1) + 12) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X7 s = (EL 7 (sha512_compress (16 * (i + 1) + 12) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                 read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                                 read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                                 read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                                 read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                                 read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                                 read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                                 read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                                 read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                                 read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                                 read X28 s = EL (16 * (i + 1) + 25) (W:int64 list) /\
                                                                 read X12 s = EL (16 * (i + 1) + 26) (W:int64 list) /\
                                                                 read X13 s = EL (16 * (i + 1) + 27) (W:int64 list) /\
                                                                 read X14 s = EL (16 * (i + 1) + 12) (W:int64 list) /\
                                                                 read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                                 read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                                 read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                                 read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                                 read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                           [
                                                            (* BODY round 11: rotation k=3, WT=X13 WT1=X14 WT9=X23 WT14=X28 *)
                                                            ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 12 = (16 * (i + 1) + 11) + 1`] THEN
                                                            REWRITE_TAC[sha512_compress] THEN
                                                            SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 44)):int64 =
                                                                          word_add kptr (word (4 * (16 * (i + 1) + 11)))` SUBST_ALL_TAC THENL
                                                             [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                            ENSURES_INIT_TAC "s0" THEN
                                                            SUBGOAL_THEN
                                                               `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 11))))) s0 =
                                                                EL (16 * (i + 1) + 11) sha512_K`
                                                            ASSUME_TAC THENL
                                                             [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 11:num`) THEN
                                                              ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                              DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                            ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                            ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                            REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                        sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                            SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                            MP_TAC(SPECL [`16 * (i + 1) + 11:num`;
                                                                          `W:int64 list`;
                                                                          `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                         LIST_8_COMPRESS_NOHW3_64) THEN
                                                            ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                            DISCH_THEN(X_CHOOSE_THEN `a_bk11:int64`
                                                              (X_CHOOSE_THEN `b_bk11:int64` (X_CHOOSE_THEN `c_bk11:int64`
                                                              (X_CHOOSE_THEN `d_bk11:int64` (X_CHOOSE_THEN `e_bk11:int64`
                                                              (X_CHOOSE_THEN `f_bk11:int64` (X_CHOOSE_THEN `g_bk11:int64`
                                                              (X_CHOOSE_THEN `h_bk11:int64` ASSUME_TAC)))))))) THEN
                                                            ASM_REWRITE_TAC[] THEN
                                                            CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                            SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                                     WORD_ZX_TRIVIAL] THEN
                                                            REWRITE_TAC[EQ_REFL] THEN
                                                            REWRITE_TAC[ADD_CLAUSES] THEN
                                                            REPEAT CONJ_TAC THENL
                                                             [CONV_TAC WORD_RULE;
                                                              CONV_TAC WORD_RULE;
                                                              CONV_TAC WORD_RULE;
                                                              MP_TAC(SPECL [`16 * (i + 1) + 11:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                              ANTS_TAC THENL
                                                               [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 11) + 16 = 16 * (i + 1) + 27`;
                                                                            ARITH_RULE `(16 * (i + 1) + 11) + 14 = 16 * (i + 1) + 25`;
                                                                            ARITH_RULE `(16 * (i + 1) + 11) + 9 = 16 * (i + 1) + 20`;
                                                                            ARITH_RULE `(16 * (i + 1) + 11) + 1 = 16 * (i + 1) + 12`] THEN
                                                              CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                              SUBGOAL_THEN
                                                               `!j. j < 16 + 16 * (i + 1) + 11 ==>
                                                                    EL j (sha512_message_schedule (16 * (i + 1) + 11) (M_i:int64 list)) =
                                                                    EL j (sha512_message_schedule 64 M_i)`
                                                              MP_TAC THENL
                                                               [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                                MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                                UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 11` THEN ARITH_TAC;
                                                                ALL_TAC] THEN
                                                              DISCH_THEN(fun th ->
                                                                MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                                  [`16 * (i + 1) + 11:num`; `16 * (i + 1) + 12`;
                                                                   `16 * (i + 1) + 20`; `16 * (i + 1) + 25`]) THEN
                                                              REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                              ASM_REWRITE_TAC[] THEN
                                                              REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                              DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                            (* ----- BODY round 12 at rotation k=4: pc+0x668..pc+0x6e0 ----- *)
                                                            ENSURES_SEQUENCE_TAC `pc + 0x6e0`
                                                              `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                                   read SP s = stackpointer /\
                                                                   read X29 s = state_ptr /\
                                                                   read X30 s = word (3 - i) /\
                                                                   read X3 s = word_add kptr (word (64 * (i + 1) + 52)) /\
                                                                   read X7 s = (EL 0 (sha512_compress (16 * (i + 1) + 13) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X8 s = (EL 1 (sha512_compress (16 * (i + 1) + 13) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X9 s = (EL 2 (sha512_compress (16 * (i + 1) + 13) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X10 s = (EL 3 (sha512_compress (16 * (i + 1) + 13) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X11 s = (EL 4 (sha512_compress (16 * (i + 1) + 13) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X4 s = (EL 5 (sha512_compress (16 * (i + 1) + 13) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X5 s = (EL 6 (sha512_compress (16 * (i + 1) + 13) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X6 s = (EL 7 (sha512_compress (16 * (i + 1) + 13) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                   read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                                   read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                                   read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                                   read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                                   read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                                   read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                                   read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                                   read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                                   read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                                   read X28 s = EL (16 * (i + 1) + 25) (W:int64 list) /\
                                                                   read X12 s = EL (16 * (i + 1) + 26) (W:int64 list) /\
                                                                   read X13 s = EL (16 * (i + 1) + 27) (W:int64 list) /\
                                                                   read X14 s = EL (16 * (i + 1) + 28) (W:int64 list) /\
                                                                   read X15 s = EL (16 * (i + 1) + 13) (W:int64 list) /\
                                                                   read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                                   read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                                   read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                                   read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                             [
                                                              (* BODY round 12: rotation k=4, WT=X14 WT1=X15 WT9=X24 WT14=X12 *)
                                                              ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 13 = (16 * (i + 1) + 12) + 1`] THEN
                                                              REWRITE_TAC[sha512_compress] THEN
                                                              SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 48)):int64 =
                                                                            word_add kptr (word (4 * (16 * (i + 1) + 12)))` SUBST_ALL_TAC THENL
                                                               [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                              ENSURES_INIT_TAC "s0" THEN
                                                              SUBGOAL_THEN
                                                                 `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 12))))) s0 =
                                                                  EL (16 * (i + 1) + 12) sha512_K`
                                                              ASSUME_TAC THENL
                                                               [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 12:num`) THEN
                                                                ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                              ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                              ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                              REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                          sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                              SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                              MP_TAC(SPECL [`16 * (i + 1) + 12:num`;
                                                                            `W:int64 list`;
                                                                            `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                           LIST_8_COMPRESS_NOHW3_64) THEN
                                                              ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                              DISCH_THEN(X_CHOOSE_THEN `a_bk12:int64`
                                                                (X_CHOOSE_THEN `b_bk12:int64` (X_CHOOSE_THEN `c_bk12:int64`
                                                                (X_CHOOSE_THEN `d_bk12:int64` (X_CHOOSE_THEN `e_bk12:int64`
                                                                (X_CHOOSE_THEN `f_bk12:int64` (X_CHOOSE_THEN `g_bk12:int64`
                                                                (X_CHOOSE_THEN `h_bk12:int64` ASSUME_TAC)))))))) THEN
                                                              ASM_REWRITE_TAC[] THEN
                                                              CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                              SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                                       WORD_ZX_TRIVIAL] THEN
                                                              REWRITE_TAC[EQ_REFL] THEN
                                                              REWRITE_TAC[ADD_CLAUSES] THEN
                                                              REPEAT CONJ_TAC THENL
                                                               [CONV_TAC WORD_RULE;
                                                                CONV_TAC WORD_RULE;
                                                                CONV_TAC WORD_RULE;
                                                                MP_TAC(SPECL [`16 * (i + 1) + 12:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                                ANTS_TAC THENL
                                                                 [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                  REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 12) + 16 = 16 * (i + 1) + 28`;
                                                                              ARITH_RULE `(16 * (i + 1) + 12) + 14 = 16 * (i + 1) + 26`;
                                                                              ARITH_RULE `(16 * (i + 1) + 12) + 9 = 16 * (i + 1) + 21`;
                                                                              ARITH_RULE `(16 * (i + 1) + 12) + 1 = 16 * (i + 1) + 13`] THEN
                                                                CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                                SUBGOAL_THEN
                                                                 `!j. j < 16 + 16 * (i + 1) + 12 ==>
                                                                      EL j (sha512_message_schedule (16 * (i + 1) + 12) (M_i:int64 list)) =
                                                                      EL j (sha512_message_schedule 64 M_i)`
                                                                MP_TAC THENL
                                                                 [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                                  MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                                  UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 12` THEN ARITH_TAC;
                                                                  ALL_TAC] THEN
                                                                DISCH_THEN(fun th ->
                                                                  MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                                    [`16 * (i + 1) + 12:num`; `16 * (i + 1) + 13`;
                                                                     `16 * (i + 1) + 21`; `16 * (i + 1) + 26`]) THEN
                                                                REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                                ASM_REWRITE_TAC[] THEN
                                                                REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                                DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                              (* ----- BODY round 13 at rotation k=5: pc+0x6e0..pc+0x758 ----- *)
                                                              ENSURES_SEQUENCE_TAC `pc + 0x758`
                                                                `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                                     read SP s = stackpointer /\
                                                                     read X29 s = state_ptr /\
                                                                     read X30 s = word (3 - i) /\
                                                                     read X3 s = word_add kptr (word (64 * (i + 1) + 56)) /\
                                                                     read X6 s = (EL 0 (sha512_compress (16 * (i + 1) + 14) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X7 s = (EL 1 (sha512_compress (16 * (i + 1) + 14) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X8 s = (EL 2 (sha512_compress (16 * (i + 1) + 14) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X9 s = (EL 3 (sha512_compress (16 * (i + 1) + 14) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X10 s = (EL 4 (sha512_compress (16 * (i + 1) + 14) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X11 s = (EL 5 (sha512_compress (16 * (i + 1) + 14) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X4 s = (EL 6 (sha512_compress (16 * (i + 1) + 14) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X5 s = (EL 7 (sha512_compress (16 * (i + 1) + 14) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                     read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                                     read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                                     read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                                     read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                                     read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                                     read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                                     read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                                     read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                                     read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                                     read X28 s = EL (16 * (i + 1) + 25) (W:int64 list) /\
                                                                     read X12 s = EL (16 * (i + 1) + 26) (W:int64 list) /\
                                                                     read X13 s = EL (16 * (i + 1) + 27) (W:int64 list) /\
                                                                     read X14 s = EL (16 * (i + 1) + 28) (W:int64 list) /\
                                                                     read X15 s = EL (16 * (i + 1) + 29) (W:int64 list) /\
                                                                     read X16 s = EL (16 * (i + 1) + 14) (W:int64 list) /\
                                                                     read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                                     read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                                     read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                               [
                                                                (* BODY round 13: rotation k=5, WT=X15 WT1=X16 WT9=X25 WT14=X13 *)
                                                                ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 14 = (16 * (i + 1) + 13) + 1`] THEN
                                                                REWRITE_TAC[sha512_compress] THEN
                                                                SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 52)):int64 =
                                                                              word_add kptr (word (4 * (16 * (i + 1) + 13)))` SUBST_ALL_TAC THENL
                                                                 [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                                ENSURES_INIT_TAC "s0" THEN
                                                                SUBGOAL_THEN
                                                                   `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 13))))) s0 =
                                                                    EL (16 * (i + 1) + 13) sha512_K`
                                                                ASSUME_TAC THENL
                                                                 [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 13:num`) THEN
                                                                  ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                  DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                                ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                                ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                                REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                            sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                                SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                                MP_TAC(SPECL [`16 * (i + 1) + 13:num`;
                                                                              `W:int64 list`;
                                                                              `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                             LIST_8_COMPRESS_NOHW3_64) THEN
                                                                ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                                DISCH_THEN(X_CHOOSE_THEN `a_bk13:int64`
                                                                  (X_CHOOSE_THEN `b_bk13:int64` (X_CHOOSE_THEN `c_bk13:int64`
                                                                  (X_CHOOSE_THEN `d_bk13:int64` (X_CHOOSE_THEN `e_bk13:int64`
                                                                  (X_CHOOSE_THEN `f_bk13:int64` (X_CHOOSE_THEN `g_bk13:int64`
                                                                  (X_CHOOSE_THEN `h_bk13:int64` ASSUME_TAC)))))))) THEN
                                                                ASM_REWRITE_TAC[] THEN
                                                                CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                                SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                                         WORD_ZX_TRIVIAL] THEN
                                                                REWRITE_TAC[EQ_REFL] THEN
                                                                REWRITE_TAC[ADD_CLAUSES] THEN
                                                                REPEAT CONJ_TAC THENL
                                                                 [CONV_TAC WORD_RULE;
                                                                  CONV_TAC WORD_RULE;
                                                                  CONV_TAC WORD_RULE;
                                                                  MP_TAC(SPECL [`16 * (i + 1) + 13:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                                  ANTS_TAC THENL
                                                                   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                    REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 13) + 16 = 16 * (i + 1) + 29`;
                                                                                ARITH_RULE `(16 * (i + 1) + 13) + 14 = 16 * (i + 1) + 27`;
                                                                                ARITH_RULE `(16 * (i + 1) + 13) + 9 = 16 * (i + 1) + 22`;
                                                                                ARITH_RULE `(16 * (i + 1) + 13) + 1 = 16 * (i + 1) + 14`] THEN
                                                                  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                                  SUBGOAL_THEN
                                                                   `!j. j < 16 + 16 * (i + 1) + 13 ==>
                                                                        EL j (sha512_message_schedule (16 * (i + 1) + 13) (M_i:int64 list)) =
                                                                        EL j (sha512_message_schedule 64 M_i)`
                                                                  MP_TAC THENL
                                                                   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                                    MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                                    UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 13` THEN ARITH_TAC;
                                                                    ALL_TAC] THEN
                                                                  DISCH_THEN(fun th ->
                                                                    MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                                      [`16 * (i + 1) + 13:num`; `16 * (i + 1) + 14`;
                                                                       `16 * (i + 1) + 22`; `16 * (i + 1) + 27`]) THEN
                                                                  REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                                  ASM_REWRITE_TAC[] THEN
                                                                  REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                                  DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                                (* ----- BODY round 14 at rotation k=6: pc+0x758..pc+0x7d0 ----- *)
                                                                ENSURES_SEQUENCE_TAC `pc + 0x7d0`
                                                                  `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                                       read SP s = stackpointer /\
                                                                       read X29 s = state_ptr /\
                                                                       read X30 s = word (3 - i) /\
                                                                       read X3 s = word_add kptr (word (64 * (i + 1) + 60)) /\
                                                                       read X5 s = (EL 0 (sha512_compress (16 * (i + 1) + 15) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X6 s = (EL 1 (sha512_compress (16 * (i + 1) + 15) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X7 s = (EL 2 (sha512_compress (16 * (i + 1) + 15) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X8 s = (EL 3 (sha512_compress (16 * (i + 1) + 15) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X9 s = (EL 4 (sha512_compress (16 * (i + 1) + 15) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X10 s = (EL 5 (sha512_compress (16 * (i + 1) + 15) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X11 s = (EL 6 (sha512_compress (16 * (i + 1) + 15) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X4 s = (EL 7 (sha512_compress (16 * (i + 1) + 15) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                       read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                                       read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                                       read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                                       read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                                       read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                                       read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                                       read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                                       read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                                       read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                                       read X28 s = EL (16 * (i + 1) + 25) (W:int64 list) /\
                                                                       read X12 s = EL (16 * (i + 1) + 26) (W:int64 list) /\
                                                                       read X13 s = EL (16 * (i + 1) + 27) (W:int64 list) /\
                                                                       read X14 s = EL (16 * (i + 1) + 28) (W:int64 list) /\
                                                                       read X15 s = EL (16 * (i + 1) + 29) (W:int64 list) /\
                                                                       read X16 s = EL (16 * (i + 1) + 30) (W:int64 list) /\
                                                                       read X17 s = EL (16 * (i + 1) + 15) (W:int64 list) /\
                                                                       read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                                       read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                                 [
                                                                  (* BODY round 14: rotation k=6, WT=X16 WT1=X17 WT9=X26 WT14=X14 *)
                                                                  ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 15 = (16 * (i + 1) + 14) + 1`] THEN
                                                                  REWRITE_TAC[sha512_compress] THEN
                                                                  SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 56)):int64 =
                                                                                word_add kptr (word (4 * (16 * (i + 1) + 14)))` SUBST_ALL_TAC THENL
                                                                   [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                                  ENSURES_INIT_TAC "s0" THEN
                                                                  SUBGOAL_THEN
                                                                     `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 14))))) s0 =
                                                                      EL (16 * (i + 1) + 14) sha512_K`
                                                                  ASSUME_TAC THENL
                                                                   [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 14:num`) THEN
                                                                    ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                    DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                                  ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                                  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                                  REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                              sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                                  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                                  MP_TAC(SPECL [`16 * (i + 1) + 14:num`;
                                                                                `W:int64 list`;
                                                                                `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                               LIST_8_COMPRESS_NOHW3_64) THEN
                                                                  ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                                  DISCH_THEN(X_CHOOSE_THEN `a_bk14:int64`
                                                                    (X_CHOOSE_THEN `b_bk14:int64` (X_CHOOSE_THEN `c_bk14:int64`
                                                                    (X_CHOOSE_THEN `d_bk14:int64` (X_CHOOSE_THEN `e_bk14:int64`
                                                                    (X_CHOOSE_THEN `f_bk14:int64` (X_CHOOSE_THEN `g_bk14:int64`
                                                                    (X_CHOOSE_THEN `h_bk14:int64` ASSUME_TAC)))))))) THEN
                                                                  ASM_REWRITE_TAC[] THEN
                                                                  CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                                  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                                           WORD_ZX_TRIVIAL] THEN
                                                                  REWRITE_TAC[EQ_REFL] THEN
                                                                  REWRITE_TAC[ADD_CLAUSES] THEN
                                                                  REPEAT CONJ_TAC THENL
                                                                   [CONV_TAC WORD_RULE;
                                                                    CONV_TAC WORD_RULE;
                                                                    CONV_TAC WORD_RULE;
                                                                    MP_TAC(SPECL [`16 * (i + 1) + 14:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                                    ANTS_TAC THENL
                                                                     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                      REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 14) + 16 = 16 * (i + 1) + 30`;
                                                                                  ARITH_RULE `(16 * (i + 1) + 14) + 14 = 16 * (i + 1) + 28`;
                                                                                  ARITH_RULE `(16 * (i + 1) + 14) + 9 = 16 * (i + 1) + 23`;
                                                                                  ARITH_RULE `(16 * (i + 1) + 14) + 1 = 16 * (i + 1) + 15`] THEN
                                                                    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                                    SUBGOAL_THEN
                                                                     `!j. j < 16 + 16 * (i + 1) + 14 ==>
                                                                          EL j (sha512_message_schedule (16 * (i + 1) + 14) (M_i:int64 list)) =
                                                                          EL j (sha512_message_schedule 64 M_i)`
                                                                    MP_TAC THENL
                                                                     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                                      MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                                      UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 14` THEN ARITH_TAC;
                                                                      ALL_TAC] THEN
                                                                    DISCH_THEN(fun th ->
                                                                      MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                                        [`16 * (i + 1) + 14:num`; `16 * (i + 1) + 15`;
                                                                         `16 * (i + 1) + 23`; `16 * (i + 1) + 28`]) THEN
                                                                    REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                                    ASM_REWRITE_TAC[] THEN
                                                                    REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                                    DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                                  (* ----- BODY round 15 at rotation k=7: pc+0x7d0..pc+0x848 ----- *)
                                                                  ENSURES_SEQUENCE_TAC `pc + 0x848`
                                                                    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
                                                                         read SP s = stackpointer /\
                                                                         read X29 s = state_ptr /\
                                                                         read X30 s = word (3 - i) /\
                                                                         read X3 s = word_add kptr (word (64 * (i + 1) + 64)) /\
                                                                         read X4 s = (EL 0 (sha512_compress (16 * (i + 1) + 16) W [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X5 s = (EL 1 (sha512_compress (16 * (i + 1) + 16) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X6 s = (EL 2 (sha512_compress (16 * (i + 1) + 16) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X7 s = (EL 3 (sha512_compress (16 * (i + 1) + 16) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X8 s = (EL 4 (sha512_compress (16 * (i + 1) + 16) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X9 s = (EL 5 (sha512_compress (16 * (i + 1) + 16) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X10 s = (EL 6 (sha512_compress (16 * (i + 1) + 16) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X11 s = (EL 7 (sha512_compress (16 * (i + 1) + 16) W [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
                                                                         read X19 s = EL (16 * (i + 1) + 16) (W:int64 list) /\
                                                                         read X20 s = EL (16 * (i + 1) + 17) (W:int64 list) /\
                                                                         read X21 s = EL (16 * (i + 1) + 18) (W:int64 list) /\
                                                                         read X22 s = EL (16 * (i + 1) + 19) (W:int64 list) /\
                                                                         read X23 s = EL (16 * (i + 1) + 20) (W:int64 list) /\
                                                                         read X24 s = EL (16 * (i + 1) + 21) (W:int64 list) /\
                                                                         read X25 s = EL (16 * (i + 1) + 22) (W:int64 list) /\
                                                                         read X26 s = EL (16 * (i + 1) + 23) (W:int64 list) /\
                                                                         read X27 s = EL (16 * (i + 1) + 24) (W:int64 list) /\
                                                                         read X28 s = EL (16 * (i + 1) + 25) (W:int64 list) /\
                                                                         read X12 s = EL (16 * (i + 1) + 26) (W:int64 list) /\
                                                                         read X13 s = EL (16 * (i + 1) + 27) (W:int64 list) /\
                                                                         read X14 s = EL (16 * (i + 1) + 28) (W:int64 list) /\
                                                                         read X15 s = EL (16 * (i + 1) + 29) (W:int64 list) /\
                                                                         read X16 s = EL (16 * (i + 1) + 30) (W:int64 list) /\
                                                                         read X17 s = EL (16 * (i + 1) + 31) (W:int64 list) /\
                                                                         read (memory :> bytes64 (word_add stackpointer (word 96))) s = dptr_i /\
                                                                         read (memory :> bytes64 (word_add stackpointer (word 104))) s = word(num_blocks - ii) /\
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
                                                                   [
                                                                    (* BODY round 15: rotation k=7, WT=X17 WT1=X19 WT9=X27 WT14=X15 *)
                                                                    ONCE_REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 16 = (16 * (i + 1) + 15) + 1`] THEN
                                                                    REWRITE_TAC[sha512_compress] THEN
                                                                    SUBGOAL_THEN `word_add kptr (word (64 * (i + 1) + 60)):int64 =
                                                                                  word_add kptr (word (4 * (16 * (i + 1) + 15)))` SUBST_ALL_TAC THENL
                                                                     [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
                                                                    ENSURES_INIT_TAC "s0" THEN
                                                                    SUBGOAL_THEN
                                                                       `read (memory :> bytes64 (word_add kptr (word (4 * (16 * (i + 1) + 15))))) s0 =
                                                                        EL (16 * (i + 1) + 15) sha512_K`
                                                                    ASSUME_TAC THENL
                                                                     [FIRST_X_ASSUM(MP_TAC o SPEC `16 * (i + 1) + 15:num`) THEN
                                                                      ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                      DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
                                                                    ARM_STEPS_TAC NOHW3_EXEC (1--30) THEN
                                                                    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                                    REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                                                                                sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
                                                                    SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                                    MP_TAC(SPECL [`16 * (i + 1) + 15:num`;
                                                                                  `W:int64 list`;
                                                                                  `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                                                                                 LIST_8_COMPRESS_NOHW3_64) THEN
                                                                    ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
                                                                    DISCH_THEN(X_CHOOSE_THEN `a_bk15:int64`
                                                                      (X_CHOOSE_THEN `b_bk15:int64` (X_CHOOSE_THEN `c_bk15:int64`
                                                                      (X_CHOOSE_THEN `d_bk15:int64` (X_CHOOSE_THEN `e_bk15:int64`
                                                                      (X_CHOOSE_THEN `f_bk15:int64` (X_CHOOSE_THEN `g_bk15:int64`
                                                                      (X_CHOOSE_THEN `h_bk15:int64` ASSUME_TAC)))))))) THEN
                                                                    ASM_REWRITE_TAC[] THEN
                                                                    CONV_TAC(DEPTH_CONV EL_CONV) THEN
                                                                    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                                                                             WORD_ZX_TRIVIAL] THEN
                                                                    REWRITE_TAC[EQ_REFL] THEN
                                                                    REWRITE_TAC[ADD_CLAUSES] THEN
                                                                    REPEAT CONJ_TAC THENL
                                                                     [CONV_TAC WORD_RULE;
                                                                      CONV_TAC WORD_RULE;
                                                                      CONV_TAC WORD_RULE;
                                                                      MP_TAC(SPECL [`16 * (i + 1) + 15:num`; `M_i:int64 list`] SHA512_W_EXTEND) THEN
                                                                      ANTS_TAC THENL
                                                                       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                        REWRITE_TAC[ARITH_RULE `(16 * (i + 1) + 15) + 16 = 16 * (i + 1) + 31`;
                                                                                    ARITH_RULE `(16 * (i + 1) + 15) + 14 = 16 * (i + 1) + 29`;
                                                                                    ARITH_RULE `(16 * (i + 1) + 15) + 9 = 16 * (i + 1) + 24`;
                                                                                    ARITH_RULE `(16 * (i + 1) + 15) + 1 = 16 * (i + 1) + 16`] THEN
                                                                      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
                                                                      SUBGOAL_THEN
                                                                       `!j. j < 16 + 16 * (i + 1) + 15 ==>
                                                                            EL j (sha512_message_schedule (16 * (i + 1) + 15) (M_i:int64 list)) =
                                                                            EL j (sha512_message_schedule 64 M_i)`
                                                                      MP_TAC THENL
                                                                       [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
                                                                        MATCH_MP_TAC SHA512_SCHEDULE_MONO THEN ASM_REWRITE_TAC[] THEN
                                                                        UNDISCH_TAC `i < 2` THEN UNDISCH_TAC `j < 16 + 16 * (i + 1) + 15` THEN ARITH_TAC;
                                                                        ALL_TAC] THEN
                                                                      DISCH_THEN(fun th ->
                                                                        MAP_EVERY (fun e -> MP_TAC(SPEC e th))
                                                                          [`16 * (i + 1) + 15:num`; `16 * (i + 1) + 16`;
                                                                           `16 * (i + 1) + 24`; `16 * (i + 1) + 29`]) THEN
                                                                      REPEAT(ANTS_TAC THENL [UNDISCH_TAC `i < 2` THEN ARITH_TAC; DISCH_TAC]) THEN
                                                                      ASM_REWRITE_TAC[] THEN
                                                                      REWRITE_TAC[sha512_sigma0; sha512_sigma1] THEN
                                                                      SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
                                                                      DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE];
                                                                    (* ----- sub x30, x30, #1 at pc+0x848 ----- *)
                                                                    SUBGOAL_THEN `3 - i < 2 EXP 64` ASSUME_TAC THENL
                                                                     [ASM_ARITH_TAC; ALL_TAC] THEN
                                                                    VAL_INT64_TAC `3 - i` THEN
                                                                    ENSURES_INIT_TAC "s0" THEN
                                                                    ARM_STEPS_TAC NOHW3_EXEC (1--1) THEN
                                                                    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                                                    REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 16 = 16 * ((i + 1) + 1)`;
                                                                                ARITH_RULE `64 * (i + 1) + 64 = 64 * ((i + 1) + 1)`;
                                                                                ARITH_RULE `16 * (i + 1) + 17 = 16 * ((i + 1) + 1) + 1`;
                                                                                ARITH_RULE `16 * (i + 1) + 18 = 16 * ((i + 1) + 1) + 2`;
                                                                                ARITH_RULE `16 * (i + 1) + 19 = 16 * ((i + 1) + 1) + 3`;
                                                                                ARITH_RULE `16 * (i + 1) + 20 = 16 * ((i + 1) + 1) + 4`;
                                                                                ARITH_RULE `16 * (i + 1) + 21 = 16 * ((i + 1) + 1) + 5`;
                                                                                ARITH_RULE `16 * (i + 1) + 22 = 16 * ((i + 1) + 1) + 6`;
                                                                                ARITH_RULE `16 * (i + 1) + 23 = 16 * ((i + 1) + 1) + 7`;
                                                                                ARITH_RULE `16 * (i + 1) + 24 = 16 * ((i + 1) + 1) + 8`;
                                                                                ARITH_RULE `16 * (i + 1) + 25 = 16 * ((i + 1) + 1) + 9`;
                                                                                ARITH_RULE `16 * (i + 1) + 26 = 16 * ((i + 1) + 1) + 10`;
                                                                                ARITH_RULE `16 * (i + 1) + 27 = 16 * ((i + 1) + 1) + 11`;
                                                                                ARITH_RULE `16 * (i + 1) + 28 = 16 * ((i + 1) + 1) + 12`;
                                                                                ARITH_RULE `16 * (i + 1) + 29 = 16 * ((i + 1) + 1) + 13`;
                                                                                ARITH_RULE `16 * (i + 1) + 30 = 16 * ((i + 1) + 1) + 14`;
                                                                                ARITH_RULE `16 * (i + 1) + 31 = 16 * ((i + 1) + 1) + 15`] THEN
                                                                    REWRITE_TAC[ADD_CLAUSES] THEN
                                                                    SUBGOAL_THEN `3 - i = (3 - (i+1)) + 1` SUBST1_TAC THENL
                                                                     [UNDISCH_TAC `i < 2` THEN ARITH_TAC; ALL_TAC] THEN
                                                                    REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE]
                                                                ]
                                                              ]
                                                            ]
                                                          ]
                                                        ]
                                                      ]
                                                    ]
                                                  ]
                                                ]
                                              ]
                                            ]
                                          ]
                                        ]
                                          ]];

                                      (* BACK-EDGE: cbnz taken at pc+0x84c (X30 = word(2-i) != 0 for i<2) *)
                                      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
                                      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
                                      SUBGOAL_THEN `3 - i < 2 EXP 64` ASSUME_TAC THENL
                                       [ASM_ARITH_TAC; ALL_TAC] THEN
                                      VAL_INT64_TAC `3 - i` THEN
                                      ENSURES_INIT_TAC "s0" THEN
                                      ARM_STEPS_TAC NOHW3_EXEC (1--1) THEN
                                      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                      ASM_SIMP_TAC[ARITH_RULE `0 < i /\ i < 3 ==> ~(3 - i = 0)`];

                                      (* EXIT: cbnz not taken at pc+0x84c (X30 = word(2-2) = word 0) *)
                                      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
                                      ENSURES_INIT_TAC "s0" THEN
                                      ARM_STEPS_TAC NOHW3_EXEC (1--1) THEN
                                      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
                                      REWRITE_TAC[ARITH_RULE `3 - 3 = 0`;
                                                  ARITH_RULE `16 * (3 + 1) = 64`;
                                                  ARITH_RULE `16 * (3 + 1) + 0 = 64`;
                                                  ARITH_RULE `16 * (3 + 1) + 1 = 65`;
                                                  ARITH_RULE `16 * (3 + 1) + 2 = 66`;
                                                  ARITH_RULE `16 * (3 + 1) + 3 = 67`;
                                                  ARITH_RULE `16 * (3 + 1) + 4 = 68`;
                                                  ARITH_RULE `16 * (3 + 1) + 5 = 69`;
                                                  ARITH_RULE `16 * (3 + 1) + 6 = 70`;
                                                  ARITH_RULE `16 * (3 + 1) + 7 = 71`;
                                                  ARITH_RULE `16 * (3 + 1) + 8 = 72`;
                                                  ARITH_RULE `16 * (3 + 1) + 9 = 73`;
                                                  ARITH_RULE `16 * (3 + 1) + 10 = 74`;
                                                  ARITH_RULE `16 * (3 + 1) + 11 = 75`;
                                                  ARITH_RULE `16 * (3 + 1) + 12 = 76`;
                                                  ARITH_RULE `16 * (3 + 1) + 13 = 77`;
                                                  ARITH_RULE `16 * (3 + 1) + 14 = 78`;
                                                  ARITH_RULE `16 * (3 + 1) + 15 = 79`;
                                                  ARITH_RULE `128 * (3 + 1) = 512`] THEN
                                      REWRITE_TAC[ADD_CLAUSES]]]]]]]]]]]]]]]]]];

    ALL_TAC] THEN

  (* ===== D-tail: pc+0x850 .. pc+0xd90, 16 compression-only rounds. ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xd90`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X3 s = word_add kptr (word 640) /\
         read X4 s = (EL 0 (sha512_compress 80 W
                    [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X5 s = (EL 1 (sha512_compress 80 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X6 s = (EL 2 (sha512_compress 80 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X7 s = (EL 3 (sha512_compress 80 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X8 s = (EL 4 (sha512_compress 80 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X9 s = (EL 5 (sha512_compress 80 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X10 s = (EL 6 (sha512_compress 80 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read X11 s = (EL 7 (sha512_compress 80 W
                    [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* D-tail body proof: 16 ROUND_NOSCHED (pc+0x850..pc+0xd90).              *)
    ENSURES_SEQUENCE_TAC `pc + 0x8a4`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 520) /\
             read X4 s = (EL 1 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 2 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 3 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 4 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 5 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 6 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 7 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 0 (sha512_compress 65 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 64: pc+0x850..pc+0x8a4, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `65 = 64 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 512):int64 =
                        word_add kptr (word (8 * 64))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 64)))) s0 =
              EL 64 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `64:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`64:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d64:int64`
            (X_CHOOSE_THEN `b_d64:int64` (X_CHOOSE_THEN `c_d64:int64`
            (X_CHOOSE_THEN `d_d64:int64` (X_CHOOSE_THEN `e_d64:int64`
            (X_CHOOSE_THEN `f_d64:int64` (X_CHOOSE_THEN `g_d64:int64`
            (X_CHOOSE_THEN `h_d64:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0x8f8`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 528) /\
             read X4 s = (EL 2 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 3 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 4 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 5 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 6 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 7 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 0 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 1 (sha512_compress 66 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 65: pc+0x8a4..pc+0x8f8, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `66 = 65 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 520):int64 =
                        word_add kptr (word (8 * 65))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 65)))) s0 =
              EL 65 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `65:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`65:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d65:int64`
            (X_CHOOSE_THEN `b_d65:int64` (X_CHOOSE_THEN `c_d65:int64`
            (X_CHOOSE_THEN `d_d65:int64` (X_CHOOSE_THEN `e_d65:int64`
            (X_CHOOSE_THEN `f_d65:int64` (X_CHOOSE_THEN `g_d65:int64`
            (X_CHOOSE_THEN `h_d65:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0x94c`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 536) /\
             read X4 s = (EL 3 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 4 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 5 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 6 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 7 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 0 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 1 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 2 (sha512_compress 67 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 66: pc+0x8f8..pc+0x94c, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `67 = 66 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 528):int64 =
                        word_add kptr (word (8 * 66))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 66)))) s0 =
              EL 66 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `66:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`66:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d66:int64`
            (X_CHOOSE_THEN `b_d66:int64` (X_CHOOSE_THEN `c_d66:int64`
            (X_CHOOSE_THEN `d_d66:int64` (X_CHOOSE_THEN `e_d66:int64`
            (X_CHOOSE_THEN `f_d66:int64` (X_CHOOSE_THEN `g_d66:int64`
            (X_CHOOSE_THEN `h_d66:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0x9a0`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 544) /\
             read X4 s = (EL 4 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 5 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 6 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 7 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 0 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 1 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 2 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 3 (sha512_compress 68 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 67: pc+0x94c..pc+0x9a0, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `68 = 67 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 536):int64 =
                        word_add kptr (word (8 * 67))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 67)))) s0 =
              EL 67 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `67:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`67:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d67:int64`
            (X_CHOOSE_THEN `b_d67:int64` (X_CHOOSE_THEN `c_d67:int64`
            (X_CHOOSE_THEN `d_d67:int64` (X_CHOOSE_THEN `e_d67:int64`
            (X_CHOOSE_THEN `f_d67:int64` (X_CHOOSE_THEN `g_d67:int64`
            (X_CHOOSE_THEN `h_d67:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0x9f4`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 552) /\
             read X4 s = (EL 5 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 6 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 7 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 0 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 1 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 2 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 3 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 4 (sha512_compress 69 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 68: pc+0x9a0..pc+0x9f4, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `69 = 68 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 544):int64 =
                        word_add kptr (word (8 * 68))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 68)))) s0 =
              EL 68 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `68:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`68:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d68:int64`
            (X_CHOOSE_THEN `b_d68:int64` (X_CHOOSE_THEN `c_d68:int64`
            (X_CHOOSE_THEN `d_d68:int64` (X_CHOOSE_THEN `e_d68:int64`
            (X_CHOOSE_THEN `f_d68:int64` (X_CHOOSE_THEN `g_d68:int64`
            (X_CHOOSE_THEN `h_d68:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xa48`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 560) /\
             read X4 s = (EL 6 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 7 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 0 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 1 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 2 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 3 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 4 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 5 (sha512_compress 70 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 69: pc+0x9f4..pc+0xa48, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `70 = 69 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 552):int64 =
                        word_add kptr (word (8 * 69))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 69)))) s0 =
              EL 69 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `69:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`69:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d69:int64`
            (X_CHOOSE_THEN `b_d69:int64` (X_CHOOSE_THEN `c_d69:int64`
            (X_CHOOSE_THEN `d_d69:int64` (X_CHOOSE_THEN `e_d69:int64`
            (X_CHOOSE_THEN `f_d69:int64` (X_CHOOSE_THEN `g_d69:int64`
            (X_CHOOSE_THEN `h_d69:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xa9c`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 568) /\
             read X4 s = (EL 7 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 0 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 1 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 2 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 3 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 4 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 5 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 6 (sha512_compress 71 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 70: pc+0xa48..pc+0xa9c, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `71 = 70 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 560):int64 =
                        word_add kptr (word (8 * 70))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 70)))) s0 =
              EL 70 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `70:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`70:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d70:int64`
            (X_CHOOSE_THEN `b_d70:int64` (X_CHOOSE_THEN `c_d70:int64`
            (X_CHOOSE_THEN `d_d70:int64` (X_CHOOSE_THEN `e_d70:int64`
            (X_CHOOSE_THEN `f_d70:int64` (X_CHOOSE_THEN `g_d70:int64`
            (X_CHOOSE_THEN `h_d70:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xaf0`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 576) /\
             read X4 s = (EL 0 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 1 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 2 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 3 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 4 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 5 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 6 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 7 (sha512_compress 72 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 71: pc+0xa9c..pc+0xaf0, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `72 = 71 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 568):int64 =
                        word_add kptr (word (8 * 71))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 71)))) s0 =
              EL 71 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `71:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`71:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d71:int64`
            (X_CHOOSE_THEN `b_d71:int64` (X_CHOOSE_THEN `c_d71:int64`
            (X_CHOOSE_THEN `d_d71:int64` (X_CHOOSE_THEN `e_d71:int64`
            (X_CHOOSE_THEN `f_d71:int64` (X_CHOOSE_THEN `g_d71:int64`
            (X_CHOOSE_THEN `h_d71:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xb44`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 584) /\
             read X4 s = (EL 1 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 2 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 3 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 4 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 5 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 6 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 7 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 0 (sha512_compress 73 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 72: pc+0xaf0..pc+0xb44, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `73 = 72 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 576):int64 =
                        word_add kptr (word (8 * 72))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 72)))) s0 =
              EL 72 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `72:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`72:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d72:int64`
            (X_CHOOSE_THEN `b_d72:int64` (X_CHOOSE_THEN `c_d72:int64`
            (X_CHOOSE_THEN `d_d72:int64` (X_CHOOSE_THEN `e_d72:int64`
            (X_CHOOSE_THEN `f_d72:int64` (X_CHOOSE_THEN `g_d72:int64`
            (X_CHOOSE_THEN `h_d72:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xb98`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 592) /\
             read X4 s = (EL 2 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 3 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 4 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 5 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 6 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 7 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 0 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 1 (sha512_compress 74 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 73: pc+0xb44..pc+0xb98, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `74 = 73 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 584):int64 =
                        word_add kptr (word (8 * 73))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 73)))) s0 =
              EL 73 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `73:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`73:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d73:int64`
            (X_CHOOSE_THEN `b_d73:int64` (X_CHOOSE_THEN `c_d73:int64`
            (X_CHOOSE_THEN `d_d73:int64` (X_CHOOSE_THEN `e_d73:int64`
            (X_CHOOSE_THEN `f_d73:int64` (X_CHOOSE_THEN `g_d73:int64`
            (X_CHOOSE_THEN `h_d73:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xbec`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 600) /\
             read X4 s = (EL 3 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 4 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 5 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 6 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 7 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 0 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 1 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 2 (sha512_compress 75 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 74: pc+0xb98..pc+0xbec, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `75 = 74 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 592):int64 =
                        word_add kptr (word (8 * 74))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 74)))) s0 =
              EL 74 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `74:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`74:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d74:int64`
            (X_CHOOSE_THEN `b_d74:int64` (X_CHOOSE_THEN `c_d74:int64`
            (X_CHOOSE_THEN `d_d74:int64` (X_CHOOSE_THEN `e_d74:int64`
            (X_CHOOSE_THEN `f_d74:int64` (X_CHOOSE_THEN `g_d74:int64`
            (X_CHOOSE_THEN `h_d74:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xc40`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 608) /\
             read X4 s = (EL 4 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 5 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 6 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 7 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 0 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 1 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 2 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 3 (sha512_compress 76 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 75: pc+0xbec..pc+0xc40, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `76 = 75 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 600):int64 =
                        word_add kptr (word (8 * 75))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 75)))) s0 =
              EL 75 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `75:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`75:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d75:int64`
            (X_CHOOSE_THEN `b_d75:int64` (X_CHOOSE_THEN `c_d75:int64`
            (X_CHOOSE_THEN `d_d75:int64` (X_CHOOSE_THEN `e_d75:int64`
            (X_CHOOSE_THEN `f_d75:int64` (X_CHOOSE_THEN `g_d75:int64`
            (X_CHOOSE_THEN `h_d75:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xc94`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 616) /\
             read X4 s = (EL 5 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 6 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 7 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 0 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 1 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 2 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 3 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 4 (sha512_compress 77 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 76: pc+0xc40..pc+0xc94, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `77 = 76 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 608):int64 =
                        word_add kptr (word (8 * 76))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 76)))) s0 =
              EL 76 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `76:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`76:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d76:int64`
            (X_CHOOSE_THEN `b_d76:int64` (X_CHOOSE_THEN `c_d76:int64`
            (X_CHOOSE_THEN `d_d76:int64` (X_CHOOSE_THEN `e_d76:int64`
            (X_CHOOSE_THEN `f_d76:int64` (X_CHOOSE_THEN `g_d76:int64`
            (X_CHOOSE_THEN `h_d76:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xce8`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 624) /\
             read X4 s = (EL 6 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 7 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 0 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 1 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 2 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 3 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 4 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 5 (sha512_compress 78 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 77: pc+0xc94..pc+0xce8, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `78 = 77 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 616):int64 =
                        word_add kptr (word (8 * 77))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 77)))) s0 =
              EL 77 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `77:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`77:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d77:int64`
            (X_CHOOSE_THEN `b_d77:int64` (X_CHOOSE_THEN `c_d77:int64`
            (X_CHOOSE_THEN `d_d77:int64` (X_CHOOSE_THEN `e_d77:int64`
            (X_CHOOSE_THEN `f_d77:int64` (X_CHOOSE_THEN `g_d77:int64`
            (X_CHOOSE_THEN `h_d77:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

    ENSURES_SEQUENCE_TAC `pc + 0xd3c`
      `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
             read SP s = stackpointer /\
             read X29 s = state_ptr /\
             read X3 s = word_add kptr (word 632) /\
             read X4 s = (EL 7 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X5 s = (EL 0 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X6 s = (EL 1 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X7 s = (EL 2 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X8 s = (EL 3 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X9 s = (EL 4 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X10 s = (EL 5 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X11 s = (EL 6 (sha512_compress 79 W
                        [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) /\
             read X19 s = (EL 64 (W:int64 list)) /\
             read X20 s = (EL 65 (W:int64 list)) /\
             read X21 s = (EL 66 (W:int64 list)) /\
             read X22 s = (EL 67 (W:int64 list)) /\
             read X23 s = (EL 68 (W:int64 list)) /\
             read X24 s = (EL 69 (W:int64 list)) /\
             read X25 s = (EL 70 (W:int64 list)) /\
             read X26 s = (EL 71 (W:int64 list)) /\
             read X27 s = (EL 72 (W:int64 list)) /\
             read X28 s = (EL 73 (W:int64 list)) /\
             read X12 s = (EL 74 (W:int64 list)) /\
             read X13 s = (EL 75 (W:int64 list)) /\
             read X14 s = (EL 76 (W:int64 list)) /\
             read X15 s = (EL 77 (W:int64 list)) /\
             read X16 s = (EL 78 (W:int64 list)) /\
             read X17 s = (EL 79 (W:int64 list)) /\
             read (memory :> bytes64 (word_add stackpointer (word 96))) s =
               dptr_i /\
             read (memory :> bytes64 (word_add stackpointer (word 104))) s =
               word(num_blocks - ii) /\
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
     [(* ----- D-tail round 78: pc+0xce8..pc+0xd3c, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `79 = 78 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 624):int64 =
                        word_add kptr (word (8 * 78))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 78)))) s0 =
              EL 78 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `78:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`78:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d78:int64`
            (X_CHOOSE_THEN `b_d78:int64` (X_CHOOSE_THEN `c_d78:int64`
            (X_CHOOSE_THEN `d_d78:int64` (X_CHOOSE_THEN `e_d78:int64`
            (X_CHOOSE_THEN `f_d78:int64` (X_CHOOSE_THEN `g_d78:int64`
            (X_CHOOSE_THEN `h_d78:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE];

          (* ----- D-tail round 79: pc+0xd3c..pc+0xd90, 21 insts (ROUND_NOSCHED). ----- *)
          ONCE_REWRITE_TAC[ARITH_RULE `80 = 79 + 1`] THEN
          REWRITE_TAC[sha512_compress] THEN
          SUBGOAL_THEN `word_add kptr (word 632):int64 =
                        word_add kptr (word (8 * 79))` SUBST_ALL_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
             `read (memory :> bytes64 (word_add kptr (word (8 * 79)))) s0 =
              EL 79 sha512_K`
          ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `79:num`) THEN
            ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[ARITH] THEN
            DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
          ARM_STEPS_TAC NOHW3_EXEC (1--21) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[sha512_compress_round; sha512_Sigma0; sha512_Sigma1;
                      sha512_Ch; sha512_Maj; LET_DEF; LET_END_DEF] THEN
          SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_64; ARITH] THEN
          MP_TAC(SPECL [`79:num`;
                        `W:int64 list`;
                        `[a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i]`]
                       LIST_8_COMPRESS_NOHW3_64) THEN
          ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `a_d79:int64`
            (X_CHOOSE_THEN `b_d79:int64` (X_CHOOSE_THEN `c_d79:int64`
            (X_CHOOSE_THEN `d_d79:int64` (X_CHOOSE_THEN `e_d79:int64`
            (X_CHOOSE_THEN `f_d79:int64` (X_CHOOSE_THEN `g_d79:int64`
            (X_CHOOSE_THEN `h_d79:int64` ASSUME_TAC)))))))) THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC(DEPTH_CONV EL_CONV) THEN
          SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
                   WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[EQ_REFL] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE]]]]]]]]]]]]]]]]
;

    ALL_TAC] THEN

  (* ===== Phase E: add-back (pc+0xd90 .. pc+0xdd0, 16 insts). ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xdd0`
    `\s. aligned_bytes_loaded s (word pc) sha512_block_data_order_nohw3_mc /\
         read SP s = stackpointer /\
         read X29 s = state_ptr /\
         read X3 s = word_add kptr (word 640) /\
         read X4 s = word_add
            (EL 0 (sha512_compress 80 W
                   [a_i:int64;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) a_i /\
         read X5 s = word_add
            (EL 1 (sha512_compress 80 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) b_i /\
         read X6 s = word_add
            (EL 2 (sha512_compress 80 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) c_i /\
         read X7 s = word_add
            (EL 3 (sha512_compress 80 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) d_i /\
         read X8 s = word_add
            (EL 4 (sha512_compress 80 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) e_i /\
         read X9 s = word_add
            (EL 5 (sha512_compress 80 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) f_i /\
         read X10 s = word_add
            (EL 6 (sha512_compress 80 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) g_i /\
         read X11 s = word_add
            (EL 7 (sha512_compress 80 W
                   [a_i;b_i;c_i;d_i;e_i;f_i;g_i;h_i])) h_i /\
         read (memory :> bytes64 (word_add stackpointer (word 96))) s =
           dptr_i /\
         read (memory :> bytes64 (word_add stackpointer (word 104))) s =
           word(num_blocks - ii) /\
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
   [(* Phase E: 8 (ldr + add) pairs. *)
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun k ->
     let th = SPECL [k] (ASSUME
      `forall t.
           t < 8
           ==> read (memory :> bytes64 (word_add state_ptr (word(8*t)))) s0 =
               EL t [a_i:int64; b_i; c_i; d_i; e_i; f_i; g_i; h_i]`) in
     MP_TAC th THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH; EL; HD; TL] THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     REWRITE_TAC[WORD_ADD_0] THEN
     DISCH_TAC)
     [`0`; `1`; `2`; `3`; `4`; `5`; `6`; `7`] THEN
    ARM_STEPS_TAC NOHW3_EXEC (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH;
             WORD_ZX_TRIVIAL] THEN
    REWRITE_TAC[EQ_REFL] THEN
    REWRITE_TAC[EL; HD; TL] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[];

    ALL_TAC] THEN

  (* ===== Phase F + postamble: pc+0xdd0 .. pc+0xe00 (12 insts body +
     cbnz at pc+0xe00 handled by outer ENSURES_WHILE_UP_TAC back-edge).
     12 insts: 8 str (Phase F) + ldp + add + sub + sub.                   *)
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC NOHW3_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [(* X1 = word_add data_ptr (word(128 * (ii+1))) *)
    REWRITE_TAC[ARITH_RULE `128 * (ii+1) = 128 * ii + 128`] THEN
    UNDISCH_TAC `word_add data_ptr (word(128 * ii):int64) = dptr_i` THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* X2 = word (num_blocks - (ii+1)) *)
    SUBGOAL_THEN `num_blocks - ii = (num_blocks - (ii + 1)) + 1` ASSUME_TAC THENL
     [UNDISCH_TAC `ii < num_blocks` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* state memory: EL t (sha512_hash_blocks (ii+1) blocks H0) for t<8 *)
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
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 EL)]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper.                                                       *)
(* ------------------------------------------------------------------------- *)

let SHA512_BLOCK_DATA_ORDER_NOHW3_SUBROUTINE_CORRECT = prove
 (`!num_blocks (blocks:(int64 list) list)
    (a:int64) b c d (e:int64) f g h
    state_ptr data_ptr kptr pc stackpointer returnaddress.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 stackpointer /\
    nonoverlapping (state_ptr,32)
                   (word_sub stackpointer (word 112), 112) /\
    ALLPAIRS nonoverlapping
             [(state_ptr:int64,64);
              (word_sub stackpointer (word 112):int64, 112)]
             [(word pc, 0xe28);
              (data_ptr:int64, 64 * num_blocks);
              (kptr:int64, 640)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
              sha512_block_data_order_nohw3_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 112), 112)])`,
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(8,8) NOHW3_EXEC
        SHA512_BLOCK_DATA_ORDER_NOHW3_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 112);;
