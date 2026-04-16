(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 multi-block hardware-accelerated function.                        *)
(*                                                                           *)
(* Proves correctness of sha256_block_data_order_hw, which processes         *)
(* num_blocks consecutive 512-bit message blocks using ARM SHA-256 hardware  *)
(* instructions (SHA256H/SHA256H2/SHA256SU0/SHA256SU1).                      *)
(*                                                                           *)
(* void sha256_block_data_order_hw(uint32_t state[8],                        *)
(*                                 const uint8_t *data,                      *)
(*                                 size_t num_blocks,                        *)
(*                                 const uint32_t K[64])                     *)
(*                                                                           *)
(* The proof uses the same cut-point approach as sha256_block_core.ml,       *)
(* adapted for memory-loaded message data (with REV32 byte-swap) and a      *)
(* multi-block outer loop.                                                   *)
(* ========================================================================= *)

needs "arm/proofs/sha256_block_core.ml";;

(* ========================================================================= *)
(* Machine code and execution rule.                                          *)
(* ========================================================================= *)

let sha256_hw_mc = define_from_elf "sha256_hw_mc"
  (file_on_path !load_path "arm/sha2/sha256_block_data_order_hw.o");;

let HW_EXEC = ARM_MK_EXEC_RULE sha256_hw_mc;;

(* ========================================================================= *)
(* Unconditional EL_W lemmas.                                                *)
(*                                                                           *)
(* EL_W_ALL_LIST from sha256_block_core.ml has the hypothesis               *)
(*   sha256_message_schedule 48 [w0;...;w15] = W                            *)
(* We build versions where this hypothesis is discharged, producing          *)
(* conditional lemmas |- hyp ==> EL n W = expr. These can be applied by     *)
(* REWRITE_TAC without the W assumption needing to be in context.            *)
(* ========================================================================= *)

let EL_W_UNCOND =
  let hyp = `sha256_message_schedule 48
    [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W` in
  let w_th = ASSUME hyp in
  List.map (fun el -> MP (DISCH hyp el) w_th) EL_W_ALL_LIST;;

(* ========================================================================= *)
(* Adapted CUT_POINT_TAC for the HW proof.                                  *)
(*                                                                           *)
(* Key difference from sha256_block_core.ml's CUT_POINT_TAC:                *)
(* - Uses UNDISCH_THEN to temporarily remove the W abbreviation before       *)
(*   ONCE_ASM_REWRITE_TAC (which substitutes Q0/Q1 register reads).         *)
(* - Uses GEN_REWRITE_TAC RAND_CONV to apply the bridge only to the RHS,    *)
(*   avoiding expansion of W.                                                *)
(* - After the SU bridge, also discards Q2/Q3/Q16 temporaries.              *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Parameterized CUT_POINT_TAC and POSTCOND_TAC.                             *)
(*                                                                           *)
(* These take an initial hash state h_tm : term (e.g., `[a;b;c;d;e;f;g;h]`) *)
(* as a parameter, allowing them to work both for the single-block proof     *)
(* (with concrete variables) and the multi-block loop body (with ghost       *)
(* variables from sha256_hash_blocks).                                       *)
(* ========================================================================= *)

let GEN_CUT_POINT_TAC h_tm i sname =
  let target = mk_small_numeral(4 * (i + 1)) in
  let bridge_h = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int32 list`; h_tm] GROUP_BRIDGE_H.(i)) in
  let bridge_h2 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int32 list`; h_tm] GROUP_BRIDGE_H2.(i)) in
  let q0_tm = subst [sname, `s:armstate`; target, `t:num`; h_tm, `H:int32 list`]
    `read Q0 s = word_join4
      (EL 0 (sha256_compress t W (H:int32 list)))
      (EL 1 (sha256_compress t W H))
      (EL 2 (sha256_compress t W H))
      (EL 3 (sha256_compress t W H))` in
  let q1_tm = subst [sname, `s:armstate`; target, `t:num`; h_tm, `H:int32 list`]
    `read Q1 s = word_join4
      (EL 4 (sha256_compress t W (H:int32 list)))
      (EL 5 (sha256_compress t W H))
      (EL 6 (sha256_compress t W H))
      (EL 7 (sha256_compress t W H))` in
  let CUT_SUBGOAL_TAC bridge =
    ASM_REWRITE_TAC[bridge] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress)))) THEN
    TRY(CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV))) THEN
    REWRITE_TAC EL_W_ALL_LIST THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST;
                WORD_JOIN4_SUBWORD; WORD_JOIN_4x32] THEN
    REFL_TAC in
  SUBGOAL_THEN q0_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h; ALL_TAC] THEN
  SUBGOAL_THEN q1_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h2; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let n = fst(dest_const t) in n = "sha256h" || n = "sha256h2"
      with _ -> false)) (concl th)))) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t ->
        try fst(dest_const t) = "sha256su1" with _ -> false)) (concl th)
    then REWRITE_RULE[SHA256SU_BRIDGE_FLAT] th
    else th) THEN
  DISCARD_MATCHING_ASSUMPTIONS
    [`read Q2 s = x:int128`;
     `read Q3 s = x:int128`;
     `read Q16 s = x:int128`];;

(* Single-block version: h_tm = [a;b;c;d;e;f;g;h] *)
let CUT_POINT_TAC_HW i sname =
  GEN_CUT_POINT_TAC `[a:int32;b;c;d;e;f;g;h]` i sname;;

(* ========================================================================= *)
(* Parameterized POSTCOND_TAC.                                               *)
(* ========================================================================= *)

let GEN_POSTCOND_TAC h_tm =
  let len_h = prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, h_tm), `8`),
    REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let m = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;
            w8;w9;w10;w11;w12;w13;w14;w15]` in
  let hw_w_abbrev = ASSUME
    `sha256_message_schedule 48
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W` in
  let inst = MP (SPECL [m; h_tm] SHA256_BLOCK_EL) len_h in
  let block_el = List.map (fun k ->
    let th = SPEC (mk_small_numeral k) inst in
    let th2 = MP th (prove(lhand(concl th), ARITH_TAC)) in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2 in
    REWRITE_RULE[hw_w_abbrev] th3) (0--7) in
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC block_el THEN
  REFL_TAC;;

let POSTCOND_TAC_HW = GEN_POSTCOND_TAC `[a:int32;b;c;d;e;f;g;h]`;;

(* GEN_POSTCOND_TAC2: like GEN_POSTCOND_TAC but takes an external LENGTH     *)
(* proof, needed for opaque h_tm like sha256_hash_blocks where LENGTH can't  *)
(* be computed by REWRITE_TAC[LENGTH] THEN ARITH_TAC.                        *)

let GEN_POSTCOND_TAC2 h_tm len_h =
  let m = `[w0:int32;w1;w2;w3;w4;w5;w6;w7;
            w8;w9;w10;w11;w12;w13;w14;w15]` in
  let hw_w_abbrev = ASSUME
    `sha256_message_schedule 48
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] = W` in
  let inst = MP (SPECL [m; h_tm] SHA256_BLOCK_EL) len_h in
  let block_el = List.map (fun k ->
    let th = SPEC (mk_small_numeral k) inst in
    let th2 = MP th (prove(lhand(concl th), ARITH_TAC)) in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2 in
    REWRITE_RULE[hw_w_abbrev] th3) (0--7) in
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC block_el THEN
  REFL_TAC;;

(* Single-block proof moved to sha256_hw_1block.ml for faster iteration. *)

(* ========================================================================= *)
(* Helper lemmas for multi-block body proof.                                 *)
(* ========================================================================= *)

let LENGTH_SHA256_HASH_BLOCKS = prove
 (`!n blocks H:int32 list. LENGTH H = 8
   ==> LENGTH(sha256_hash_blocks n blocks H) = 8`,
  INDUCT_TAC THENL
   [REWRITE_TAC[sha256_hash_blocks];
    REWRITE_TAC[ARITH_RULE `SUC n = n + 1`; sha256_hash_blocks] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LENGTH_SHA256_BLOCK THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let WORD_SUB_SUC = prove
 (`!n. word_sub (word(SUC n):int64) (word 1) = word n`,
  GEN_TAC THEN REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV
    (WORD_RULE `word_sub(word_add x (word 1))(word 1):int64 = x`))));;

(* REV32_BITBLAST_TAC: establish clean word_join4 form for a SIMD register   *)
(* after REV32 instruction (double byte-reversal cancels).                   *)

let REV32_BITBLAST_TAC qpat qtm =
  SUBGOAL_THEN qtm
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] qpat) (concl asm) &&
         not (can (find_term (fun t ->
           try fst(dest_const t) = "EL" with _ -> false)) (concl asm))
      then th else asm))
  THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN
    BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC];;

(* EXPAND_K_TAC: expand quantified K constant into individual assumptions.   *)

let EXPAND_K_TAC =
  FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "sha256_K" with _ -> false)) (concl th)
    then
      MAP_EVERY (fun i ->
        let spec = SPEC (mk_small_numeral i) th in
        let mp = MP spec (prove(lhand(concl spec), ARITH_TAC)) in
        ASSUME_TAC(CONV_RULE
          (DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) mp))
        (0--15)
    else FAIL_TAC "");;

(* EXPAND_DATA_TAC: specialize quantified data memory at j=ii.               *)

let EXPAND_DATA_TAC =
  FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl th)
    then
      MP_TAC(SPEC `ii:num` th) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]
    else FAIL_TAC "");;

(* ========================================================================= *)
(* Multi-block correctness.                                                  *)
(*                                                                           *)
(* Uses ENSURES_WHILE_UP_TAC with the loop invariant:                        *)
(*   after i blocks, Q0/Q1 hold the iterated sha256_block result,           *)
(*   X1 advanced by 64*i, X2 decremented by i.                             *)
(* ========================================================================= *)

needs "arm/proofs/utils/sha256_spec.ml";;

(* ========================================================================= *)
(* Multi-block correctness theorem.                                          *)
(*                                                                           *)
(* The `blocks` parameter represents the SHA-256-ready message blocks        *)
(* (after byte-reversal). Memory contains word_bytereverse of each element   *)
(* (raw little-endian format); the assembly applies REV32 to convert.        *)
(*                                                                           *)
(* The loop invariant tracks sha256_hash_blocks i blocks H in Q0/Q1,        *)
(* data pointer at data_ptr + 64*i, block counter at num_blocks - i.        *)
(* ========================================================================= *)

let SHA256_HW_CORRECT = time prove(
 `!num_blocks state_ptr data_ptr kptr
   (a:int32) b c d (e:int32) f g h
   (blocks:(int32 list) list) pc.
   1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
   LENGTH blocks = num_blocks /\
   ALL (\bl. LENGTH bl = 16) blocks /\
   ALL (nonoverlapping (state_ptr, 32))
       [(word pc, 496); (data_ptr, 64 * num_blocks); (kptr, 256)] /\
   nonoverlapping (data_ptr, 64 * num_blocks) (word pc, 496) /\
   nonoverlapping (kptr, 256) (word pc, 496)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_hw_mc /\
         read PC s = word pc /\
         read X0 s = state_ptr /\
         read X1 s = data_ptr /\
         read X2 s = word num_blocks /\
         read X3 s = kptr /\
         read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
         read (memory :> bytes128 (word_add state_ptr (word 16))) s =
           word_join4 e f g h /\
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
         (!i. i < 16 ==>
           read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
           word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                      (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)))
    (\s. read PC s = word(pc + 0x1ec) /\
         (let result = sha256_hash_blocks num_blocks blocks [a;b;c;d;e;f;g;h] in
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

  SUBGOAL_THEN `~(num_blocks = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN

  ENSURES_WHILE_UP_TAC `num_blocks:num` `pc + 0x8` `pc + 0x1e0`
    `\i s. aligned_bytes_loaded s (word pc) sha256_hw_mc /\
           read X0 s = state_ptr /\
           read X1 s = word_add data_ptr (word(64 * i)) /\
           read X2 s = word(num_blocks - i) /\
           read X3 s = kptr /\
           read Q0 s = word_join4
             (EL 0 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h]:int32 list))
             (EL 1 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h]))
             (EL 2 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h]))
             (EL 3 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h])) /\
           read Q1 s = word_join4
             (EL 4 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h]:int32 list))
             (EL 5 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h]))
             (EL 6 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h]))
             (EL 7 (sha256_hash_blocks i blocks [a;b;c;d;e;f;g;h])) /\
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
           (!k. k < 16 ==>
             read (memory :> bytes128 (word_add kptr (word(16 * k)))) s =
             word_join4 (EL (4*k) sha256_K) (EL (4*k+1) sha256_K)
                        (EL (4*k+2) sha256_K) (EL (4*k+3) sha256_K)) /\
           read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
           read (memory :> bytes128 (word_add state_ptr (word 16))) s =
             word_join4 e f g h` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [

    (* ================================================================= *)
    (* Subgoal 1: INIT -- precondition ==> invariant(0) at pc+0x8        *)
    (* Execute instructions 1-2 (LDR Q0, LDR Q1 for state)              *)
    (* ================================================================= *)
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[sha256_hash_blocks; WORD_ADD_0; MULT_CLAUSES; SUB_0] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];

    (* ================================================================= *)
    (* Subgoal 2: BODY -- invariant(i) at pc+0x8 ==>                     *)
    (*            invariant(i+1) at pc+0x1e0                             *)
    (* This is the full single-block proof for one loop iteration.       *)
    (*                                                                   *)
    (* Key setup steps before symbolic execution:                        *)
    (*   1. Expand K constant quantifier into 16 individual assumptions  *)
    (*   2. Specialize data memory quantifier at j=ii                    *)
    (*   3. REV32 bitblast Q4-Q7 to clean word_join4(EL k ...) form     *)
    (*   4. Abbreviate w0-w15 and W                                      *)
    (* Then 16 round groups with cut-points + add-back + postcondition.  *)
    (* ================================================================= *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `num_blocks - ii < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `num_blocks - ii` THEN
    ENSURES_INIT_TAC "s0" THEN
    EXPAND_K_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    EXPAND_DATA_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
    ARM_STEPS_TAC HW_EXEC (1--12) THEN
    REV32_BITBLAST_TAC `read Q4 s = x:int128`
      `read Q4 s12 = word_join4 ((EL 0 (EL ii blocks)):int32)
        (EL 1 (EL ii blocks)) (EL 2 (EL ii blocks))
        (EL 3 (EL ii blocks))` THEN
    REV32_BITBLAST_TAC `read Q5 s = x:int128`
      `read Q5 s12 = word_join4 ((EL 4 (EL ii blocks)):int32)
        (EL 5 (EL ii blocks)) (EL 6 (EL ii blocks))
        (EL 7 (EL ii blocks))` THEN
    REV32_BITBLAST_TAC `read Q6 s = x:int128`
      `read Q6 s12 = word_join4 ((EL 8 (EL ii blocks)):int32)
        (EL 9 (EL ii blocks)) (EL 10 (EL ii blocks))
        (EL 11 (EL ii blocks))` THEN
    REV32_BITBLAST_TAC `read Q7 s = x:int128`
      `read Q7 s12 = word_join4 ((EL 12 (EL ii blocks)):int32)
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
    ABBREV_TAC `W = sha256_message_schedule 48
      [w0:int32;w1;w2;w3;w4;w5;w6;w7;
       w8;w9;w10;w11;w12;w13;w14;w15]` THEN
    (let h_tm = `sha256_hash_blocks ii blocks [a:int32;b;c;d;e;f;g;h]` in
    ARM_STEPS_TAC HW_EXEC (13--19) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 0 `s19:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (20--26) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 1 `s26:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (27--33) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 2 `s33:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (34--40) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 3 `s40:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (41--47) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 4 `s47:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (48--54) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 5 `s54:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (55--61) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 6 `s61:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (62--68) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 7 `s68:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (69--75) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 8 `s75:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (76--82) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 9 `s82:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (83--89) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 10 `s89:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (90--96) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 11 `s96:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (97--101) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 12 `s101:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (102--106) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 13 `s106:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (107--111) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 14 `s111:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (112--116) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
      GEN_CUT_POINT_TAC h_tm 15 `s116:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (117--118) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[sha256_hash_blocks; sha256_block] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_ADD_ASSOC; GSYM WORD_ADD;
                ARITH_RULE `64 * ii + 64 = 64 * (ii + 1)`] THEN
    REWRITE_TAC[WORD_SUB_SUC] THEN
    GEN_POSTCOND_TAC2 h_tm
      (prove(`LENGTH(sha256_hash_blocks ii blocks [a:int32;b;c;d;e;f;g;h]) = 8`,
        MATCH_MP_TAC LENGTH_SHA256_HASH_BLOCKS THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC)));

    (* ================================================================= *)
    (* Subgoal 3: BACK-EDGE -- invariant(i) at pc+0x1e0 ==>             *)
    (*            invariant(i) at pc+0x8                                 *)
    (* Just CBNZ x2, .Loop_hw (1 instruction, branches since x2 != 0)   *)
    (* ================================================================= *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    VAL_INT64_TAC `num_blocks - ii` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

    (* ================================================================= *)
    (* Subgoal 4: EXIT -- invariant(num_blocks) at pc+0x1e0 ==>          *)
    (*            postcondition at pc+0x1ec                              *)
    (* CBNZ falls through (x2=0), STR Q0, STR Q1 (3 instructions)       *)
    (* RET is NOT executed here; handled by SUBROUTINE_CORRECT wrapper.  *)
    (* ================================================================= *)
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                NONOVERLAPPING_CLAUSES; SUB_REFL] THEN
    STRIP_TAC THEN
    VAL_INT64_TAC `num_blocks - num_blocks` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[]
  ]);;
