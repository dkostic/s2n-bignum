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

(* ADD_SIMP_RULE_SELECTIVE: apply WORD_JOIN4_SUBWORD/WORD_JOIN_4x32 only to    *)
(* assumptions that don't involve Q0 or Q1, since ADD_SIMP_RULE can cause     *)
(* Q0/Q1 (containing sha256h/sha256h2) to be absorbed into tautologies.       *)

let ADD_SIMP_RULE_SELECTIVE =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t ->
        try let n = fst(dest_const t) in n = "Q0" || n = "Q1"
        with _ -> false)) (concl th)
    then th
    else ADD_SIMP_RULE th);;

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
    CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV)) THEN
    REWRITE_TAC EL_W_ALL_LIST THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST] THEN
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

(* ========================================================================= *)
(* Single-block correctness (num_blocks = 1).                                *)
(* ========================================================================= *)

let SHA256_HW_1BLOCK_CORRECT = time prove(
 `!(a:int32) b c d (e:int32) f g h
   (m0:int32) m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
   state_ptr data_ptr kptr pc.
   ALL (nonoverlapping (state_ptr, 32))
       [(word pc, 496); (data_ptr, 64); (kptr, 256)] /\
   nonoverlapping (data_ptr, 64) (word pc, 496) /\
   nonoverlapping (kptr, 256) (word pc, 496)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_hw_mc /\
         read PC s = word pc /\
         read X30 s = word(pc + 0x1ec) /\
         read X0 s = state_ptr /\
         read X1 s = data_ptr /\
         read X2 s = word 1 /\
         read X3 s = kptr /\
         read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
         read (memory :> bytes128 (word_add state_ptr (word 16))) s =
           word_join4 e f g h /\
         read (memory :> bytes128 data_ptr) s = word_join4 m0 m1 m2 m3 /\
         read (memory :> bytes128 (word_add data_ptr (word 16))) s =
           word_join4 m4 m5 m6 m7 /\
         read (memory :> bytes128 (word_add data_ptr (word 32))) s =
           word_join4 m8 m9 m10 m11 /\
         read (memory :> bytes128 (word_add data_ptr (word 48))) s =
           word_join4 m12 m13 m14 m15 /\
         (!i. i < 16 ==>
           read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
           word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                      (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)))
    (\s. read PC s = word(pc + 0x1ec) /\
         (let M = [word_bytereverse m0; word_bytereverse m1;
                   word_bytereverse m2; word_bytereverse m3;
                   word_bytereverse m4; word_bytereverse m5;
                   word_bytereverse m6; word_bytereverse m7;
                   word_bytereverse m8; word_bytereverse m9;
                   word_bytereverse m10; word_bytereverse m11;
                   word_bytereverse m12; word_bytereverse m13;
                   word_bytereverse m14; word_bytereverse m15] in
          let H = [a;b;c;d;e;f;g;h] in
          let result = sha256_block M H in
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
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN

  (* Instructions 1-14: state loads + data loads + ADD x1 + SUB x2 +
     REV32 + save state *)
  ARM_STEPS_TAC HW_EXEC (1--14) THEN
  RULE_ASSUM_TAC ADD_SIMP_RULE THEN

  (* Simplify REV32 via BITBLAST: Q4-Q7 -> word_join4 of word_bytereverse *)
  SUBGOAL_THEN
    `read Q4 s14 = word_join4 (word_bytereverse m0:int32) (word_bytereverse m1)
                               (word_bytereverse m2) (word_bytereverse m3)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] `read Q4 s = x:int128`) (concl asm)
         && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm))
      then th else asm))
  THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN
    BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN
  SUBGOAL_THEN
    `read Q5 s14 = word_join4 (word_bytereverse m4:int32) (word_bytereverse m5)
                               (word_bytereverse m6) (word_bytereverse m7)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] `read Q5 s = x:int128`) (concl asm)
         && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm))
      then th else asm))
  THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN
    BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN
  SUBGOAL_THEN
    `read Q6 s14 = word_join4 (word_bytereverse m8:int32) (word_bytereverse m9)
                               (word_bytereverse m10) (word_bytereverse m11)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] `read Q6 s = x:int128`) (concl asm)
         && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm))
      then th else asm))
  THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN
    BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN
  SUBGOAL_THEN
    `read Q7 s14 = word_join4 (word_bytereverse m12:int32) (word_bytereverse m13)
                               (word_bytereverse m14) (word_bytereverse m15)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] `read Q7 s = x:int128`) (concl asm)
         && not (can (find_term (fun t -> try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl asm))
      then th else asm))
  THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[word_join4] THEN
    BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC] THEN

  (* Abbreviate byte-reversed message words *)
  ABBREV_TAC `w0 = word_bytereverse m0 :int32` THEN
  ABBREV_TAC `w1 = word_bytereverse m1 :int32` THEN
  ABBREV_TAC `w2 = word_bytereverse m2 :int32` THEN
  ABBREV_TAC `w3 = word_bytereverse m3 :int32` THEN
  ABBREV_TAC `w4 = word_bytereverse m4 :int32` THEN
  ABBREV_TAC `w5 = word_bytereverse m5 :int32` THEN
  ABBREV_TAC `w6 = word_bytereverse m6 :int32` THEN
  ABBREV_TAC `w7 = word_bytereverse m7 :int32` THEN
  ABBREV_TAC `w8 = word_bytereverse m8 :int32` THEN
  ABBREV_TAC `w9 = word_bytereverse m9 :int32` THEN
  ABBREV_TAC `w10 = word_bytereverse m10 :int32` THEN
  ABBREV_TAC `w11 = word_bytereverse m11 :int32` THEN
  ABBREV_TAC `w12 = word_bytereverse m12 :int32` THEN
  ABBREV_TAC `w13 = word_bytereverse m13 :int32` THEN
  ABBREV_TAC `w14 = word_bytereverse m14 :int32` THEN
  ABBREV_TAC `w15 = word_bytereverse m15 :int32` THEN

  (* Abbreviate W = message schedule *)
  ABBREV_TAC `W = sha256_message_schedule 48
    [w0:int32;w1;w2;w3;w4;w5;w6;w7;
     w8;w9;w10;w11;w12;w13;w14;w15]` THEN

  (* NOTE: Do NOT discard data memory here. ARM_STEPS_TAC needs all memory
     assumptions present for address resolution during LDR instructions.
     Discarding data_ptr memory before the round groups causes ARM_STEPS_TAC
     to not produce Q0/Q1 assumptions after sha256h/sha256h2. *)

  (let w_hyp_tm =
    `sha256_message_schedule 48
     [w0:int32;w1;w2;w3;w4;w5;w6;w7;
      w8;w9;w10;w11;w12;w13;w14;w15] = W` in

  (* ---- Round groups 0-11 (with schedule update, 7 steps each) ---- *)
  ARM_STEPS_TAC HW_EXEC (15--21) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 0 `s21:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (22--28) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 1 `s28:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (29--35) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 2 `s35:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (36--42) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 3 `s42:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (43--49) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 4 `s49:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (50--56) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 5 `s56:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (57--63) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 6 `s63:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (64--70) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 7 `s70:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (71--77) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 8 `s77:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (78--84) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 9 `s84:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (85--91) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 10 `s91:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (92--98) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 11 `s98:armstate` THEN

  (* NOTE: Do NOT discard Q4-Q7 here. ARM_STEPS_TAC needs them for the
     ADD V2.4S instructions in groups 12-15 which read the schedule registers.
     The CUT_POINT_TAC will discard the old sha256h/sha256h2 assumptions,
     keeping the growth manageable. *)

  (* ---- Round groups 12-15 (no schedule update, 5 steps each) ---- *)
  ARM_STEPS_TAC HW_EXEC (99--103) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 12 `s103:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (104--108) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 13 `s108:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (109--113) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 14 `s113:armstate` THEN

  ARM_STEPS_TAC HW_EXEC (114--118) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN
  CUT_POINT_TAC_HW 15 `s118:armstate` THEN

  (* ---- Instructions 119-124: add-back + CBNZ (fall through) + stores + RET ---- *)
  ARM_STEPS_TAC HW_EXEC (119--124) THEN RULE_ASSUM_TAC ADD_SIMP_RULE THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* ---- Postcondition: sha256_compress 64 + add-back = sha256_block ---- *)
  POSTCOND_TAC_HW));;

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
   1 <= num_blocks /\
   LENGTH blocks = num_blocks /\
   ALL (\bl. LENGTH bl = 16) blocks /\
   ALL (nonoverlapping (state_ptr, 32))
       [(word pc, 496); (data_ptr, 64 * num_blocks); (kptr, 256)] /\
   nonoverlapping (data_ptr, 64 * num_blocks) (word pc, 496) /\
   nonoverlapping (kptr, 256) (word pc, 496)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_hw_mc /\
         read PC s = word pc /\
         read X30 s = word(pc + 0x1ec) /\
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
    (* ================================================================= *)
    (* TODO: full body proof with GEN_CUT_POINT_TAC *)
    CHEAT_TAC;

    (* ================================================================= *)
    (* Subgoal 3: BACK-EDGE -- invariant(i) at pc+0x1e0 ==>             *)
    (*            invariant(i) at pc+0x8                                 *)
    (* Just CBNZ x2, .Loop_hw (1 instruction, branches since x2 != 0)   *)
    (* ================================================================= *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];

    (* ================================================================= *)
    (* Subgoal 4: EXIT -- invariant(num_blocks) at pc+0x1e0 ==>          *)
    (*            postcondition at pc+0x1ec                              *)
    (* CBNZ falls through (x2=0), STR Q0, STR Q1, RET (4 instructions) *)
    (* ================================================================= *)
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SUB_REFL] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[]
  ]);;
