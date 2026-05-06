(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-512 multi-block hardware-accelerated function.                        *)
(*                                                                           *)
(* Proves correctness of sha512_block_data_order_hw, which processes         *)
(* num_blocks consecutive 1024-bit message blocks using ARMv8.2 FEAT_SHA512  *)
(* hardware instructions (SHA512H/SHA512H2/SHA512SU0/SHA512SU1).             *)
(*                                                                           *)
(* void sha512_block_data_order_hw(uint64_t state[8],                        *)
(*                                 const uint8_t *data,                      *)
(*                                 uint64_t num_blocks,                      *)
(*                                 const uint64_t K[80])                     *)
(*                                                                           *)
(* The proof mirrors sha256_block_data_order_hw.ml: it reuses the cut-point  *)
(* infrastructure from sha512_block_core.ml (CUT_POINT_TAC_512, GROUP_BRIDGE *)
(* lemmas, EL_W lists) and wraps it in ENSURES_WHILE_UP_TAC for the outer    *)
(* block loop.                                                               *)
(* ========================================================================= *)

needs "arm/proofs/sha512_block_core.ml";;

(* ========================================================================= *)
(* Machine code and execution rule.                                          *)
(* ========================================================================= *)

let sha512_hw_mc = define_from_elf "sha512_hw_mc"
  (file_on_path !load_path "arm/sha2/sha512_block_data_order_hw.o");;

let HW_EXEC = ARM_MK_EXEC_RULE sha512_hw_mc;;

(* ========================================================================= *)
(* Helpers mirroring the SHA-256 hw pilot.                                   *)
(* ========================================================================= *)

let WORD_SUB_SUC = prove
 (`!n. word_sub (word(SUC n):int64) (word 1) = word n`,
  GEN_TAC THEN REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE);;

let WORD_ADVANCE_128 = WORD_RULE
 `word_add (word_add d (word(128 * ii):int64)) (word 128) =
  word_add d (word(128 * (ii + 1)))`;;

(* REV64_BITBLAST_TAC: after REV64 V16.16B instruction, Q16's 128-bit value
   is byte-reversed lane-by-lane on 2x64-bit halves. If the pre-state Q16
   held `word_join (word_bytereverse w1) (word_bytereverse w0)` (what a raw
   LDR Q from LE memory gives when the logical SHA-512 message words w0, w1
   are stored in BE byte order), the post-REV64 Q16 holds `word_join w1 w0`.

   Pattern analogous to REV32_BITBLAST_TAC in the SHA-256 pilot, but the
   `is_clean_wj_rhs` check is tighter: after ARM_STEPS_TAC unfolds the
   usimd2/4/8 definitions, the expanded Q hypothesis still has an outer
   `word_join`, so the SHA-256 check (outermost constructor = word_join)
   doesn't distinguish "already cleaned" from "freshly expanded". We
   therefore require the word_join's first argument to be headed by EL,
   i.e. the clean `word_join (EL k1 ...) (EL k0 ...)` form. *)

let REV64_BITBLAST_TAC qpat qtm =
  let is_clean_wj_rhs th =
    try
      let _,rhs = dest_eq (concl th) in
      let hd,args = strip_comb rhs in
      fst(dest_const hd) = "word_join" &&
      List.length args = 2 &&
      (try let ell,_ = strip_comb(List.nth args 0) in
           fst(dest_const ell) = "EL"
       with _ -> false)
    with _ -> false in
  SUBGOAL_THEN qtm
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] qpat) (concl asm) && not(is_clean_wj_rhs asm)
      then th else asm))
  THENL
   [ASM_REWRITE_TAC[] THEN
    BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT; ALL_TAC];;

(* LENGTH destructuring for 16-element data blocks (same shape as SHA-256). *)

let LENGTH_16_CONS_512 = prove
 (`!L:A list. LENGTH L = 16
   ==> ?a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15.
       L = [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15]`,
  let suc16 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC
      (SUC(SUC(SUC(SUC 0)))))))))))))))` in
  REWRITE_TAC[GSYM suc16; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_16_EL_512 = prove
 (`!L:A list. LENGTH L = 16 ==>
    L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L; EL 4 L; EL 5 L; EL 6 L; EL 7 L;
         EL 8 L; EL 9 L; EL 10 L; EL 11 L; EL 12 L; EL 13 L; EL 14 L;
         EL 15 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_16_CONS_512) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let RECONSTRUCT_BLOCK_TAC_512 =
  SUBGOAL_THEN
    `EL ii blocks = [w0:int64;w1;w2;w3;w4;w5;w6;w7;
                     w8;w9;w10;w11;w12;w13;w14;w15]`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC
      ["w0";"w1";"w2";"w3";"w4";"w5";"w6";"w7";
       "w8";"w9";"w10";"w11";"w12";"w13";"w14";"w15"] THEN
    MATCH_MP_TAC LIST_16_EL_512 THEN
    UNDISCH_TAC `ALL (\bl:int64 list. LENGTH bl = 16) blocks` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC];;

(* EXPAND_K_TAC_512: specialize the quantified K table at 40 values k=0..39,
   each chunk being `word_join (EL (2k+1) sha512_K) (EL (2k) sha512_K)`.
   We keep the quantified assumption around (FIRST_ASSUM) so it survives to
   the postcondition. *)

let EXPAND_K_TAC_512 =
  FIRST_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "sha512_K" with _ -> false)) (concl th)
    then
      MAP_EVERY (fun i ->
        let spec = SPEC (mk_small_numeral i) th in
        let mp = MP spec (prove(lhand(concl spec), ARITH_TAC)) in
        ASSUME_TAC(CONV_RULE
          (DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) mp))
        (0--39)
    else FAIL_TAC "");;

(* EXPAND_DATA_TAC_512: specialize the quantified data memory at j=ii and
   further at each of l=0..7, normalizing 128*ii + 16*l to its concrete
   offset form so the simulator can resolve LDR Q16-Q23 addresses. The
   SHA-256 analogue didn't need per-l specialization because its memory
   hypothesis was a fixed 4-way conjunction of four LDRs per block; the
   SHA-512 hypothesis is `!l. l<8 ==> ...` which must be unfolded per-l.
   REWRITE_CONV[ADD_CLAUSES] reduces `128*ii + 0` to `128*ii` (needed for
   the l=0 LDR to match X1 = data_ptr + 128*ii). *)

let EXPAND_DATA_TAC_512 =
  FIRST_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl th)
    then
      MP_TAC(SPEC `ii:num` th) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN (fun dth ->
          MAP_EVERY (fun l ->
            let sp = SPEC (mk_small_numeral l) dth in
            let mp = MP sp (prove(lhand(concl sp), ARITH_TAC)) in
            ASSUME_TAC (CONV_RULE
              (DEPTH_CONV NUM_MULT_CONV THENC
               DEPTH_CONV NUM_ADD_CONV THENC
               REWRITE_CONV[ADD_CLAUSES]) mp))
            (0--7))]
    else FAIL_TAC "");;

(* ========================================================================= *)
(* Generalised CUT_POINT_TAC_512 taking the initial hash state h_tm as a     *)
(* parameter. For the multi-block body proof, h_tm is                        *)
(*   sha512_hash_blocks ii blocks [a;b;c;d;e;f;g;h]                          *)
(* (an opaque int64 list of length 8).                                       *)
(*                                                                           *)
(* Structurally identical to CUT_POINT_TAC_512 in sha512_block_core.ml but   *)
(* substitutes h_tm wherever the core proof used `[a;b;c;d;e;f;g;h]`.         *)
(* The opaque-letter abbreviations (a_{i+1}, b_{i+1}, e_{i+1}, f_{i+1}) are  *)
(* still used to keep per-instruction ARM_STEPS_TAC cost linear.             *)
(* ========================================================================= *)

let GEN_SHIFT2_RULE h_tm =
  let l_name = "_hlist_" in
  let l_var = mk_var(l_name, `:int64 list`) in
  fun n ->
    let th = SPEC_ALL SHA512_COMPRESS_SHIFT2 in
    let th1 = INST [mk_small_numeral n, `n:num`;
                    h_tm, `state:int64 list`] th in
    let len_hyp = lhand(concl th1) in
    let len_th = prove(len_hyp,
      REWRITE_TAC[LENGTH_SHA512_HASH_BLOCKS; LENGTH] THEN
      TRY (MATCH_MP_TAC LENGTH_SHA512_HASH_BLOCKS) THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
    ignore l_var;
    CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV) (MP th1 len_th);;

let GEN_abbrev_compress_el_tac h_tm i k_name pos =
  let tgt_n = 2*(i+1) in
  let tgt = mk_small_numeral tgt_n in
  let pos_tm = mk_small_numeral pos in
  let letter = cut_letter_name k_name i in
  let rhs_template =
    `EL p (sha512_compress t W (H:int64 list))` in
  let rhs = subst [tgt,`t:num`; pos_tm,`p:num`; h_tm,`H:int64 list`]
    rhs_template in
  let eq_tm = mk_eq(mk_var(letter,`:int64`), rhs) in
  ABBREV_TAC eq_tm;;

let GEN_CUT_POINT_TAC_512 h_tm i sname =
  let p = i mod 5 in
  let q_res = mk_const("Q" ^ string_of_int phase_res_arr_512.(p),[]) in
  let q_mid = mk_const("Q" ^ string_of_int phase_mid_arr_512.(p),[]) in
  let bridge_h = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int64 list`; h_tm] GROUP_BRIDGE_H512.(i)) in
  let bridge_mid = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`W:int64 list`; h_tm] GROUP_BRIDGE_MID.(i)) in
  let shift2_thm =
    if i = 0 then TRUTH
    else GEN_SHIFT2_RULE h_tm (2*(i-1)) in
  let el_w_local = [List.nth EL_W_ALL_LIST_512 (2*i);
                    List.nth EL_W_ALL_LIST_512 (2*i+1)] in
  let target_n = 2 * (i + 1) in
  let target = mk_small_numeral target_n in
  (* Build the cut goal terms programmatically so that all types are
     concrete. Starting from a quoted template with abstract `s` leaves a
     fresh type variable after subst, which then type-mismatches the
     assumption-list entries. *)
  let read_const =
    `read:(armstate,int128)component->armstate->int128` in
  let word_join_c = `word_join:int64->int64->int128` in
  let mk_q_cut_tm qcomp hi lo =
    let compress_tm =
      list_mk_icomb "sha512_compress" [target; `W:int64 list`; h_tm] in
    let el_hi = list_mk_icomb "EL" [mk_small_numeral hi; compress_tm] in
    let el_lo = list_mk_icomb "EL" [mk_small_numeral lo; compress_tm] in
    let wj = mk_comb(mk_comb(word_join_c, el_hi), el_lo) in
    mk_eq(mk_comb(mk_comb(read_const, qcomp), sname), wj) in
  let q_res_tm_full = mk_q_cut_tm q_res 1 0 in
  let q_mid_tm_full = mk_q_cut_tm q_mid 5 4 in
  let CUT_SUBGOAL_TAC bridge =
    ASM_REWRITE_TAC[bridge] THEN
    REWRITE_TAC[shift2_thm] THEN
    REWRITE_TAC[CONJUNCT1 sha512_compress] THEN
    (* EL_CONV can reduce EL over concrete lists but fails on opaque
       sha512_hash_blocks applications; wrap in TRY so the i=0 case
       (where h_tm is opaque) doesn't blow up. *)
    TRY(CONV_TAC(DEPTH_CONV EL_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC el_w_local THEN
    REFL_TAC in
  SUBGOAL_THEN q_res_tm_full ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h; ALL_TAC] THEN
  SUBGOAL_THEN q_mid_tm_full ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_mid; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let n = fst(dest_const t) in n = "sha512h" || n = "sha512h2"
      with _ -> false)) (concl th)))) THEN
  GEN_abbrev_compress_el_tac h_tm i "a" 0 THEN
  GEN_abbrev_compress_el_tac h_tm i "b" 1 THEN
  GEN_abbrev_compress_el_tac h_tm i "e" 4 THEN
  GEN_abbrev_compress_el_tac h_tm i "f" 5 THEN
  (if i < 32 then
    (let prefix_gsyms =
       List.init 16 (fun k -> GSYM (List.nth EL_W_ALL_LIST_512 k)) in
     let step_folds =
       [GSYM (List.nth EL_W_STEP_LIST_512 (2*i));
        GSYM (List.nth EL_W_STEP_LIST_512 (2*i+1))] in
     RULE_ASSUM_TAC(fun th ->
       if can (find_term (fun t ->
           try fst(dest_const t) = "sha512su1" with _ -> false)) (concl th)
       then REWRITE_RULE step_folds
              (REWRITE_RULE prefix_gsyms
                (REWRITE_RULE [SHA512SU_BRIDGE_FLAT] th))
       else th))
   else ALL_TAC);;

(* ========================================================================= *)
(* Main correctness theorem.                                                 *)
(*                                                                           *)
(* PC offsets (from objdump -d sha512_block_data_order_hw.o):                *)
(*   entry:    0x000                                                         *)
(*   loop top: 0x010   (after 4 state LDRs)                                  *)
(*   cbnz:     0x798   (branches back to 0x010 if X2 != 0)                   *)
(*   ret:      0x7ac   (after 4 state STRs)                                  *)
(*   function length: 0x7b0 = 1968 bytes                                     *)
(* ========================================================================= *)

let SHA512_HW_CORRECT = prove
 (`!num_blocks state_ptr data_ptr kptr
    (a:int64) b c d (e:int64) f g h
    (blocks:(int64 list) list) pc.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    ALL (nonoverlapping (state_ptr, 64))
        [(word pc, 1968); (data_ptr, 128 * num_blocks); (kptr, 640)] /\
    nonoverlapping (data_ptr, 128 * num_blocks) (word pc, 1968) /\
    nonoverlapping (kptr, 640) (word pc, 1968)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha512_hw_mc /\
          read PC s = word pc /\
          read X0 s = state_ptr /\
          read X1 s = data_ptr /\
          read X2 s = word num_blocks /\
          read X3 s = kptr /\
          read (memory :> bytes128 state_ptr) s =
            (word_join:int64->int64->int128) b a /\
          read (memory :> bytes128 (word_add state_ptr (word 16))) s =
            (word_join:int64->int64->int128) d c /\
          read (memory :> bytes128 (word_add state_ptr (word 32))) s =
            (word_join:int64->int64->int128) f e /\
          read (memory :> bytes128 (word_add state_ptr (word 48))) s =
            (word_join:int64->int64->int128) h g /\
          (!j. j < num_blocks ==>
            (!l. l < 8 ==>
              read (memory :> bytes128
                     (word_add data_ptr (word(128 * j + 16 * l)))) s =
              (word_join:int64->int64->int128)
                (word_bytereverse (EL (2*l+1) (EL j blocks)))
                (word_bytereverse (EL (2*l) (EL j blocks))))) /\
          (!k. k < 40 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * k)))) s =
            (word_join:int64->int64->int128)
              (EL (2*k+1) sha512_K) (EL (2*k) sha512_K)))
     (\s. read PC s = word(pc + 0x7ac) /\
          (let result =
             sha512_hash_blocks num_blocks blocks [a;b;c;d;e;f;g;h] in
           read (memory :> bytes128 state_ptr) s =
             (word_join:int64->int64->int128) (EL 1 result) (EL 0 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 16))) s =
             (word_join:int64->int64->int128) (EL 3 result) (EL 2 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 32))) s =
             (word_join:int64->int64->int128) (EL 5 result) (EL 4 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 48))) s =
             (word_join:int64->int64->int128) (EL 7 result) (EL 6 result)))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                 Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24;
                 Q28; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(state_ptr, 64)] ,,
      MAYCHANGE [events])`,

  REWRITE_TAC[ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `~(num_blocks = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN

  ENSURES_WHILE_UP_TAC `num_blocks:num` `pc + 0x10` `pc + 0x798`
    `\i s. aligned_bytes_loaded s (word pc) sha512_hw_mc /\
           read X0 s = state_ptr /\
           read X1 s = word_add data_ptr (word(128 * i)) /\
           read X2 s = word(num_blocks - i) /\
           read X3 s = kptr /\
           read Q0 s = (word_join:int64->int64->int128)
             (EL 1 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h]:int64 list))
             (EL 0 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h])) /\
           read Q1 s = (word_join:int64->int64->int128)
             (EL 3 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h]:int64 list))
             (EL 2 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h])) /\
           read Q2 s = (word_join:int64->int64->int128)
             (EL 5 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h]:int64 list))
             (EL 4 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h])) /\
           read Q3 s = (word_join:int64->int64->int128)
             (EL 7 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h]:int64 list))
             (EL 6 (sha512_hash_blocks i blocks [a;b;c;d;e;f;g;h])) /\
           (!j. j < num_blocks ==>
             (!l. l < 8 ==>
               read (memory :> bytes128
                      (word_add data_ptr (word(128 * j + 16 * l)))) s =
               (word_join:int64->int64->int128)
                 (word_bytereverse (EL (2*l+1) (EL j blocks)))
                 (word_bytereverse (EL (2*l) (EL j blocks))))) /\
           (!k. k < 40 ==>
             read (memory :> bytes128 (word_add kptr (word(16 * k)))) s =
             (word_join:int64->int64->int128)
               (EL (2*k+1) sha512_K) (EL (2*k) sha512_K)) /\
           read (memory :> bytes128 state_ptr) s =
             (word_join:int64->int64->int128) b a /\
           read (memory :> bytes128 (word_add state_ptr (word 16))) s =
             (word_join:int64->int64->int128) d c /\
           read (memory :> bytes128 (word_add state_ptr (word 32))) s =
             (word_join:int64->int64->int128) f e /\
           read (memory :> bytes128 (word_add state_ptr (word 48))) s =
             (word_join:int64->int64->int128) h g` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [

    (* ================================================================= *)
    (* Subgoal 1: INIT -- precondition ==> invariant(0) at pc+0x10       *)
    (* Execute instructions 1-4 (LDR Q0-Q3).                             *)
    (* ================================================================= *)
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[sha512_hash_blocks; WORD_ADD_0; MULT_CLAUSES; SUB_0] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];

    (* ================================================================= *)
    (* Subgoal 2: BODY -- invariant(ii) at pc+0x10 ==>                   *)
    (*            invariant(ii+1) at pc+0x798                            *)
    (*                                                                   *)
    (* 482 ARM steps, 40 cut-points. Prefix = 22 instrs (8 LDR Q +       *)
    (* ADD X1 + SUB X2 + 8 REV64 + 4 MOV Q28-Q31); then 32 x 12-instr    *)
    (* groups + 8 x 9-instr groups (no SU); finally 4 ADD add-back.      *)
    (* ================================================================= *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `num_blocks - ii < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `num_blocks - ii` THEN
    ENSURES_INIT_TAC "s0" THEN
    EXPAND_K_TAC_512 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    EXPAND_DATA_TAC_512 THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
    ARM_STEPS_TAC HW_EXEC (1--22) THEN
    REV64_BITBLAST_TAC `read Q16 s = x:int128`
      `read Q16 s22 = (word_join:int64->int64->int128)
        (EL 1 (EL ii blocks):int64) (EL 0 (EL ii blocks))` THEN
    REV64_BITBLAST_TAC `read Q17 s = x:int128`
      `read Q17 s22 = (word_join:int64->int64->int128)
        (EL 3 (EL ii blocks):int64) (EL 2 (EL ii blocks))` THEN
    REV64_BITBLAST_TAC `read Q18 s = x:int128`
      `read Q18 s22 = (word_join:int64->int64->int128)
        (EL 5 (EL ii blocks):int64) (EL 4 (EL ii blocks))` THEN
    REV64_BITBLAST_TAC `read Q19 s = x:int128`
      `read Q19 s22 = (word_join:int64->int64->int128)
        (EL 7 (EL ii blocks):int64) (EL 6 (EL ii blocks))` THEN
    REV64_BITBLAST_TAC `read Q20 s = x:int128`
      `read Q20 s22 = (word_join:int64->int64->int128)
        (EL 9 (EL ii blocks):int64) (EL 8 (EL ii blocks))` THEN
    REV64_BITBLAST_TAC `read Q21 s = x:int128`
      `read Q21 s22 = (word_join:int64->int64->int128)
        (EL 11 (EL ii blocks):int64) (EL 10 (EL ii blocks))` THEN
    REV64_BITBLAST_TAC `read Q22 s = x:int128`
      `read Q22 s22 = (word_join:int64->int64->int128)
        (EL 13 (EL ii blocks):int64) (EL 12 (EL ii blocks))` THEN
    REV64_BITBLAST_TAC `read Q23 s = x:int128`
      `read Q23 s22 = (word_join:int64->int64->int128)
        (EL 15 (EL ii blocks):int64) (EL 14 (EL ii blocks))` THEN
    ABBREV_TAC `w0 = (EL 0 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w1 = (EL 1 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w2 = (EL 2 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w3 = (EL 3 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w4 = (EL 4 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w5 = (EL 5 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w6 = (EL 6 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w7 = (EL 7 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w8 = (EL 8 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w9 = (EL 9 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w10 = (EL 10 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w11 = (EL 11 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w12 = (EL 12 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w13 = (EL 13 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w14 = (EL 14 (EL ii blocks)):int64` THEN
    ABBREV_TAC `w15 = (EL 15 (EL ii blocks)):int64` THEN
    ABBREV_TAC `W = sha512_message_schedule 64
      [w0:int64;w1;w2;w3;w4;w5;w6;w7;
       w8;w9;w10;w11;w12;w13;w14;w15]` THEN
    (let h_tm = `sha512_hash_blocks ii blocks [a:int64;b;c;d;e;f;g;h]` in
    ARM_STEPS_TAC HW_EXEC (23--34) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 0 `s34:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (35--46) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 1 `s46:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (47--58) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 2 `s58:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (59--70) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 3 `s70:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (71--82) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 4 `s82:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (83--94) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 5 `s94:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (95--106) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 6 `s106:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (107--118) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 7 `s118:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (119--130) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 8 `s130:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (131--142) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 9 `s142:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (143--154) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 10 `s154:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (155--166) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 11 `s166:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (167--178) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 12 `s178:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (179--190) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 13 `s190:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (191--202) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 14 `s202:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (203--214) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 15 `s214:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (215--226) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 16 `s226:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (227--238) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 17 `s238:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (239--250) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 18 `s250:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (251--262) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 19 `s262:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (263--274) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 20 `s274:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (275--286) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 21 `s286:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (287--298) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 22 `s298:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (299--310) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 23 `s310:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (311--322) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 24 `s322:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (323--334) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 25 `s334:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (335--346) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 26 `s346:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (347--358) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 27 `s358:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (359--370) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 28 `s370:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (371--382) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 29 `s382:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (383--394) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 30 `s394:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (395--406) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 31 `s406:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (407--415) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 32 `s415:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (416--424) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 33 `s424:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (425--433) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 34 `s433:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (434--442) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 35 `s442:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (443--451) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 36 `s451:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (452--460) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 37 `s460:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (461--469) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 38 `s469:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (470--478) THEN RULE_ASSUM_TAC ADD_SIMP_RULE_512 THEN
      GEN_CUT_POINT_TAC_512 h_tm 39 `s478:armstate` THEN
    ARM_STEPS_TAC HW_EXEC (479--482) THEN
    ENSURES_FINAL_STATE_TAC THEN
    RECONSTRUCT_BLOCK_TAC_512 THEN
    (let len_h = prove(
       `LENGTH(sha512_hash_blocks ii blocks [a:int64;b;c;d;e;f;g;h]) = 8`,
       MATCH_MP_TAC LENGTH_SHA512_HASH_BLOCKS THEN
       REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
     let block_el = List.map (fun k ->
       let th = SPEC (mk_small_numeral k)
         (MP (SPECL [`[w0:int64;w1;w2;w3;w4;w5;w6;w7;
                       w8;w9;w10;w11;w12;w13;w14;w15]`; h_tm]
                     SHA512_BLOCK_EL) len_h) in
       let th2 = MP th (prove(lhand(concl th), ARITH_TAC)) in
       try CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2
       with _ -> th2) (0--7) in
     let shift2_78 = GEN_SHIFT2_RULE h_tm 78 in
     (* Postcondition closure (see feedback_sha512_postcond_closure.md):
        unfold only sha512_hash_blocks (step form), then let SHA512_BLOCK_EL
        do the MAP2 rewriting lazily via pre-built block_el. *)
     ASM_REWRITE_TAC[sha512_hash_blocks] THEN
     ASM_REWRITE_TAC(WORD_JOIN_64_HI_LO :: block_el) THEN
     REWRITE_TAC[shift2_78] THEN
     ASM_REWRITE_TAC[WORD_ADVANCE_128] THEN
     SUBGOAL_THEN `num_blocks - ii = SUC(num_blocks - (ii + 1))`
       SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[WORD_SUB_SUC]]));


    (* ================================================================= *)
    (* Subgoal 3: BACK-EDGE -- invariant(i) at pc+0x798 ==>              *)
    (*            invariant(i) at pc+0x10                                *)
    (* CBNZ branches back since num_blocks - i != 0.                     *)
    (* ================================================================= *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    VAL_INT64_TAC `num_blocks - ii` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

    (* ================================================================= *)
    (* Subgoal 4: EXIT -- invariant(num_blocks) at pc+0x798 ==>          *)
    (*            postcondition at pc+0x7ac                              *)
    (* CBNZ falls through (X2 = 0) + 4 STR Q (5 instructions).          *)
    (* RET not executed here; handled by SUBROUTINE_CORRECT wrapper.     *)
    (* ================================================================= *)
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                NONOVERLAPPING_CLAUSES; SUB_REFL] THEN
    VAL_INT64_TAC `num_blocks - num_blocks` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC HW_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[]
  ]);;

(* ========================================================================= *)
(* Subroutine wrapper.                                                        *)
(*                                                                           *)
(* No stack prologue / no callee-saved registers, so                         *)
(* ARM_ADD_RETURN_NOSTACK_TAC is the right combinator (same choice as        *)
(* SHA-256 hw).                                                              *)
(* ========================================================================= *)

let SHA512_HW_SUBROUTINE_CORRECT = prove
 (`!num_blocks state_ptr data_ptr kptr
    (a:int64) b c d (e:int64) f g h
    (blocks:(int64 list) list) pc returnaddress.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    ALL (nonoverlapping (state_ptr, 64))
        [(word pc, 1968); (data_ptr, 128 * num_blocks); (kptr, 640)] /\
    nonoverlapping (data_ptr, 128 * num_blocks) (word pc, 1968) /\
    nonoverlapping (kptr, 640) (word pc, 1968)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha512_hw_mc /\
          read PC s = word pc /\
          read X30 s = returnaddress /\
          read X0 s = state_ptr /\
          read X1 s = data_ptr /\
          read X2 s = word num_blocks /\
          read X3 s = kptr /\
          read (memory :> bytes128 state_ptr) s =
            (word_join:int64->int64->int128) b a /\
          read (memory :> bytes128 (word_add state_ptr (word 16))) s =
            (word_join:int64->int64->int128) d c /\
          read (memory :> bytes128 (word_add state_ptr (word 32))) s =
            (word_join:int64->int64->int128) f e /\
          read (memory :> bytes128 (word_add state_ptr (word 48))) s =
            (word_join:int64->int64->int128) h g /\
          (!j. j < num_blocks ==>
            (!l. l < 8 ==>
              read (memory :> bytes128
                     (word_add data_ptr (word(128 * j + 16 * l)))) s =
              (word_join:int64->int64->int128)
                (word_bytereverse (EL (2*l+1) (EL j blocks)))
                (word_bytereverse (EL (2*l) (EL j blocks))))) /\
          (!k. k < 40 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * k)))) s =
            (word_join:int64->int64->int128)
              (EL (2*k+1) sha512_K) (EL (2*k) sha512_K)))
     (\s. read PC s = returnaddress /\
          (let result =
             sha512_hash_blocks num_blocks blocks [a;b;c;d;e;f;g;h] in
           read (memory :> bytes128 state_ptr) s =
             (word_join:int64->int64->int128) (EL 1 result) (EL 0 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 16))) s =
             (word_join:int64->int64->int128) (EL 3 result) (EL 2 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 32))) s =
             (word_join:int64->int64->int128) (EL 5 result) (EL 4 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 48))) s =
             (word_join:int64->int64->int128) (EL 7 result) (EL 6 result)))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(state_ptr, 64)])`,
  ARM_ADD_RETURN_NOSTACK_TAC HW_EXEC SHA512_HW_CORRECT);;
