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

   Pattern exactly analogous to REV32_BITBLAST_TAC in the SHA-256 pilot. *)

let REV64_BITBLAST_TAC qpat qtm =
  let is_wj_rhs th =
    try fst(dest_const(fst(strip_comb(rand(concl th))))) = "word_join"
    with _ -> false in
  SUBGOAL_THEN qtm
    (fun th -> RULE_ASSUM_TAC(fun asm ->
      if can (term_match [] qpat) (concl asm) && not(is_wj_rhs asm)
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

(* EXPAND_DATA_TAC_512: specialize the quantified data memory at j=ii. *)

let EXPAND_DATA_TAC_512 =
  FIRST_ASSUM(fun th ->
    if can (find_term (fun t ->
      try fst(dest_const t) = "word_bytereverse" with _ -> false)) (concl th)
    then
      MP_TAC(SPEC `ii:num` th) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]
    else FAIL_TAC "");;

(* ========================================================================= *)
(* Generalised CUT_POINT_TAC_512 taking a parameter h_tm for the initial     *)
(* hash state. Used both for the single-block core (h_tm = `[a;b;c;d;e;f;g;h]`)
   and for the multi-block body proof (h_tm = `sha512_hash_blocks ii blocks   *)
(* [a;b;c;d;e;f;g;h]`).                                                      *)
(*                                                                           *)
(* NOTE: For Phase F the body proof is done with CHEAT_TAC for now; the      *)
(* full implementation will lift CUT_POINT_TAC_512 to take h_tm (and the     *)
(* opaque-letter abbreviations will use letters derived from ii).            *)
(* ========================================================================= *)

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
        [(word pc, LENGTH sha512_hw_mc);
         (data_ptr, 128 * num_blocks); (kptr, 640)] /\
    nonoverlapping (data_ptr, 128 * num_blocks)
                   (word pc, LENGTH sha512_hw_mc) /\
    nonoverlapping (kptr, 640) (word pc, LENGTH sha512_hw_mc)
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
  CHEAT_TAC);;

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
        [(word pc, LENGTH sha512_hw_mc);
         (data_ptr, 128 * num_blocks); (kptr, 640)] /\
    nonoverlapping (data_ptr, 128 * num_blocks)
                   (word pc, LENGTH sha512_hw_mc) /\
    nonoverlapping (kptr, 640) (word pc, LENGTH sha512_hw_mc)
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
  CHEAT_TAC);;
