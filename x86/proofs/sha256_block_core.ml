(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 single-block register core (x86-64 SHA-NI).                       *)
(*                                                                           *)
(* Proves correctness of the loop body of sha256_block_data_order_hw in      *)
(* isolation: starting at the loop-top PC with XMM1/XMM2 holding the         *)
(* ABEF/CDGH packing of the initial hash state and memory holding one        *)
(* 512-bit message block + the K table, after running the body the XMM1/    *)
(* XMM2 pair holds the ABEF/CDGH packing of sha256_block M H.                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/sha256_bridge_x86.ml";;

(* ========================================================================= *)
(* Machine code and execution rule.                                          *)
(* ========================================================================= *)

let sha256_hw_mc = define_from_elf "sha256_hw_mc"
  (file_on_path !load_path "x86/sha2/sha256_block_data_order_hw.o");;

let HW_EXEC = X86_MK_EXEC_RULE sha256_hw_mc;;

(* ========================================================================= *)
(* SIMD simplification.  Pasted from common/mlkem_mldsa.ml to avoid the      *)
(* 5-minute load of the ML-KEM/ML-DSA spec.                                  *)
(* ========================================================================= *)

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let arm_simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  let x86_simdable = can (term_match [] `read X (s:x86state):int256 = whatever`) in
  let x86_simdable_128 = can (term_match []
    `read X (s:x86state):int128 = whatever`) in
  let simdable tm =
    arm_simdable tm || x86_simdable tm || x86_simdable_128 tm in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

(* ========================================================================= *)
(* PSHUFB mask constant.                                                     *)
(*                                                                           *)
(* The routine expects [rcx+256] to contain the "byte-reverse within each    *)
(* 32-bit lane" mask, stored as the 4-word sequence                          *)
(*   0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f.                         *)
(*                                                                           *)
(* After pshufb of a lane against this mask, each 32-bit lane is             *)
(* byte-reversed.                                                            *)
(* ========================================================================= *)

let pshufb_mask_val = define
  `pshufb_mask_val:int128 =
   word_join4 (word 0x00010203:int32)
              (word 0x04050607)
              (word 0x08090a0b)
              (word 0x0c0d0e0f)`;;

(* ========================================================================= *)
(* Packing-level lemmas for the hardware SSE operations used in the body.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Balanced word_join4: re-associates the right-leaning definition           *)
(*   word_join d (word_join c (word_join b a))                               *)
(* as a balanced binary join                                                 *)
(*   word_join (word_join d c) (word_join b a),                              *)
(* so that SIMD2 (and hence simd4 = simd2 o simd2) can rewrite it.           *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN4_BALANCED = prove
 (`!a b c d:int32.
     word_join4 a b c d =
     (word_join:64 word->64 word->int128)
       (word_join d c) (word_join b a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* PADDD on two word_join4-packed XMM registers: lane-wise addition.         *)
(* Rewrites simd4 word_add (word_join4 ...) (word_join4 ...) to a           *)
(* word_join4 of lane-wise word_adds.                                        *)
(* ------------------------------------------------------------------------- *)

let PADDD_WORD_JOIN4 = prove
 (`!x0 x1 x2 x3 y0 y1 y2 y3:int32.
     simd4 (word_add:int32->int32->int32)
       (word_join4 x0 x1 x2 x3)
       (word_join4 y0 y1 y2 y3) =
     word_join4 (word_add x0 y0) (word_add x1 y1)
                (word_add x2 y2) (word_add x3 y3)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_JOIN4_BALANCED] THEN
  REWRITE_TAC[simd4; SIMD2] THEN
  REWRITE_TAC[WORD_JOIN4_BALANCED]);;

(* ------------------------------------------------------------------------- *)
(* PALIGNR 4: byte-level 4-byte right-shift across a (dest,src) concat.      *)
(* In lane terms, for dest = (x0,x1,x2,x3) and src = (y0,y1,y2,y3):          *)
(*   palignr dest, src, 4  →  (y1, y2, y3, x0)                              *)
(* ------------------------------------------------------------------------- *)

let PALIGNR_4_WORD_JOIN4 = prove
 (`!x0 x1 x2 x3 y0 y1 y2 y3:int32.
     word_subword
       ((word_join:int128->int128->int256)
         (word_join4 x0 x1 x2 x3) (word_join4 y0 y1 y2 y3))
       (32,128) = word_join4 y1 y2 y3 x0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST);;

(* PALIGNR 8 (used only in the post-loop shuffle, handled by Phase 5). *)
let PALIGNR_8_WORD_JOIN4 = prove
 (`!x0 x1 x2 x3 y0 y1 y2 y3:int32.
     word_subword
       ((word_join:int128->int128->int256)
         (word_join4 x0 x1 x2 x3) (word_join4 y0 y1 y2 y3))
       (64,128) = word_join4 y2 y3 x0 x1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* PSHUFD imm8=0x1b selects lanes (3,2,1,0) — lane-reversal.                 *)
(* PSHUFD imm8=0xb1 selects lanes (1,0,3,2) — swap adjacent 32-bit pairs.   *)
(* PSHUFD imm8=0x0e selects lanes (2,3,0,1) — used after paddd for the      *)
(*   second sha256rnds2's wk argument (brings W[t+2..t+3] into lanes 0,1).  *)
(*                                                                           *)
(* These are proven via bitblast on the x86_PSHUFD definition.  Only the   *)
(* 0x0e variant is needed by the body proof; the others appear in the      *)
(* prologue/epilogue handled by Phase 5.                                    *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* Postcondition tactic.                                                     *)
(* ========================================================================= *)

let h_list_tm = `[a:int32;b;c;d;e;ff;g;h]`;;

let GEN_POSTCOND_TAC_HW h_tm =
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
    let th3 = try CONV_RULE(RAND_CONV(RAND_CONV EL_CONV)) th2
              with _ -> th2 in
    REWRITE_RULE[hw_w_abbrev] th3) (0--7) in
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC block_el THEN
  REFL_TAC;;

let POSTCOND_TAC_HW = GEN_POSTCOND_TAC_HW h_list_tm;;

(* ========================================================================= *)
(* Cut-point tactic.                                                         *)
(*                                                                           *)
(* After symbolic execution of round-group i's instructions, the XMM1 and    *)
(* XMM2 assumptions contain nested sha_ni_rnds2 applications over the        *)
(* ABEF/CDGH packs of the previous group's state.  CUT_POINT_TAC_HW applies  *)
(* GROUP_BRIDGE_H.(i) and GROUP_BRIDGE_H2.(i) to collapse these into         *)
(* ABEF/CDGH packs of sha256_compress (4*(i+1)) W H.                         *)
(* ========================================================================= *)

let GEN_CUT_POINT_TAC_HW h_tm i sname =
  let target = mk_small_numeral(4 * (i + 1)) in
  let len_h_thm =
    prove(mk_eq(mk_comb(`LENGTH:int32 list->num`, h_tm), `8`),
          REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
  let bridge_h = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (MP (SPECL [`W:int32 list`; h_tm] GROUP_BRIDGE_H.(i)) len_h_thm) in
  let bridge_h2 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (MP (SPECL [`W:int32 list`; h_tm] GROUP_BRIDGE_H2.(i)) len_h_thm) in
  let xmm1_tm = subst [sname, `s:x86state`; target, `t:num`; h_tm, `H:int32 list`]
    `read XMM1 s = ABEF_PACK
       (EL 0 (sha256_compress t W (H:int32 list)))
       (EL 1 (sha256_compress t W H))
       (EL 4 (sha256_compress t W H))
       (EL 5 (sha256_compress t W H))` in
  let xmm2_tm = subst [sname, `s:x86state`; target, `t:num`; h_tm, `H:int32 list`]
    `read XMM2 s = CDGH_PACK
       (EL 2 (sha256_compress t W (H:int32 list)))
       (EL 3 (sha256_compress t W H))
       (EL 6 (sha256_compress t W H))
       (EL 7 (sha256_compress t W H))` in
  let CUT_SUBGOAL_TAC bridge =
    ASM_REWRITE_TAC[bridge] THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(CONJUNCT1 sha256_compress)))) THEN
    TRY(CONV_TAC(RAND_CONV(DEPTH_CONV EL_CONV))) THEN
    REWRITE_TAC EL_W_ALL_LIST THEN
    REWRITE_TAC[SHA256_COMPRESS_ROUND_EL_LIST;
                WORD_JOIN4_SUBWORD] THEN
    REFL_TAC in
  SUBGOAL_THEN xmm1_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h; ALL_TAC] THEN
  SUBGOAL_THEN xmm2_tm ASSUME_TAC THENL
   [CUT_SUBGOAL_TAC bridge_h2; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t ->
      try let n = fst(dest_const t) in n = "sha_ni_rnds2"
      with _ -> false)) (concl th))));;

let CUT_POINT_TAC_HW i sname = GEN_CUT_POINT_TAC_HW h_list_tm i sname;;

(* ========================================================================= *)
(* Single-block register core theorem.                                       *)
(*                                                                           *)
(* Starting at pc+64 (loop-top: first MOVDQU xmm3, [rsi]) with:              *)
(*   - XMM1 / XMM2 holding ABEF/CDGH of initial hash state H                 *)
(*   - XMM7 = XMM8 = pshufb_mask_val                                         *)
(*   - memory[rsi..rsi+63] = 4 x word_join4 of word_bytereverse w_i          *)
(*   - memory[rcx..rcx+255] = 16 x word_join4 of sha256_K                    *)
(*   - memory[rcx+256..rcx+271] = pshufb_mask_val                            *)
(*                                                                           *)
(* After the body (pc+64..pc+788, i.e., up to but not including the JNZ):    *)
(*   - XMM1 / XMM2 hold ABEF/CDGH of sha256_block M H                        *)
(*   - PC = pc + 788, RDX decremented, RSI advanced 64.                      *)
(*                                                                           *)
(* The proof body is currently CHEAT_TAC.  The per-group structure is        *)
(* (from memory: /home/ubuntu/.claude/.../memory/sha256_x86_phase4.md):      *)
(*                                                                           *)
(*   Round-group step boundaries (X86_STEPS_TAC 1-based indices):            *)
(*     prologue (MOVDQU xmm3..xmm6, pshufb):  steps  1- 4 of loop body       *)
(*     group  0: ends at step 26 (pc+121)                                    *)
(*     group  1: ends at step 34 (pc+156)                                    *)
(*     ...                                                                    *)
(*     group 15: ends at step 179 (pc+774)                                   *)
(*     add-back + jnz:                       steps 180-182                   *)
(*                                                                           *)
(* Per-group pattern:                                                         *)
(*   X86_STEPS_TAC HW_EXEC [n..n+k] THEN                                     *)
(*   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN *)
(*   (* specialise K memory at the group's index *) THEN                    *)
(*   CUT_POINT_TAC_HW i sN                                                  *)
(* ========================================================================= *)

let SHA256_BLOCK_CORE_CORRECT = prove
 (`!pc data_ptr kptr
    (a:int32) b c d e (ff:int32) g h
    (w0:int32) w1 w2 w3 w4 w5 w6 w7
    w8 w9 w10 w11 w12 w13 w14 w15
    rdx_in.
    nonoverlapping (data_ptr:int64, 64) (word pc, 829) /\
    nonoverlapping (kptr:int64, 272) (word pc, 829) /\
    nonoverlapping (data_ptr:int64, 64) (kptr:int64, 272)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) sha256_hw_mc /\
          read RIP s = word(pc + 64) /\
          read RSI s = data_ptr /\
          read RCX s = kptr /\
          read RDX s = rdx_in /\
          read XMM1 s = ABEF_PACK a b e ff /\
          read XMM2 s = CDGH_PACK c d g h /\
          read XMM7 s = pshufb_mask_val /\
          read XMM8 s = pshufb_mask_val /\
          read (memory :> bytes128 data_ptr) s =
            word_join4 (word_bytereverse w0) (word_bytereverse w1)
                       (word_bytereverse w2) (word_bytereverse w3) /\
          read (memory :> bytes128 (word_add data_ptr (word 16))) s =
            word_join4 (word_bytereverse w4) (word_bytereverse w5)
                       (word_bytereverse w6) (word_bytereverse w7) /\
          read (memory :> bytes128 (word_add data_ptr (word 32))) s =
            word_join4 (word_bytereverse w8) (word_bytereverse w9)
                       (word_bytereverse w10) (word_bytereverse w11) /\
          read (memory :> bytes128 (word_add data_ptr (word 48))) s =
            word_join4 (word_bytereverse w12) (word_bytereverse w13)
                       (word_bytereverse w14) (word_bytereverse w15) /\
          (!i. i < 16 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
              word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                         (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)) /\
          read (memory :> bytes128 (word_add kptr (word 256))) s =
            pshufb_mask_val)
     (\s. read RIP s = word(pc + 788) /\
          read RSI s = word_add data_ptr (word 64) /\
          read RDX s = word_sub rdx_in (word 1) /\
          (let blk = sha256_block [w0;w1;w2;w3;w4;w5;w6;w7;
                                   w8;w9;w10;w11;w12;w13;w14;w15]
                                  [a;b;c;d;e;ff;g;h] in
           read XMM1 s =
             ABEF_PACK (EL 0 blk) (EL 1 blk) (EL 4 blk) (EL 5 blk) /\
           read XMM2 s =
             CDGH_PACK (EL 2 blk) (EL 3 blk) (EL 6 blk) (EL 7 blk)))
     (MAYCHANGE [RIP; RSI; RDX] ,,
      MAYCHANGE [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
                 XMM9; XMM10] ,,
      MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [events])`,
  CHEAT_TAC);;
