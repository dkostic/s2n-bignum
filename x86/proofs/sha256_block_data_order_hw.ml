(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 multi-block hardware-accelerated function (x86-64 SHA-NI).        *)
(*                                                                           *)
(* Proves correctness of sha256_block_data_order_hw, which processes         *)
(* num_blocks consecutive 512-bit message blocks using the Intel SHA-NI      *)
(* extensions (SHA256RNDS2 / SHA256MSG1 / SHA256MSG2 and friends).           *)
(*                                                                           *)
(* void sha256_block_data_order_hw(uint32_t state[8],     /* %rdi */         *)
(*                                 const uint8_t *data,   /* %rsi */         *)
(*                                 size_t num_blocks,     /* %rdx */         *)
(*                                 const uint32_t K[64])  /* %rcx */         *)
(*                                                                           *)
(* Structure (mirrors arm/proofs/sha256_block_data_order_hw.ml):             *)
(*   - Prologue (pc+0..pc+63): load state, pack it into ABEF/CDGH,           *)
(*     load pshufb mask, duplicate into xmm7/xmm8.                           *)
(*   - Loop body (pc+64..pc+788): SHA256_BLOCK_CORE_CORRECT handles one      *)
(*     full 64-round compression; this is a (strengthened) reuse of the      *)
(*     single-block core theorem from sha256_block_core.ml.                  *)
(*   - Back-edge (pc+788..pc+794): JNE to pc+64 if RDX != 0.                 *)
(*   - Epilogue (pc+794..pc+828): unpack ABEF/CDGH back to linear            *)
(*     state[0..7] and store via movdqu.                                     *)
(* ========================================================================= *)

needs "x86/proofs/sha256_block_core.ml";;

(* ========================================================================= *)
(* Re-use machine code and execution rule from the core file.               *)
(* (sha256_hw_mc and HW_EXEC are defined in sha256_block_core.ml.)          *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Strengthened single-block core theorem.                                   *)
(*                                                                           *)
(* Identical to SHA256_BLOCK_CORE_CORRECT but additionally asserts that      *)
(* XMM7 and XMM8 still hold the pshufb_mask_val at loop exit.                *)
(* The x86 asm's group 14 reloads XMM7 via `movdqa xmm7, xmm8` (step 158)    *)
(* for the post-loop byteswap the ARM version never needs; XMM8 is never     *)
(* written after prologue step 3.  Both facts are in-asl at POSTCOND time    *)
(* in the original proof — only the theorem statement elides them.           *)
(*                                                                           *)
(* Needed for the multi-block proof: the loop body restarts at pc+64 and     *)
(* the core theorem's precondition requires XMM7 = XMM8 = pshufb_mask_val.   *)
(* ========================================================================= *)

let SHA256_BLOCK_CORE_CORRECT_PLUS = time prove
 (`!pc data_ptr kptr
    (a:int32) b c d e (ff:int32) g h
    (w0:int32) w1 w2 w3 w4 w5 w6 w7
    w8 w9 w10 w11 w12 w13 w14 w15
    rdx_in.
    aligned 16 kptr /\
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
          (read ZF s <=> val (word_sub rdx_in (word 1):int64) = 0) /\
          read XMM7 s = pshufb_mask_val /\
          read XMM8 s = pshufb_mask_val /\
          (let blk = sha256_block [w0;w1;w2;w3;w4;w5;w6;w7;
                                   w8;w9;w10;w11;w12;w13;w14;w15]
                                  [a;b;c;d;e;ff;g;h] in
           read XMM1 s =
             ABEF_PACK (EL 0 blk) (EL 1 blk) (EL 4 blk) (EL 5 blk) /\
           read XMM2 s =
             CDGH_PACK (EL 2 blk) (EL 3 blk) (EL 6 blk) (EL 7 blk)))
     (MAYCHANGE [RIP; RSI; RDX] ,,
      MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE;
                 YMM5_SSE; YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
      MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  PROLOGUE_PLUS_GROUP0_TAC THEN
  GROUP1_TAC THEN GROUP2_TAC THEN GROUP3_TAC THEN GROUP4_TAC THEN
  GROUP5_TAC THEN GROUP6_TAC THEN GROUP7_TAC THEN GROUP8_TAC THEN
  GROUP9_TAC THEN GROUP10_TAC THEN GROUP11_TAC THEN GROUP12_TAC THEN
  GROUP13_TAC THEN GROUP14_TAC THEN GROUP15_TAC THEN
  POSTCOND_TAC_HW_NEW);;

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

let WORD_SUB_SUC_64 = prove
 (`!n. word_sub (word(SUC n):int64) (word 1) = word n`,
  GEN_TAC THEN REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE);;

let WORD_ADVANCE_64 = WORD_RULE
 `word_add (word_add d (word(64 * ii):int64)) (word 64) =
  word_add d (word(64 * (ii + 1)))`;;

(* LENGTH_16_CONS: a list of length 16 is a 16-CONS chain.                   *)

let LENGTH_16_CONS = prove
 (`!L:A list. LENGTH L = 16
   ==> ?a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15.
       L = [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15]`,
  let suc16 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC
      (SUC(SUC(SUC(SUC 0)))))))))))))))` in
  REWRITE_TAC[GSYM suc16; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

(* LIST_16_EL: a list of length 16 equals the list of its 16 elements.       *)

let LIST_16_EL = prove
 (`!L:A list. LENGTH L = 16 ==>
    L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L; EL 4 L; EL 5 L; EL 6 L; EL 7 L;
         EL 8 L; EL 9 L; EL 10 L; EL 11 L; EL 12 L; EL 13 L; EL 14 L;
         EL 15 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_16_CONS) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* LENGTH_8_CONS, LIST_8_EL: same for length-8 (used to decompose the hash   *)
(* state list [a;b;c;d;e;f;g;h] and sha256_hash_blocks outputs).              *)

let LENGTH_8_CONS = prove
 (`!L:A list. LENGTH L = 8
   ==> ?a0 a1 a2 a3 a4 a5 a6 a7.
       L = [a0;a1;a2;a3;a4;a5;a6;a7]`,
  let suc8 = NUM_REDUCE_CONV
    `SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))` in
  REWRITE_TAC[GSYM suc8; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_8_EL = prove
 (`!L:A list. LENGTH L = 8 ==>
    L = [EL 0 L; EL 1 L; EL 2 L; EL 3 L;
         EL 4 L; EL 5 L; EL 6 L; EL 7 L]`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_8_CONS) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* XMM_EXISTSTOP gives the YMMi read as word_join of an existential top128    *)
(* and the known XMMi value.  Useful for cleaning up YMM assumptions between  *)
(* SIMD steps so the stepper's next write produces a WORD_BLAST-friendly      *)
(* shape.  (Copy of the tactic from mlkem_rej_uniform_VARIABLE_TIME.ml.)      *)

let XMM_EXISTSTOP = prove
 (`!c s:S. read (c :> zerotop_128) s = l
           ==> ?h. read c s = (word_join:int128->int128->int256) h l`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `word_subword (read c (s:S):int256) (128,128):int128` THEN
  REWRITE_TAC[READ_ZEROTOP_128] THEN CONV_TAC WORD_BLAST);;

let XMM_EXISTSTOP_RULE =
  REWRITE_RULE (map GSYM
   [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
    XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15]) o
  C ISPEC XMM_EXISTSTOP;;

let XMM_EXISTSTOP_TAC top y =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (XMM_EXISTSTOP_RULE y)) THEN
  DISCH_THEN(X_CHOOSE_TAC(mk_var(top,`:int128`)));;


(* ========================================================================= *)
(* Prologue (pc+0..pc+51) converts linear state[0..7] in XMM1,XMM2 into the  *)
(* (ABEF, CDGH) pair expected at pc+64.  The shuffle chain is:               *)
(*                                                                           *)
(*   xmm1 = [a,b,c,d]  (lane 0..3 = state[0..3])                             *)
(*   xmm2 = [e,f,g,h]  (lane 0..3 = state[4..7])                             *)
(*   pshufd $0x1b xmm1,xmm0:  xmm0 = [d,c,b,a]                               *)
(*   pshufd $0xb1 xmm1,xmm1:  xmm1 = [b,a,d,c]                               *)
(*   pshufd $0x1b xmm2,xmm2:  xmm2 = [h,g,f,e]                               *)
(*   movdqa    xmm8,xmm7:     (mask copy into xmm8, saves for epilogue)      *)
(*   palignr  $0x8 xmm2,xmm1: xmm1 = [f,e,b,a] = ABEF_PACK a b e f           *)
(*   punpcklqdq xmm0,xmm2:    xmm2 = [h,g,d,c] = CDGH_PACK c d g h           *)
(*                                                                           *)
(* PROLOGUE_HW_TAC symbolically runs these 11 instructions (steps 1..11) and *)
(* asserts the clean ABEF_PACK / CDGH_PACK forms for XMM1, XMM2 at pc+64,    *)
(* along with XMM7 = XMM8 = pshufb_mask_val, matching the preconditions of   *)
(* the loop body (SHA256_BLOCK_CORE_CORRECT_PLUS).                           *)
(* ========================================================================= *)

let PROLOGUE_HW_TAC : tactic =
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `ymm8_init:int256` `read YMM8` THEN
  ENSURES_INIT_TAC "s0" THEN
  (* Steps 1-3: endbr64; MOVDQU xmm1,[rdi]; MOVDQU xmm2,[rdi+16] *)
  X86_STEPS_TAC HW_EXEC [1;2;3] THEN
  SUBGOAL_THEN `read XMM1 s3 = word_join4 a b c d` ASSUME_TAC
   THENL [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read XMM2 s3 = word_join4 e ff g h` ASSUME_TAC
   THENL [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 4: MOVDQA xmm7, [rcx+256] *)
  X86_STEPS_TAC HW_EXEC [4] THEN
  SUBGOAL_THEN `read XMM7 s4 = pshufb_mask_val` ASSUME_TAC
   THENL [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 5: PSHUFD xmm0, xmm1, 0x1b — full-lane reverse of xmm1 *)
  X86_STEPS_TAC HW_EXEC [5] THEN
  SUBGOAL_THEN `read XMM0 s5 = word_join4 d c b a` ASSUME_TAC
   THENL [REWRITE_TAC[XMM0; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 6: PSHUFD xmm1, xmm1, 0xb1 — pair-swap of xmm1 *)
  X86_STEPS_TAC HW_EXEC [6] THEN
  SUBGOAL_THEN `read XMM1 s6 = word_join4 b a d c` ASSUME_TAC
   THENL [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 7: PSHUFD xmm2, xmm2, 0x1b — full-lane reverse of xmm2 *)
  X86_STEPS_TAC HW_EXEC [7] THEN
  SUBGOAL_THEN `read XMM2 s7 = word_join4 h g ff e` ASSUME_TAC
   THENL [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 8: MOVDQA xmm8, xmm7 — copy mask so xmm8 holds a backup. *)
  X86_STEPS_TAC HW_EXEC [8] THEN
  SUBGOAL_THEN `read XMM8 s8 = pshufb_mask_val` ASSUME_TAC
   THENL [REWRITE_TAC[XMM8; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 9: PALIGNR xmm1, xmm2, 0x8 — xmm1 = high64(xmm2) || low64(xmm1)
     = [f,e,b,a] = ABEF_PACK a b e ff. *)
  X86_STEPS_TAC HW_EXEC [9] THEN
  SUBGOAL_THEN `read XMM1 s9 = ABEF_PACK a b e ff` ASSUME_TAC
   THENL [REWRITE_TAC[XMM1; READ_ZEROTOP_128; ABEF_PACK] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 10: PUNPCKLQDQ xmm2, xmm0 — xmm2 = low64(xmm0) || low64(xmm2)
     = [h,g,d,c] = CDGH_PACK c d g h. *)
  X86_STEPS_TAC HW_EXEC [10] THEN
  SUBGOAL_THEN `read XMM2 s10 = CDGH_PACK c d g h` ASSUME_TAC
   THENL [REWRITE_TAC[XMM2; READ_ZEROTOP_128; CDGH_PACK] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* Step 11: JMP +0xb → pc+64 (loop top) *)
  X86_STEPS_TAC HW_EXEC [11];;

(* ========================================================================= *)
(* Epilogue (pc+794..pc+828): unpack ABEF/CDGH in XMM1,XMM2 back into linear *)
(* state[0..7] layout and store it at state_ptr.  Inverse of the prologue:   *)
(*                                                                           *)
(*   pshufd $0xb1 xmm2,xmm2:  xmm2 = [g,h,c,d]  (from CDGH = [h,g,d,c])      *)
(*   pshufd $0x1b xmm1,xmm7:  xmm7 = reverse  = [a,b,e,f]                    *)
(*   pshufd $0xb1 xmm1,xmm1:  xmm1 = pair-swap = [e,f,a,b]                   *)
(*   punpckhqdq xmm1,xmm2:    xmm1 = high64(xmm2) || high64(xmm1)            *)
(*                                 = [c,d] || [a,b] = [a,b,c,d]              *)
(*   palignr    $0x8 xmm2,xmm7: xmm2 = high64(xmm7) || low64(xmm2)           *)
(*                                   = [e,f] || [g,h] = [e,f,g,h]            *)
(*   movdqu xmm1,(%rdi):       store state[0..3] = [a,b,c,d]                 *)
(*   movdqu xmm2,0x10(%rdi):   store state[4..7] = [e,f,g,h]                 *)
(*                                                                           *)
(* EPILOGUE_HW_TAC symbolically runs these 7 instructions (steps N..N+6 from *)
(* the "end of last loop body + JNE-not-taken" entry point) and asserts the  *)
(* final clean state-store forms.                                            *)
(* ========================================================================= *)

(* Note: The actual step numbers in the epilogue depend on how we arrive;
   they start at `1` with ENSURES_INIT_TAC "s0" at pc+794 (post-JNE fall
   through).  Instructions:
     step 1: pshufd $0xb1 xmm2, xmm2
     step 2: pshufd $0x1b xmm1, xmm7
     step 3: pshufd $0xb1 xmm1, xmm1
     step 4: punpckhqdq xmm1, xmm2
     step 5: palignr $0x8 xmm2, xmm7
     step 6: movdqu %xmm1, (%rdi)
     step 7: movdqu %xmm2, 0x10(%rdi)
   (step 8 would be RET, handled by the SUBROUTINE wrapper). *)

(* ========================================================================= *)
(* Multi-block correctness theorem.                                          *)
(*                                                                           *)
(* The `blocks` parameter represents the SHA-256-ready message blocks (each  *)
(* a list of 16 int32 words in logical order, as processed by the compress   *)
(* function).  Memory at data_ptr holds the word_bytereverse of each element *)
(* (the raw little-endian bytes from the input stream); the assembly applies *)
(* PSHUFB with pshufb_mask_val to convert.                                   *)
(*                                                                           *)
(* The loop invariant tracks sha256_hash_blocks i blocks H in XMM1/XMM2      *)
(* (ABEF/CDGH form), data pointer advanced by 64*i, counter decremented by i.*)
(* ========================================================================= *)

let SHA256_HW_CORRECT = time prove(
 `!num_blocks state_ptr data_ptr kptr
    (a:int32) b c d (e:int32) (ff:int32) g h
    (blocks:(int32 list) list) pc.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 kptr /\
    ALL (nonoverlapping (state_ptr, 32))
        [(word pc, 829); (data_ptr, 64 * num_blocks); (kptr, 272)] /\
    nonoverlapping (data_ptr, 64 * num_blocks) (word pc, 829) /\
    nonoverlapping (kptr, 272) (word pc, 829) /\
    nonoverlapping (data_ptr, 64 * num_blocks) (kptr, 272)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) sha256_hw_mc /\
          read RIP s = word pc /\
          read RDI s = state_ptr /\
          read RSI s = data_ptr /\
          read RDX s = word num_blocks /\
          read RCX s = kptr /\
          read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
          read (memory :> bytes128 (word_add state_ptr (word 16))) s =
            word_join4 e ff g h /\
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
                         (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)) /\
          read (memory :> bytes128 (word_add kptr (word 256))) s =
            pshufb_mask_val)
     (\s. read RIP s = word(pc + 828) /\
          (let result = sha256_hash_blocks num_blocks blocks
                          [a;b;c;d;e;ff;g;h] in
           read (memory :> bytes128 state_ptr) s =
             word_join4 (EL 0 result) (EL 1 result)
                        (EL 2 result) (EL 3 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 16))) s =
             word_join4 (EL 4 result) (EL 5 result)
                        (EL 6 result) (EL 7 result)))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE;
                 YMM5_SSE; YMM6_SSE; YMM7_SSE; YMM8_SSE;
                 YMM9_SSE; YMM10_SSE] ,,
      MAYCHANGE [memory :> bytes(state_ptr, 32)] ,,
      MAYCHANGE [events])`,

  REWRITE_TAC[ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `~(num_blocks = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN

  (* ======================================================================= *)
  (* Split 1: pc+0 → pc+64.  Run the prologue; reorder preconditions into the *)
  (* ABEF/CDGH layout the core expects.                                       *)
  (* ======================================================================= *)
  ENSURES_SEQUENCE_TAC `pc + 64`
    `\s. bytes_loaded s (word pc) sha256_hw_mc /\
         read RDI s = state_ptr /\
         read RSI s = data_ptr /\
         read RDX s = word num_blocks /\
         read RCX s = kptr /\
         read XMM1 s = ABEF_PACK a b e ff /\
         read XMM2 s = CDGH_PACK c d g h /\
         read XMM7 s = pshufb_mask_val /\
         read XMM8 s = pshufb_mask_val /\
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
                        (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)) /\
         read (memory :> bytes128 (word_add kptr (word 256))) s =
           pshufb_mask_val /\
         read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
         read (memory :> bytes128 (word_add state_ptr (word 16))) s =
           word_join4 e ff g h` THEN
  CONJ_TAC THENL
   [(* Prologue: pc+0 → pc+64 *)
    PROLOGUE_HW_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (* ======================================================================= *)
  (* Split 2: pc+64 → pc+794.  Loop body (pc+64..pc+788) + JNE-fall-through  *)
  (* (pc+788..pc+794).  Epilogue is the subsequent pc+794..pc+828 segment.   *)
  (* ======================================================================= *)

  (* Introduce the loop invariant.  After i iterations, XMM1/XMM2 hold the    *)
  (* ABEF/CDGH pack of sha256_hash_blocks i blocks H, RSI = data_ptr+64*i,    *)
  (* RDX = num_blocks - i, XMM7=XMM8=mask, data/K memory unchanged.           *)
  (* Use ENSURES_WHILE_UP2_TAC so body goes pc1 → (pc1 or pc2) depending  *)
  (* on i+1<k.  This avoids a separate back-edge subgoal: JNE branch is  *)
  (* handled inside the body via ZF postcondition from the core theorem. *)
  ENSURES_WHILE_UP2_TAC `num_blocks:num` `pc + 64` `pc + 794`
    `\i s. bytes_loaded s (word pc) sha256_hw_mc /\
           read RDI s = state_ptr /\
           read RSI s = word_add data_ptr (word(64 * i)) /\
           read RDX s = word(num_blocks - i) /\
           read RCX s = kptr /\
           read XMM1 s = ABEF_PACK
             (EL 0 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h]:int32 list))
             (EL 1 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h]))
             (EL 4 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h]))
             (EL 5 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h])) /\
           read XMM2 s = CDGH_PACK
             (EL 2 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h]:int32 list))
             (EL 3 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h]))
             (EL 6 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h]))
             (EL 7 (sha256_hash_blocks i blocks [a;b;c;d;e;ff;g;h])) /\
           read XMM7 s = pshufb_mask_val /\
           read XMM8 s = pshufb_mask_val /\
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
           read (memory :> bytes128 (word_add kptr (word 256))) s =
             pshufb_mask_val /\
           read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
           read (memory :> bytes128 (word_add state_ptr (word 16))) s =
             word_join4 e ff g h` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
    (* ==================================================================== *)
    (* Subgoal 1: Invariant at i=0 follows from post-prologue state.         *)
    (* ==================================================================== *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[sha256_hash_blocks; WORD_ADD_0; MULT_CLAUSES; SUB_0] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];

    (* ==================================================================== *)
    (* Subgoal 2: Body from pc+64 (inv(ii)) to pc+64 or pc+794 (inv(ii+1))   *)
    (* via SHA256_BLOCK_CORE_CORRECT_PLUS (one loop iteration) + JNE.        *)
    (*                                                                       *)
    (* Shape of the step: the core theorem processes one 512-bit block in    *)
    (* one "big step" (s0 -> s1) via X86_BIGSTEP_TAC; the subsequent JNE at  *)
    (* pc+788 is one X86_STEPS_TAC, and its RIP destination matches the      *)
    (* loop invariant's conditional RIP via num_blocks-ii = SUC(num_blocks-  *)
    (* (ii+1)) + WORD_SUB_SUC_64 + case analysis.                            *)
    (*                                                                       *)
    (* The XMM1/XMM2 sha256_hash_blocks equalities use sha256_hash_blocks's  *)
    (* recursive case and LIST_16_EL / LIST_8_EL to bridge between the       *)
    (* core theorem's "ws as explicit args / state as explicit args" form    *)
    (* and the invariant's "EL k (EL ii blocks) / EL k (hash_ii)" form.      *)
    (* ==================================================================== *)
    X_GEN_TAC `ii:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `num_blocks - ii < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `num_blocks - ii` THEN
    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL
     [`pc:num`;
      `word_add (data_ptr:int64) (word (64 * ii)):int64`;
      `kptr:int64`;
      `EL 0 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 1 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 2 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 3 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 4 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 5 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 6 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 7 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]):int32`;
      `EL 0 (EL ii blocks):int32`;
      `EL 1 (EL ii blocks):int32`;
      `EL 2 (EL ii blocks):int32`;
      `EL 3 (EL ii blocks):int32`;
      `EL 4 (EL ii blocks):int32`;
      `EL 5 (EL ii blocks):int32`;
      `EL 6 (EL ii blocks):int32`;
      `EL 7 (EL ii blocks):int32`;
      `EL 8 (EL ii blocks):int32`;
      `EL 9 (EL ii blocks):int32`;
      `EL 10 (EL ii blocks):int32`;
      `EL 11 (EL ii blocks):int32`;
      `EL 12 (EL ii blocks):int32`;
      `EL 13 (EL ii blocks):int32`;
      `EL 14 (EL ii blocks):int32`;
      `EL 15 (EL ii blocks):int32`;
      `word(num_blocks - ii):int64`] SHA256_BLOCK_CORE_CORRECT_PLUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT CONJ_TAC THEN
      NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    X86_BIGSTEP_TAC HW_EXEC "s1" THENL [
      (* Subgoal: data-memory matches at (data_ptr + 64*ii + {0,16,32,48}).
         Rewrite the inner `word_add (data_ptr + 64*ii) k` to
         `word_add data_ptr (64*ii + k)` so the quantified ASM fires. *)
      REPEAT CONJ_TAC THEN
      REWRITE_TAC[WORD_RULE
        `word_add (word_add data_ptr (word(64 * ii))) (word k) =
         word_add data_ptr (word(64 * ii + k))`] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    (* Step 2: JNE at pc+788; RIP becomes (if ~ZF then pc+64 else pc+794). *)
    X86_STEPS_TAC HW_EXEC [2] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* Normalize num_blocks - ii = SUC(num_blocks - (ii+1)) so WORD_SUB_SUC_64
       fires in the `word_sub ... (word 1)` slots. *)
    SUBGOAL_THEN `num_blocks - ii = SUC(num_blocks - (ii + 1))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[WORD_SUB_SUC_64]] THEN
    REPEAT CONJ_TAC THENL [
      (* RIP: (if ~(val(word(num_blocks-(ii+1))) = 0) then pc+64 else pc+794)
             = word (if ii+1 < num_blocks then pc+64 else pc+794) *)
      SUBGOAL_THEN `num_blocks - (ii + 1) < 2 EXP 64` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `num_blocks - (ii + 1)` THEN
      ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
       [COND_CASES_TAC THENL [REFL_TAC; ASM_ARITH_TAC];
        COND_CASES_TAC THENL [ASM_ARITH_TAC; REFL_TAC]];
      (* RSI: word_add (data_ptr + 64*ii) 64 = data_ptr + 64*(ii+1) *)
      CONV_TAC WORD_RULE;
      (* (The RDX equality `word_sub(word(SUC k))(word 1) = word k` is
         discharged implicitly by ASM_REWRITE_TAC + WORD_SUB_SUC_64 above.) *)
      (* XMM1: unfold sha256_hash_blocks (ii+1) and the two list-rebuild
         steps via LIST_16_EL (for EL ii blocks) and LIST_8_EL (for the hash
         state list).  Both LIST_16/8_EL applications need the corresponding
         LENGTH side-conditions. *)
      REWRITE_TAC[sha256_hash_blocks] THEN
      SUBGOAL_THEN `LENGTH(EL ii blocks:int32 list) = 16` ASSUME_TAC THENL
       [UNDISCH_TAC `ALL (\bll:int32 list. LENGTH bll = 16) blocks` THEN
        REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `LENGTH(sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]) = 8`
        ASSUME_TAC THENL
       [MATCH_MP_TAC LENGTH_SHA256_HASH_BLOCKS THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
      SUBGOAL_THEN
        `[EL 0 (EL ii blocks):int32; EL 1 (EL ii blocks);
          EL 2 (EL ii blocks); EL 3 (EL ii blocks);
          EL 4 (EL ii blocks); EL 5 (EL ii blocks);
          EL 6 (EL ii blocks); EL 7 (EL ii blocks);
          EL 8 (EL ii blocks); EL 9 (EL ii blocks);
          EL 10 (EL ii blocks); EL 11 (EL ii blocks);
          EL 12 (EL ii blocks); EL 13 (EL ii blocks);
          EL 14 (EL ii blocks); EL 15 (EL ii blocks)]
         = EL ii blocks`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
      THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LIST_16_EL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `[EL 0 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]);
          EL 1 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 2 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 3 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 4 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 5 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 6 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 7 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h])]
         = sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
      THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LIST_8_EL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      (* XMM2: same pattern. *)
      REWRITE_TAC[sha256_hash_blocks] THEN
      SUBGOAL_THEN `LENGTH(EL ii blocks:int32 list) = 16` ASSUME_TAC THENL
       [UNDISCH_TAC `ALL (\bll:int32 list. LENGTH bll = 16) blocks` THEN
        REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `ii:num`) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `LENGTH(sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]) = 8`
        ASSUME_TAC THENL
       [MATCH_MP_TAC LENGTH_SHA256_HASH_BLOCKS THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
      SUBGOAL_THEN
        `[EL 0 (EL ii blocks):int32; EL 1 (EL ii blocks);
          EL 2 (EL ii blocks); EL 3 (EL ii blocks);
          EL 4 (EL ii blocks); EL 5 (EL ii blocks);
          EL 6 (EL ii blocks); EL 7 (EL ii blocks);
          EL 8 (EL ii blocks); EL 9 (EL ii blocks);
          EL 10 (EL ii blocks); EL 11 (EL ii blocks);
          EL 12 (EL ii blocks); EL 13 (EL ii blocks);
          EL 14 (EL ii blocks); EL 15 (EL ii blocks)]
         = EL ii blocks`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
      THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LIST_16_EL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `[EL 0 (sha256_hash_blocks ii blocks [a:int32;b;c;d;e;ff;g;h]);
          EL 1 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 2 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 3 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 4 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 5 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 6 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]);
          EL 7 (sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h])]
         = sha256_hash_blocks ii blocks [a;b;c;d;e;ff;g;h]`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
      THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LIST_8_EL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[]
    ];

    (* ==================================================================== *)
    (* Subgoal 3: Exit at pc+794 with invariant(num_blocks) → postcondition. *)
    (* Runs the 7-instruction epilogue (pc+794..pc+828) — the inverse of the *)
    (* prologue's ABEF/CDGH pack plus two MOVDQU stores to state_ptr.        *)
    (*                                                                       *)
    (* Each SIMD step establishes a clean XMM form via SUBGOAL_THEN +         *)
    (* REWRITE[XMMi;READ_ZEROTOP_128;ABEF/CDGH_PACK] + WORD_BLAST and then    *)
    (* re-ghosts the YMM via XMM_EXISTSTOP_TAC so the next step's write can   *)
    (* be bit-blasted without exploding.                                     *)
    (* ==================================================================== *)
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    ABBREV_TAC `result = sha256_hash_blocks num_blocks blocks
                          [a:int32;b;c;d;e;ff;g;h]` THEN
    (* Introduce ghost upper-128 halves for YMM1/YMM2/YMM7 so subsequent
       writes produce bit-blastable shapes. *)
    XMM_EXISTSTOP_TAC "top1" `YMM1` THEN
    XMM_EXISTSTOP_TAC "top2" `YMM2` THEN
    XMM_EXISTSTOP_TAC "top7" `YMM7` THEN
    (* Step 1: pshufd xmm2,xmm2,0xb1 — pair-swap lanes of CDGH_PACK. *)
    X86_STEPS_TAC HW_EXEC [1] THEN
    SUBGOAL_THEN
      `read XMM2 s1 = word_join4 (EL 6 (result:int32 list)) (EL 7 result)
                                 (EL 2 result) (EL 3 result)`
      ASSUME_TAC THENL
     [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[CDGH_PACK] THEN
      REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o
      check (fun th -> let s = string_of_term (concl th) in
                       String.length s > 200 &&
                       (try String.sub s 0 9 = "read YMM2" with _ -> false))) THEN
    XMM_EXISTSTOP_TAC "top2a" `YMM2` THEN
    (* Step 2: pshufd xmm7,xmm1,0x1b — full-lane reverse into XMM7. *)
    X86_STEPS_TAC HW_EXEC [2] THEN
    SUBGOAL_THEN
      `read XMM7 s2 = word_join4 (EL 0 (result:int32 list)) (EL 1 result)
                                 (EL 4 result) (EL 5 result)`
      ASSUME_TAC THENL
     [REWRITE_TAC[XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[ABEF_PACK] THEN
      REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o
      check (fun th -> let s = string_of_term (concl th) in
                       String.length s > 200 &&
                       (try String.sub s 0 9 = "read YMM7" with _ -> false))) THEN
    XMM_EXISTSTOP_TAC "top7a" `YMM7` THEN
    (* Step 3: pshufd xmm1,xmm1,0xb1 — pair-swap of XMM1. *)
    X86_STEPS_TAC HW_EXEC [3] THEN
    SUBGOAL_THEN
      `read XMM1 s3 = word_join4 (EL 4 (result:int32 list)) (EL 5 result)
                                 (EL 0 result) (EL 1 result)`
      ASSUME_TAC THENL
     [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[ABEF_PACK] THEN
      REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o
      check (fun th -> let s = string_of_term (concl th) in
                       String.length s > 200 &&
                       (try String.sub s 0 9 = "read YMM1" with _ -> false))) THEN
    XMM_EXISTSTOP_TAC "top1a" `YMM1` THEN
    (* Step 4: punpckhqdq xmm1,xmm2 — XMM1 ← high64(xmm2)||high64(xmm1). *)
    X86_STEPS_TAC HW_EXEC [4] THEN
    SUBGOAL_THEN
      `read XMM1 s4 = word_join4 (EL 0 (result:int32 list)) (EL 1 result)
                                 (EL 2 result) (EL 3 result)`
      ASSUME_TAC THENL
     [REWRITE_TAC[XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o
      check (fun th -> let s = string_of_term (concl th) in
                       String.length s > 200 &&
                       (try String.sub s 0 9 = "read YMM1" with _ -> false))) THEN
    XMM_EXISTSTOP_TAC "top1b" `YMM1` THEN
    (* Step 5: palignr xmm2,xmm7,0x8 — high64(xmm7)||low64(xmm2). *)
    X86_STEPS_TAC HW_EXEC [5] THEN
    SUBGOAL_THEN
      `read XMM2 s5 = word_join4 (EL 4 (result:int32 list)) (EL 5 result)
                                 (EL 6 result) (EL 7 result)`
      ASSUME_TAC THENL
     [REWRITE_TAC[XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[word_join4] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o
      check (fun th -> let s = string_of_term (concl th) in
                       String.length s > 200 &&
                       (try String.sub s 0 9 = "read YMM2" with _ -> false))) THEN
    XMM_EXISTSTOP_TAC "top2b" `YMM2` THEN
    (* Steps 6-7: the two MOVDQU stores to state_ptr and state_ptr+16. *)
    X86_STEPS_TAC HW_EXEC [6;7] THEN
    (* Finalize: split state eqs from MAYCHANGE; close each with WORD_BLAST
       after abbreviating EL k result to a fresh variable; handle the
       MAYCHANGE subsumption via subsumed_pth_hw (SOME_FLAGS needs explicit
       unfolding — MONOTONE_MAYCHANGE_TAC won't do it here). *)
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    (* The MAYCHANGE conjunct is discharged automatically by ASM_REWRITE_TAC
       (it matches an assumption on s0/s7 accumulated during stepping).
       Two state-memory conjuncts remain, both closable by WORD_BLAST. *)
    CONJ_TAC THEN CONV_TAC WORD_BLAST
  ]);;

(* ========================================================================= *)
(* Subroutine correctness: lifts SHA256_HW_CORRECT to the C-ABI subroutine   *)
(* form, with returnaddress on the stack and RIP = returnaddress on exit.    *)
(* ========================================================================= *)

let SHA256_HW_SUBROUTINE_CORRECT = time prove(
 `!num_blocks state_ptr data_ptr kptr
    (a:int32) b c d (e:int32) (ff:int32) g h
    (blocks:(int32 list) list) pc stackpointer returnaddress.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\
    ALL (\bl. LENGTH bl = 16) blocks /\
    aligned 16 kptr /\
    ALL (nonoverlapping (state_ptr, 32))
        [(word pc, 829); (data_ptr, 64 * num_blocks); (kptr, 272);
         (stackpointer, 8)] /\
    nonoverlapping (data_ptr, 64 * num_blocks) (word pc, 829) /\
    nonoverlapping (kptr, 272) (word pc, 829) /\
    nonoverlapping (data_ptr, 64 * num_blocks) (kptr, 272)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) sha256_hw_mc /\
          read RIP s = word pc /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read RDI s = state_ptr /\
          read RSI s = data_ptr /\
          read RDX s = word num_blocks /\
          read RCX s = kptr /\
          read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
          read (memory :> bytes128 (word_add state_ptr (word 16))) s =
            word_join4 e ff g h /\
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
                         (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)) /\
          read (memory :> bytes128 (word_add kptr (word 256))) s =
            pshufb_mask_val)
     (\s. read RIP s = returnaddress /\
          read RSP s = word_add stackpointer (word 8) /\
          (let result = sha256_hash_blocks num_blocks blocks
                          [a;b;c;d;e;ff;g;h] in
           read (memory :> bytes128 state_ptr) s =
             word_join4 (EL 0 result) (EL 1 result)
                        (EL 2 result) (EL 3 result) /\
           read (memory :> bytes128 (word_add state_ptr (word 16))) s =
             word_join4 (EL 4 result) (EL 5 result)
                        (EL 6 result) (EL 7 result)))
     (MAYCHANGE [RSP] ,,
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(state_ptr, 32)])`,
  X86_ADD_RETURN_NOSTACK_TAC HW_EXEC SHA256_HW_CORRECT);;



