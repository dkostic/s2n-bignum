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
