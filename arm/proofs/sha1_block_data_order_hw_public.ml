(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Phase 9 public-facing correctness theorem for                             *)
(* sha1_block_data_order_hw, stated over a byte-level data buffer.           *)
(*                                                                           *)
(* This is a thin wrapper around SHA1_HW_SUBROUTINE_CORRECT (in              *)
(* arm/proofs/sha1_block_data_order_hw_ensures.ml) that exposes the          *)
(* data buffer as a byte list (what callers normally have at hand) instead   *)
(* of the structured block list (which the existing theorem uses             *)
(* internally for proof bookkeeping).                                        *)
(*                                                                           *)
(* It is whole-blocks-only: no FIPS padding or length-tagging. The caller    *)
(* (e.g. the FIPS one-shot SHA-1 hash function) is responsible for           *)
(* preparing a buffer whose length is a multiple of 64 bytes.                *)
(* ========================================================================= *)

needs "arm/proofs/sha1_block_data_order_hw_ensures.ml";;

(* ------------------------------------------------------------------------- *)
(* Public correctness theorem.                                               *)
(*                                                                           *)
(* Given:                                                                    *)
(*   - state_ptr -> 20-byte state buffer holding 5 little-endian uint32s     *)
(*     (the 5-word SHA-1 hash state H = [a;b;c;d;e]).                        *)
(*   - data_ptr -> 64*num_blocks-byte data buffer holding raw message bytes. *)
(*   - kptr -> 64-byte K-constants table (4 uint32s per FIPS K, broadcast).  *)
(*                                                                           *)
(* The routine produces the updated 5-word state                             *)
(*   sha1_hash_bytes num_blocks data_bytes [a;b;c;d;e]                       *)
(* in the state buffer.                                                      *)
(*                                                                           *)
(* Discharged by instantiating SHA1_HW_SUBROUTINE_CORRECT with               *)
(*   blocks = sha1_blocks_from_bytes num_blocks data_bytes                   *)
(* and using the bytelist-to-bytes128 bridge SHA1_BYTES128_FROM_BYTELIST     *)
(* (in arm/proofs/utils/sha1_bridge.ml).                                     *)
(* ------------------------------------------------------------------------- *)

let SHA1_HW_BYTES_SUBROUTINE_CORRECT = prove
 (`!num_blocks state_ptr data_ptr kptr
    (a:int32) (b:int32) (c:int32) (d:int32) (e:int32)
    (data_bytes:byte list) pc returnaddress.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH data_bytes = 64 * num_blocks /\
    ALL (nonoverlapping (state_ptr, 20))
        [(word pc, 468); (data_ptr, 64 * num_blocks); (kptr, 64)] /\
    nonoverlapping (data_ptr, 64 * num_blocks) (word pc, 468) /\
    nonoverlapping (kptr, 64) (word pc, 468)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha1_block_data_order_hw_mc /\
          read PC s = word pc /\
          read X30 s = returnaddress /\
          read X0 s = state_ptr /\
          read X1 s = data_ptr /\
          read X2 s = word num_blocks /\
          read X3 s = kptr /\
          read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
          read (memory :> bytes32 (word_add state_ptr (word 16))) s = e /\
          read (memory :> bytelist (data_ptr, 64 * num_blocks)) s =
            data_bytes /\
          (!i. i < 4 ==>
            read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
            word_join4 (sha1_K (20*i)) (sha1_K (20*i))
                       (sha1_K (20*i)) (sha1_K (20*i))))
     (\s. read PC s = returnaddress /\
          (let result =
             sha1_hash_bytes num_blocks data_bytes [a;b;c;d;e] in
           read (memory :> bytes128 state_ptr) s =
             word_join4 (EL 0 result) (EL 1 result)
                        (EL 2 result) (EL 3 result) /\
           read (memory :> bytes32 (word_add state_ptr (word 16))) s =
             EL 4 result))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19;
                 Q20; Q21; Q22] ,,
      MAYCHANGE [memory :> bytes(state_ptr, 20)] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`num_blocks:num`; `state_ptr:int64`; `data_ptr:int64`; `kptr:int64`;
    `a:int32`; `b:int32`; `c:int32`; `d:int32`; `e:int32`;
    `sha1_blocks_from_bytes num_blocks (data_bytes:byte list)`;
    `pc:num`; `returnaddress:int64`]
   SHA1_HW_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[LENGTH_SHA1_BLOCKS_FROM_BYTES;
                  ALL_LENGTH_SHA1_BLOCKS_FROM_BYTES] THEN
  REWRITE_TAC[sha1_hash_bytes] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EL_SHA1_BLOCKS_FROM_BYTES; EL_SHA1_BLOCK_FROM_BYTES; ARITH] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_SHA1_BLOCK_WORD] THEN
  CONJ_TAC THENL [
    MP_TAC(SPECL [`x:armstate`; `data_ptr:int64`; `data_bytes:byte list`;
                  `64 * j`] SHA1_BYTES128_FROM_BYTELIST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `64 * j + 0 = 64 * j`] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE
      `64*j + 4*0 + 0 = 64 * j + 0 /\
       64*j + 4*0 + 1 = 64 * j + 1 /\
       64*j + 4*0 + 2 = 64 * j + 2 /\
       64*j + 4*0 + 3 = 64 * j + 3 /\
       64*j + 4*1 + 0 = 64 * j + 4 /\
       64*j + 4*1 + 1 = 64 * j + 5 /\
       64*j + 4*1 + 2 = 64 * j + 6 /\
       64*j + 4*1 + 3 = 64 * j + 7 /\
       64*j + 4*2 + 0 = 64 * j + 8 /\
       64*j + 4*2 + 1 = 64 * j + 9 /\
       64*j + 4*2 + 2 = 64 * j + 10 /\
       64*j + 4*2 + 3 = 64 * j + 11 /\
       64*j + 4*3 + 0 = 64 * j + 12 /\
       64*j + 4*3 + 1 = 64 * j + 13 /\
       64*j + 4*3 + 2 = 64 * j + 14 /\
       64*j + 4*3 + 3 = 64 * j + 15`] THEN
    REWRITE_TAC[ARITH_RULE `64 * j + 0 = 64 * j`];
    ALL_TAC] THEN
  CONJ_TAC THENL [
    MP_TAC(SPECL [`x:armstate`; `data_ptr:int64`; `data_bytes:byte list`;
                  `64 * j + 16`] SHA1_BYTES128_FROM_BYTELIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE
      `64*j + 4*4 + 0 = 64*j + 16 /\
       64*j + 4*4 + 1 = (64*j + 16) + 1 /\
       64*j + 4*4 + 2 = (64*j + 16) + 2 /\
       64*j + 4*4 + 3 = (64*j + 16) + 3 /\
       64*j + 4*5 + 0 = (64*j + 16) + 4 /\
       64*j + 4*5 + 1 = (64*j + 16) + 5 /\
       64*j + 4*5 + 2 = (64*j + 16) + 6 /\
       64*j + 4*5 + 3 = (64*j + 16) + 7 /\
       64*j + 4*6 + 0 = (64*j + 16) + 8 /\
       64*j + 4*6 + 1 = (64*j + 16) + 9 /\
       64*j + 4*6 + 2 = (64*j + 16) + 10 /\
       64*j + 4*6 + 3 = (64*j + 16) + 11 /\
       64*j + 4*7 + 0 = (64*j + 16) + 12 /\
       64*j + 4*7 + 1 = (64*j + 16) + 13 /\
       64*j + 4*7 + 2 = (64*j + 16) + 14 /\
       64*j + 4*7 + 3 = (64*j + 16) + 15`];
    ALL_TAC] THEN
  CONJ_TAC THENL [
    MP_TAC(SPECL [`x:armstate`; `data_ptr:int64`; `data_bytes:byte list`;
                  `64 * j + 32`] SHA1_BYTES128_FROM_BYTELIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE
      `64*j + 4*8 + 0 = 64*j + 32 /\
       64*j + 4*8 + 1 = (64*j + 32) + 1 /\
       64*j + 4*8 + 2 = (64*j + 32) + 2 /\
       64*j + 4*8 + 3 = (64*j + 32) + 3 /\
       64*j + 4*9 + 0 = (64*j + 32) + 4 /\
       64*j + 4*9 + 1 = (64*j + 32) + 5 /\
       64*j + 4*9 + 2 = (64*j + 32) + 6 /\
       64*j + 4*9 + 3 = (64*j + 32) + 7 /\
       64*j + 4*10 + 0 = (64*j + 32) + 8 /\
       64*j + 4*10 + 1 = (64*j + 32) + 9 /\
       64*j + 4*10 + 2 = (64*j + 32) + 10 /\
       64*j + 4*10 + 3 = (64*j + 32) + 11 /\
       64*j + 4*11 + 0 = (64*j + 32) + 12 /\
       64*j + 4*11 + 1 = (64*j + 32) + 13 /\
       64*j + 4*11 + 2 = (64*j + 32) + 14 /\
       64*j + 4*11 + 3 = (64*j + 32) + 15`];
    MP_TAC(SPECL [`x:armstate`; `data_ptr:int64`; `data_bytes:byte list`;
                  `64 * j + 48`] SHA1_BYTES128_FROM_BYTELIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE
      `64*j + 4*12 + 0 = 64*j + 48 /\
       64*j + 4*12 + 1 = (64*j + 48) + 1 /\
       64*j + 4*12 + 2 = (64*j + 48) + 2 /\
       64*j + 4*12 + 3 = (64*j + 48) + 3 /\
       64*j + 4*13 + 0 = (64*j + 48) + 4 /\
       64*j + 4*13 + 1 = (64*j + 48) + 5 /\
       64*j + 4*13 + 2 = (64*j + 48) + 6 /\
       64*j + 4*13 + 3 = (64*j + 48) + 7 /\
       64*j + 4*14 + 0 = (64*j + 48) + 8 /\
       64*j + 4*14 + 1 = (64*j + 48) + 9 /\
       64*j + 4*14 + 2 = (64*j + 48) + 10 /\
       64*j + 4*14 + 3 = (64*j + 48) + 11 /\
       64*j + 4*15 + 0 = (64*j + 48) + 12 /\
       64*j + 4*15 + 1 = (64*j + 48) + 13 /\
       64*j + 4*15 + 2 = (64*j + 48) + 14 /\
       64*j + 4*15 + 3 = (64*j + 48) + 15`]
  ]);;
