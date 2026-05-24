(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas connecting the kernel-level CRC32C specification          *)
(* (arm/proofs/utils/crc32c_spec.ml) to the ARM hardware-instruction model   *)
(* (arm/proofs/instruction.ml).                                              *)
(*                                                                           *)
(* The spec-side definitions `crc32c_step` and `crc32c_byte` are             *)
(* structurally identical to the hardware-side `crc32c_bit` and              *)
(* `crc32c_hw_step` (modulo the `crc32c_poly_refl` constant), so the load-   *)
(* bearing single-byte bridge collapses by REWRITE.                          *)
(*                                                                           *)
(* The 2/4/8-byte bridges express the chain of `crc32c_hw_step` applications *)
(* produced by `arm_CRC32C{H,W,X}` as a `crc32c_bytes` fold over the         *)
(* little-endian byte decomposition of the source operand. This is the form  *)
(* Phase 5 onwards consumes: after `ARM_STEPS_TAC`, the state contains the   *)
(* nested `crc32c_hw_step` chain on the LHS, which the bridge rewrites to    *)
(* `crc32c_bytes acc [byte_0; byte_1; ...]` on the RHS — matching the        *)
(* spec-level fold.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Step bridge: the spec's bit-level step equals the hardware's bit-level    *)
(* step. This holds by definition modulo `crc32c_poly_refl`.                 *)
(* ------------------------------------------------------------------------- *)

let CRC32C_STEP_BRIDGE = prove
 (`!acc:int32 b. crc32c_step acc b = crc32c_bit acc b`,
  REWRITE_TAC[crc32c_step; crc32c_bit; crc32c_poly_refl]);;

(* ------------------------------------------------------------------------- *)
(* Single-byte bridge: the spec's `crc32c_byte` equals the hardware's        *)
(* `crc32c_hw_step` (8 bit-steps over the byte, LSB-first).                  *)
(* ------------------------------------------------------------------------- *)

let CRC32CB_BRIDGE = prove
 (`!acc:int32 b:byte. crc32c_hw_step acc b = crc32c_byte acc b`,
  REWRITE_TAC[crc32c_hw_step; crc32c_byte; CRC32C_STEP_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Two-byte bridge: the chain of two `crc32c_hw_step` applications produced  *)
(* by `arm_CRC32CH` equals the `crc32c_bytes` fold over the little-endian    *)
(* byte decomposition of the 16-bit source.                                  *)
(* ------------------------------------------------------------------------- *)

let CRC32CH_BRIDGE = prove
 (`!acc:int32 m:int32.
        crc32c_hw_step
         (crc32c_hw_step acc (word_subword m (0,8):byte))
         (word_subword m (8,8):byte) =
        crc32c_bytes acc
         [word_subword m (0,8):byte; word_subword m (8,8):byte]`,
  REWRITE_TAC[crc32c_bytes; CRC32CB_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Four-byte bridge: as CRC32CH_BRIDGE but for `arm_CRC32CW`.                 *)
(* ------------------------------------------------------------------------- *)

let CRC32CW_BRIDGE = prove
 (`!acc:int32 m:int32.
        crc32c_hw_step
         (crc32c_hw_step
          (crc32c_hw_step
           (crc32c_hw_step acc (word_subword m (0,8):byte))
           (word_subword m (8,8):byte))
          (word_subword m (16,8):byte))
         (word_subword m (24,8):byte) =
        crc32c_bytes acc
         [word_subword m (0,8):byte; word_subword m (8,8):byte;
          word_subword m (16,8):byte; word_subword m (24,8):byte]`,
  REWRITE_TAC[crc32c_bytes; CRC32CB_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Eight-byte bridge: as CRC32CH_BRIDGE but for `arm_CRC32CX`. The source     *)
(* operand is an int64 here (mirroring `arm_CRC32CX`).                       *)
(* ------------------------------------------------------------------------- *)

let CRC32CX_BRIDGE = prove
 (`!acc:int32 m:int64.
        crc32c_hw_step
         (crc32c_hw_step
          (crc32c_hw_step
           (crc32c_hw_step
            (crc32c_hw_step
             (crc32c_hw_step
              (crc32c_hw_step
               (crc32c_hw_step acc (word_subword m (0,8):byte))
                              (word_subword m (8,8):byte))
                             (word_subword m (16,8):byte))
                            (word_subword m (24,8):byte))
                           (word_subword m (32,8):byte))
                          (word_subword m (40,8):byte))
                         (word_subword m (48,8):byte))
                        (word_subword m (56,8):byte) =
        crc32c_bytes acc
         [word_subword m (0,8):byte; word_subword m (8,8):byte;
          word_subword m (16,8):byte; word_subword m (24,8):byte;
          word_subword m (32,8):byte; word_subword m (40,8):byte;
          word_subword m (48,8):byte; word_subword m (56,8):byte]`,
  REWRITE_TAC[crc32c_bytes; CRC32CB_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for the bytes64-from-bytelist bridge below.                 *)
(*                                                                           *)
(* `NUM_OF_BYTELIST_BS_DECOMP` decomposes `num_of_bytelist bs` as            *)
(* prefix + 2^(8n) * (middle + 2^(8k) * suffix) given `n + k <= LENGTH bs`.  *)
(*                                                                           *)
(* `NUM_OF_BYTELIST_SUB_LIST` extracts the middle slice via DIV/MOD on the   *)
(* full numeric value of the bytelist.                                       *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_BYTELIST_APPEND_LOCAL = prove
 (`!l1 l2. num_of_bytelist (APPEND l1 l2) =
           num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
   LIST_INDUCT_TAC THENL
   [ REWRITE_TAC[APPEND; LENGTH; num_of_bytelist; MULT_CLAUSES; EXP; ADD_CLAUSES];
     REWRITE_TAC[APPEND; LENGTH; num_of_bytelist] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[MULT_SUC; EXP_ADD] THEN
     REWRITE_TAC[MULT_ASSOC; LEFT_ADD_DISTRIB] THEN
     ARITH_TAC]);;

let POW256_EQ_POW2 = prove
 (`!n. (256:num) EXP n = 2 EXP (8 * n)`,
  GEN_TAC THEN REWRITE_TAC[EXP_MULT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC NUM_REDUCE_CONV);;

let NUM_OF_BYTELIST_BS_DECOMP = prove
 (`!(bs:byte list) n k.
        n + k <= LENGTH bs
        ==> num_of_bytelist bs =
            num_of_bytelist (SUB_LIST(0,n) bs) +
            2 EXP (8 * n) *
            (num_of_bytelist (SUB_LIST(n,k) bs) +
             2 EXP (8 * k) *
             num_of_bytelist (SUB_LIST(n + k, LENGTH bs - n - k) bs))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM SUB_LIST_LENGTH] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, LENGTH (bs:byte list)) bs =
     APPEND (SUB_LIST(0, n) bs)
            (APPEND (SUB_LIST(n, k) bs)
                    (SUB_LIST(n + k, LENGTH bs - n - k) bs))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `SUB_LIST(0, LENGTH (bs:byte list)) bs =
                  SUB_LIST(0, n + (LENGTH bs - n)) bs`
      SUBST1_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBST1_TAC(ISPECL [`bs:byte list`; `n:num`; `LENGTH (bs:byte list) - n`;
                       `0:num`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `SUB_LIST(n, LENGTH (bs:byte list) - n) bs =
                  SUB_LIST(n, k + (LENGTH bs - n - k)) bs`
      SUBST1_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUB_LIST_SPLIT];
    ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_APPEND_LOCAL] THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
  SUBGOAL_THEN `MIN n (LENGTH (bs:byte list)) = n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MIN k (LENGTH (bs:byte list) - n) = k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REFL_TAC);;

let NUM_OF_BYTELIST_SUB_LIST = prove
 (`!(bs:byte list) n k.
        n + k <= LENGTH bs
        ==> num_of_bytelist (SUB_LIST (n, k) bs) =
            (num_of_bytelist bs DIV (2 EXP (8 * n))) MOD (2 EXP (8 * k))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP NUM_OF_BYTELIST_BS_DECOMP) THEN
  MP_TAC(ISPEC `SUB_LIST(0, n) (bs:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `SUB_LIST(n, k) (bs:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
  SUBGOAL_THEN `MIN n (LENGTH (bs:byte list)) = n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MIN k (LENGTH (bs:byte list) - n) = k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[POW256_EQ_POW2] THEN
  ABBREV_TAC `np = num_of_bytelist (SUB_LIST(0,n) (bs:byte list))` THEN
  ABBREV_TAC `nm = num_of_bytelist (SUB_LIST(n,k) (bs:byte list))` THEN
  ABBREV_TAC
    `ns = num_of_bytelist (SUB_LIST(n + k, LENGTH (bs:byte list) - n - k) bs)` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_2_NE_0] THEN
  ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;
