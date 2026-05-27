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

(* ------------------------------------------------------------------------- *)
(* BYTES64_FROM_BYTELIST: extracts an 8-byte aligned sub-window from a       *)
(* bytelist as a bytes64 (int64) read. This is the per-iteration bridge      *)
(* used when applying CRC32C_LOOP16_CORRECT as a big-step inside an outer    *)
(* proof that has the source buffer typed as a `bytelist`.                   *)
(* ------------------------------------------------------------------------- *)

let BYTES64_FROM_BYTELIST = prove
 (`!(a:int64) (s:armstate) (bs:byte list) n.
        read (memory :> bytelist (a, LENGTH bs)) s = bs /\
        n + 8 <= LENGTH bs
        ==> read (memory :> bytes64 (word_add a (word n))) s =
            word (num_of_bytelist (SUB_LIST(n, 8) bs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes64; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
    `read (bytes (word_add (a:int64) (word n), 8)) (read memory s) =
     (read (bytes (a, LENGTH (bs:byte list))) (read memory s) DIV 2 EXP (8 * n))
     MOD 2 EXP (8 * 8)`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
    SUBGOAL_THEN `MIN (LENGTH (bs:byte list) - n) 8 = 8` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `read (bytes (a, LENGTH (bs:byte list))) (read memory s) = num_of_bytelist bs`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [READ_BYTELIST_EQ_BYTES]) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bs:byte list`; `n:num`; `8:num`] NUM_OF_BYTELIST_SUB_LIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* BYTES8_FROM_BYTELIST: 1-byte analogue of BYTES64_FROM_BYTELIST. Used      *)
(* when a single LDRB reads from inside a region whose bytelist contents    *)
(* are pinned in the precondition.                                           *)
(* ------------------------------------------------------------------------- *)

let BYTES8_FROM_BYTELIST = prove
 (`!(a:int64) (s:armstate) (bs:byte list) n.
        read (memory :> bytelist (a, LENGTH bs)) s = bs /\
        n + 1 <= LENGTH bs
        ==> read (memory :> bytes8 (word_add a (word n))) s =
            word (num_of_bytelist (SUB_LIST(n, 1) bs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
    `read (bytes (word_add (a:int64) (word n), 1)) (read memory s) =
     (read (bytes (a, LENGTH (bs:byte list))) (read memory s) DIV 2 EXP (8 * n))
     MOD 2 EXP (8 * 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
    SUBGOAL_THEN `MIN (LENGTH (bs:byte list) - n) 1 = 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `read (bytes (a, LENGTH (bs:byte list))) (read memory s) = num_of_bytelist bs`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [READ_BYTELIST_EQ_BYTES]) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bs:byte list`; `n:num`; `1:num`] NUM_OF_BYTELIST_SUB_LIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* MEMORY_BYTELIST_1_EQ_BYTES8: a 1-byte bytelist read equals a single-byte  *)
(* bytes8 read packaged as a singleton list. Useful when bridging post-STRB  *)
(* state (where bytes8 = word 0) back to the bytelist form expected by the   *)
(* outer postcondition.                                                      *)
(* ------------------------------------------------------------------------- *)

let MEMORY_BYTELIST_1_EQ_BYTES8 = prove
 (`!(a:int64) (s:armstate).
        read (memory :> bytelist (a, 1)) s =
        [(read (memory :> bytes8 a) s):byte]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ONE; bytelist_clauses; READ_COMPONENT_COMPOSE; bytes8;
              asword; through; read; CONS_11] THEN
  REWRITE_TAC[GSYM ONE; READ_BYTES_1] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* WORD_SUBWORD_ZX_BYTE_TRIVIAL: round-trip a byte through a word_zx int32   *)
(* and a low-byte word_subword. The CRC32CB ARM model's data path passes the *)
(* loaded byte through word_zx into the int32 W-register, then crc32c_hw    *)
(* extracts the byte via word_subword (0,8). This bridge lets us recover    *)
(* the raw byte for matching against `crc32c_bytes`.                         *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_ZX_BYTE_TRIVIAL = prove
 (`!b:byte. word_subword ((word_zx b):int32) (0, 8):byte = b`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE1_X_UPDATE: per-buffer X-register update fact for residue=1 case   *)
(* of the tail-block. Given a buffer `bs` of length n+1, the CRC32CB output  *)
(* on `acc = crc32c_bytes 0xFFFFFFFF (SUB_LIST(0,n) bs)` consuming the byte  *)
(* loaded from `bytes8 (a + n)` (which equals the n-th byte of bs by         *)
(* BYTES8_FROM_BYTELIST applied to the suffix bytelist) collapses to         *)
(* `crc32c_bytes 0xFFFFFFFF bs` — i.e. the full-buffer CRC.                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* SUFFIX_BYTELIST_TO_BYTES8: a 1-byte suffix-bytelist read gives the same   *)
(* underlying byte as the bytes8 read at that address. This is the residue=1 *)
(* per-buffer adapter: from the cut-state's suffix-bytelist hypothesis        *)
(*    read (memory :> bytelist (a + word k, 1)) s = SUB_LIST(k, 1) bs        *)
(* (where LENGTH bs = k + 1), derive                                          *)
(*    read (memory :> bytes8 (a + word k)) s =                                *)
(*      word(num_of_bytelist (SUB_LIST(k, 1) bs))                             *)
(* ------------------------------------------------------------------------- *)

let SUFFIX_BYTELIST_TO_BYTES8 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 1 /\
        read (memory :> bytelist (word_add a (word k), 1)) s =
          SUB_LIST (k, 1) bs
        ==> read (memory :> bytes8 (word_add a (word k))) s =
            word(num_of_bytelist (SUB_LIST(k, 1) bs))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add a (word k):int64`; `s:armstate`;
                 `SUB_LIST(k, 1) (bs:byte list)`; `0:num`]
                BYTES8_FROM_BYTELIST) THEN
  SUBGOAL_THEN `LENGTH (SUB_LIST (k,1) (bs:byte list)) = 1` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 1) (SUB_LIST(k, 1) (bs:byte list)) =
     SUB_LIST(k, 1) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE1_MEMORY_CLOSE: per-buffer memory zero-projection for residue=1.   *)
(* Composes the orthogonal-prefix lift (`bytelist (a, 16*iters) s = ZEROES`) *)
(* with the post-STRB tail byte (`bytes8 (a + 16*iters) s = word 0`) into    *)
(* the full-buffer zero-fill `bytelist (a, 16*iters + 1) s = ZEROES`.        *)
(* ------------------------------------------------------------------------- *)

let REPLICATE_ZERO_PLUS_ONE = prove
 (`!k. REPLICATE (k + 1) (word 0:byte) =
       APPEND (REPLICATE k (word 0:byte)) [word 0:byte]`,
  INDUCT_TAC THEN
  REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES;
              ARITH_RULE `0 + 1 = SUC 0`;
              ARITH_RULE `SUC k + 1 = SUC(k + 1)`] THEN
  ASM_REWRITE_TAC[]);;

let RESIDUE1_MEMORY_CLOSE = prove
 (`!(a:int64) (s:armstate) k.
        read (memory :> bytelist (a, k)) s = REPLICATE k (word 0) /\
        read (memory :> bytes8 (word_add a (word k))) s = word 0
        ==> read (memory :> bytelist (a, k + 1)) s =
            REPLICATE (k + 1) (word 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  SUBGOAL_THEN
    `k + 1 = LENGTH (APPEND (REPLICATE k (word 0:byte)) [word 0:byte])`
  SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
  REWRITE_TAC[LENGTH_REPLICATE; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      ACCEPT_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE] th));
    ONCE_REWRITE_TAC[GSYM(SPEC_ALL READ_COMPONENT_COMPOSE)] THEN
    REWRITE_TAC[MEMORY_BYTELIST_1_EQ_BYTES8] THEN
    ASM_REWRITE_TAC[]]);;

let RESIDUE1_X_UPDATE = prove
 (`!(bs:byte list) n.
        LENGTH bs = n + 1
        ==> crc32c_hw_step
              (crc32c_bytes (word 0xFFFFFFFF:int32) (SUB_LIST(0, n) bs))
              (word_subword
                (word_zx
                  (word(num_of_bytelist (SUB_LIST(n, 1) bs)):byte):int32)
                (0, 8):byte)
            = crc32c_bytes (word 0xFFFFFFFF:int32) bs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CRC32CB_BRIDGE; WORD_SUBWORD_ZX_BYTE_TRIVIAL] THEN
  SUBGOAL_THEN `SUB_LIST (n, 1) (bs:byte list) = [EL n bs]` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUB_LIST_1;
      ARITH_RULE `LENGTH (bs:byte list) = n + 1 ==> n < LENGTH bs`];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `word (num_of_bytelist [EL n (bs:byte list)]) = EL n bs:byte`
  SUBST1_TAC THENL
   [REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `crc32c_bytes (word 0xFFFFFFFF:int32)
      (APPEND (SUB_LIST(0,n) (bs:byte list)) [EL n bs])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[crc32c_bytes_APPEND; crc32c_bytes];
    AP_TERM_TAC THEN
    SUBGOAL_THEN `[EL n (bs:byte list)] = SUB_LIST(n, 1) bs` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SUB_LIST_1;
        ARITH_RULE `LENGTH (bs:byte list) = n + 1 ==> n < LENGTH bs`];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bs:byte list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE
      `LENGTH (bs:byte list) = n + 1 ==> LENGTH bs - n = 1`]]);;

(* ------------------------------------------------------------------------- *)
(* BYTES16_FROM_BYTELIST: 2-byte analogue of BYTES8_FROM_BYTELIST. Used      *)
(* on the residue=2 path where LDRH reads a 16-bit halfword from inside a   *)
(* region whose bytelist contents are pinned in the precondition.            *)
(* ------------------------------------------------------------------------- *)

let BYTES16_FROM_BYTELIST = prove
 (`!(a:int64) (s:armstate) (bs:byte list) n.
        read (memory :> bytelist (a, LENGTH bs)) s = bs /\
        n + 2 <= LENGTH bs
        ==> read (memory :> bytes16 (word_add a (word n))) s =
            word (num_of_bytelist (SUB_LIST(n, 2) bs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes16; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
    `read (bytes (word_add (a:int64) (word n), 2)) (read memory s) =
     (read (bytes (a, LENGTH (bs:byte list))) (read memory s) DIV 2 EXP (8 * n))
     MOD 2 EXP (8 * 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
    SUBGOAL_THEN `MIN (LENGTH (bs:byte list) - n) 2 = 2` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `read (bytes (a, LENGTH (bs:byte list))) (read memory s) = num_of_bytelist bs`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [READ_BYTELIST_EQ_BYTES]) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bs:byte list`; `n:num`; `2:num`] NUM_OF_BYTELIST_SUB_LIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* MEMORY_BYTELIST_2_EQ_BYTES16: a 2-byte bytelist read equals the byte     *)
(* decomposition of a single bytes16 read. Useful when bridging post-STRH    *)
(* state (where bytes16 = word 0) back to the bytelist form expected by the   *)
(* outer postcondition.                                                      *)
(* ------------------------------------------------------------------------- *)

let MEMORY_BYTELIST_2_EQ_BYTES16 = prove
 (`!(a:int64) (s:armstate).
        read (memory :> bytelist (a, 2)) s =
        [word_subword (read (memory :> bytes16 a) s) (0,8):byte;
         word_subword (read (memory :> bytes16 a) s) (8,8):byte]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC (SUC 0)`; bytelist_clauses;
              READ_COMPONENT_COMPOSE; bytes16;
              asword; through; read; CONS_11] THEN
  REWRITE_TAC[ARITH_RULE `SUC (SUC 0) = 2`; ARITH_RULE `SUC 0 = 1`] THEN
  REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; READ_BYTES_COMBINE; READ_BYTES_1] THEN
  ABBREV_TAC `b0:byte = read memory s (a:int64)` THEN
  ABBREV_TAC `b1:byte = read memory s (word_add (a:int64) (word 1))` THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) + 256 * val (b1:byte)) MOD 65536 =
     val b0 + 256 * val b1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_1] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* SUFFIX_BYTELIST_TO_BYTES16: a 2-byte suffix-bytelist read gives the same  *)
(* underlying halfword as the bytes16 read at that address. This is the      *)
(* residue=2 per-buffer adapter: from the cut-state's suffix-bytelist hyp     *)
(*    read (memory :> bytelist (a + word k, 2)) s = SUB_LIST(k, 2) bs        *)
(* (where LENGTH bs = k + 2), derive                                          *)
(*    read (memory :> bytes16 (a + word k)) s =                               *)
(*      word(num_of_bytelist (SUB_LIST(k, 2) bs))                             *)
(* ------------------------------------------------------------------------- *)

let SUFFIX_BYTELIST_TO_BYTES16 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 2 /\
        read (memory :> bytelist (word_add a (word k), 2)) s =
          SUB_LIST (k, 2) bs
        ==> read (memory :> bytes16 (word_add a (word k))) s =
            word(num_of_bytelist (SUB_LIST(k, 2) bs))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add a (word k):int64`; `s:armstate`;
                 `SUB_LIST(k, 2) (bs:byte list)`; `0:num`]
                BYTES16_FROM_BYTELIST) THEN
  SUBGOAL_THEN `LENGTH (SUB_LIST (k,2) (bs:byte list)) = 2` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 2) (SUB_LIST(k, 2) (bs:byte list)) =
     SUB_LIST(k, 2) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE2_X_UPDATE: per-buffer X-register update fact for residue=2 case   *)
(* of the tail-block. Given a buffer `bs` of length n+2, the CRC32CH chain   *)
(* output on `acc = crc32c_bytes 0xFFFFFFFF (SUB_LIST(0,n) bs)` consuming    *)
(* the halfword loaded from `bytes16 (a + n)` (which equals the bytes at     *)
(* positions n,n+1 of bs by SUFFIX_BYTELIST_TO_BYTES16) collapses to         *)
(* `crc32c_bytes 0xFFFFFFFF bs` — i.e. the full-buffer CRC.                  *)
(*                                                                           *)
(* The kernel's W-register data path passes the loaded int16 through         *)
(* word_zx into an int32, so the CRC32CH source operand is the int32         *)
(* `word_zx (word(num_of_bytelist (SUB_LIST(n,2) bs)):int16)`, whose         *)
(* low 16 bits split as the n-th and (n+1)-th bytes of bs (LSB-first).       *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_ZX_INT16_BYTE0 = prove
 (`!w:int16. word_subword ((word_zx w):int32) (0, 8):byte =
             word_subword w (0, 8)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_ZX_INT16_BYTE1 = prove
 (`!w:int16. word_subword ((word_zx w):int32) (8, 8):byte =
             word_subword w (8, 8)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_BYTELIST2_LSB = prove
 (`!b0 b1:byte.
       word_subword
        (word(num_of_bytelist [b0; b1]):int16) (0, 8):byte = b0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) + 256 * val (b1:byte)) MOD 65536 =
     val b0 + 256 * val b1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_1] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST2_MSB = prove
 (`!b0 b1:byte.
       word_subword
        (word(num_of_bytelist [b0; b1]):int16) (8, 8):byte = b1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) + 256 * val (b1:byte)) MOD 65536 =
     val b0 + 256 * val b1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_LT]);;

let LENGTH_EQ_2_DECOMP = prove
 (`!l:byte list. LENGTH l = 2 ==> ?b0 b1. l = [b0; b1]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC 1`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let RESIDUE2_X_UPDATE = prove
 (`!(bs:byte list) n.
        LENGTH bs = n + 2
        ==> crc32c_hw_step
              (crc32c_hw_step
                (crc32c_bytes (word 0xFFFFFFFF:int32) (SUB_LIST(0, n) bs))
                (word_subword
                  (word_zx
                    (word(num_of_bytelist
                            (SUB_LIST(n, 2) bs)):int16):int32)
                  (0, 8):byte))
              (word_subword
                (word_zx
                  (word(num_of_bytelist
                          (SUB_LIST(n, 2) bs)):int16):int32)
                (8, 8):byte)
            = crc32c_bytes (word 0xFFFFFFFF:int32) bs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_SUBWORD_ZX_INT16_BYTE0; WORD_SUBWORD_ZX_INT16_BYTE1] THEN
  SUBGOAL_THEN `?b0 b1:byte. SUB_LIST (n, 2) (bs:byte list) = [b0; b1]`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_EQ_2_DECOMP THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTELIST2_LSB; WORD_SUBWORD_BYTELIST2_MSB] THEN
  REWRITE_TAC[CRC32CB_BRIDGE] THEN
  TRANS_TAC EQ_TRANS
   `crc32c_bytes (word 0xFFFFFFFF:int32)
      (APPEND (SUB_LIST(0,n) (bs:byte list)) [b0; b1])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[crc32c_bytes_APPEND; crc32c_bytes];
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`bs:byte list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE
      `LENGTH (bs:byte list) = n + 2 ==> LENGTH bs - n = 2`]]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE2_MEMORY_CLOSE: per-buffer memory zero-projection for residue=2.   *)
(* Composes the orthogonal-prefix lift (`bytelist (a, 16*iters) s = ZEROES`) *)
(* with the post-STRH tail halfword (`bytes16 (a + 16*iters) s = word 0`)    *)
(* into the full-buffer zero-fill `bytelist (a, 16*iters + 2) s = ZEROES`.   *)
(* ------------------------------------------------------------------------- *)

let REPLICATE_ZERO_PLUS_TWO = prove
 (`!k. REPLICATE (k + 2) (word 0:byte) =
       APPEND (REPLICATE k (word 0:byte))
              [word 0:byte; word 0:byte]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `k + 2 = (k + 1) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let RESIDUE2_MEMORY_CLOSE = prove
 (`!(a:int64) (s:armstate) k.
        read (memory :> bytelist (a, k)) s = REPLICATE k (word 0) /\
        read (memory :> bytes16 (word_add a (word k))) s = word 0
        ==> read (memory :> bytelist (a, k + 2)) s =
            REPLICATE (k + 2) (word 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_TWO] THEN
  SUBGOAL_THEN
    `k + 2 = LENGTH (APPEND (REPLICATE k (word 0:byte))
                            [word 0:byte; word 0:byte])`
  SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
  REWRITE_TAC[LENGTH_REPLICATE; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      ACCEPT_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE] th));
    ONCE_REWRITE_TAC[GSYM(SPEC_ALL READ_COMPONENT_COMPOSE)] THEN
    REWRITE_TAC[MEMORY_BYTELIST_2_EQ_BYTES16] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONS_11] THEN CONV_TAC WORD_BLAST]);;

(* ------------------------------------------------------------------------- *)
(* BYTES32_FROM_BYTELIST: 4-byte analogue of BYTES16_FROM_BYTELIST. Used     *)
(* on the residue=4 path where LDR W reads a 32-bit word from inside a       *)
(* region whose bytelist contents are pinned in the precondition.            *)
(* ------------------------------------------------------------------------- *)

let BYTES32_FROM_BYTELIST = prove
 (`!(a:int64) (s:armstate) (bs:byte list) n.
        read (memory :> bytelist (a, LENGTH bs)) s = bs /\
        n + 4 <= LENGTH bs
        ==> read (memory :> bytes32 (word_add a (word n))) s =
            word (num_of_bytelist (SUB_LIST(n, 4) bs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
    `read (bytes (word_add (a:int64) (word n), 4)) (read memory s) =
     (read (bytes (a, LENGTH (bs:byte list))) (read memory s) DIV 2 EXP (8 * n))
     MOD 2 EXP (8 * 4)`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
    SUBGOAL_THEN `MIN (LENGTH (bs:byte list) - n) 4 = 4` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `read (bytes (a, LENGTH (bs:byte list))) (read memory s) = num_of_bytelist bs`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [READ_BYTELIST_EQ_BYTES]) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bs:byte list`; `n:num`; `4:num`] NUM_OF_BYTELIST_SUB_LIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* MEMORY_BYTELIST_4_EQ_BYTES32: a 4-byte bytelist read equals the byte     *)
(* decomposition of a single bytes32 read. Useful when bridging post-STR   *)
(* state (where bytes32 = word 0) back to the bytelist form expected by the *)
(* outer postcondition.                                                     *)
(* ------------------------------------------------------------------------- *)

let MEMORY_BYTELIST_4_EQ_BYTES32 = prove
 (`!(a:int64) (s:armstate).
        read (memory :> bytelist (a, 4)) s =
        [word_subword (read (memory :> bytes32 a) s) (0,8):byte;
         word_subword (read (memory :> bytes32 a) s) (8,8):byte;
         word_subword (read (memory :> bytes32 a) s) (16,8):byte;
         word_subword (read (memory :> bytes32 a) s) (24,8):byte]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC (SUC (SUC (SUC 0)))`; bytelist_clauses;
              READ_COMPONENT_COMPOSE; bytes32;
              asword; through; read; CONS_11] THEN
  REWRITE_TAC[ARITH_RULE `SUC (SUC (SUC (SUC 0))) = 4`;
              ARITH_RULE `SUC (SUC (SUC 0)) = 3`;
              ARITH_RULE `SUC (SUC 0) = 2`;
              ARITH_RULE `SUC 0 = 1`] THEN
  REWRITE_TAC[ARITH_RULE `4 = 1 + (1 + (1 + 1))`;
              ARITH_RULE `3 = 1 + (1 + 1)`;
              ARITH_RULE `2 = 1 + 1`;
              READ_BYTES_COMBINE; READ_BYTES_1] THEN
  REWRITE_TAC[
    WORD_RULE `word_add (word_add (a:int64) (word 1)) (word 1) =
               word_add a (word 2)`;
    WORD_RULE `word_add (word_add (word_add (a:int64) (word 1)) (word 1))
                        (word 1) = word_add a (word 3)`] THEN
  ABBREV_TAC `b0:byte = read memory s (a:int64)` THEN
  ABBREV_TAC `b1:byte = read memory s (word_add (a:int64) (word 1))` THEN
  ABBREV_TAC `b2:byte = read memory s (word_add (a:int64) (word 2))` THEN
  ABBREV_TAC `b3:byte = read memory s (word_add (a:int64) (word 3))` THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
             256 * (val (b2:byte) + 256 * val (b3:byte)))) MOD 4294967296 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * val b3))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_1] THEN
  REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THENL
   [(* byte 0: ... MOD 256 = b0 *)
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    (* byte 1: (... DIV 256) MOD 256 = b1 *)
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 2: (... DIV 65536) MOD 256 = b2 *)
    SUBGOAL_THEN `(65536:num) = 256 * 256` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 3: (... DIV 16777216) MOD 256 = b3 *)
    SUBGOAL_THEN `(16777216:num) = 256 * (256 * 256)` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* SUFFIX_BYTELIST_TO_BYTES32: a 4-byte suffix-bytelist read gives the same  *)
(* underlying word as the bytes32 read at that address. This is the         *)
(* residue=4 per-buffer adapter: from the cut-state's suffix-bytelist hyp    *)
(*    read (memory :> bytelist (a + word k, 4)) s = SUB_LIST(k, 4) bs        *)
(* (where LENGTH bs = k + 4), derive                                         *)
(*    read (memory :> bytes32 (a + word k)) s =                              *)
(*      word(num_of_bytelist (SUB_LIST(k, 4) bs))                            *)
(* ------------------------------------------------------------------------- *)

let SUFFIX_BYTELIST_TO_BYTES32 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 4 /\
        read (memory :> bytelist (word_add a (word k), 4)) s =
          SUB_LIST (k, 4) bs
        ==> read (memory :> bytes32 (word_add a (word k))) s =
            word(num_of_bytelist (SUB_LIST(k, 4) bs))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add a (word k):int64`; `s:armstate`;
                 `SUB_LIST(k, 4) (bs:byte list)`; `0:num`]
                BYTES32_FROM_BYTELIST) THEN
  SUBGOAL_THEN `LENGTH (SUB_LIST (k,4) (bs:byte list)) = 4` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 4) (SUB_LIST(k, 4) (bs:byte list)) =
     SUB_LIST(k, 4) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE4_X_UPDATE: per-buffer X-register update fact for residue=4 case   *)
(* of the tail-block. Given a buffer `bs` of length n+4, the CRC32CW chain   *)
(* output on `acc = crc32c_bytes 0xFFFFFFFF (SUB_LIST(0,n) bs)` consuming    *)
(* the 4-byte word loaded from `bytes32 (a + n)` (which equals the bytes at  *)
(* positions n..n+3 of bs by SUFFIX_BYTELIST_TO_BYTES32) collapses to        *)
(* `crc32c_bytes 0xFFFFFFFF bs` — i.e. the full-buffer CRC.                  *)
(*                                                                           *)
(* The kernel's W-register data path passes the loaded int32 directly into   *)
(* CRC32CW (no word_zx); the 4 word_subword extractions (0,8) (8,8) (16,8)  *)
(* (24,8) of `word(num_of_bytelist (SUB_LIST(n,4) bs)):int32` are the four   *)
(* bytes of bs at positions n..n+3 (LSB-first).                              *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_BYTELIST4_BYTE0 = prove
 (`!b0 b1 b2 b3:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3]):int32) (0, 8):byte = b0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
             256 * (val (b2:byte) + 256 * val (b3:byte)))) MOD 4294967296 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * val b3))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_1] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST4_BYTE1 = prove
 (`!b0 b1 b2 b3:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3]):int32) (8, 8):byte = b1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
             256 * (val (b2:byte) + 256 * val (b3:byte)))) MOD 4294967296 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * val b3))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST4_BYTE2 = prove
 (`!b0 b1 b2 b3:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3]):int32) (16, 8):byte = b2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
             256 * (val (b2:byte) + 256 * val (b3:byte)))) MOD 4294967296 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * val b3))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(65536:num) = 256 * 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST4_BYTE3 = prove
 (`!b0 b1 b2 b3:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3]):int32) (24, 8):byte = b3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
             256 * (val (b2:byte) + 256 * val (b3:byte)))) MOD 4294967296 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * val b3))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(16777216:num) = 256 * (256 * 256)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let LENGTH_EQ_4_DECOMP = prove
 (`!l:byte list. LENGTH l = 4 ==> ?b0 b1 b2 b3. l = [b0; b1; b2; b3]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC 3`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC 2`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC 1`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let RESIDUE4_X_UPDATE = prove
 (`!(bs:byte list) n.
        LENGTH bs = n + 4
        ==> crc32c_hw_step
              (crc32c_hw_step
                (crc32c_hw_step
                  (crc32c_hw_step
                    (crc32c_bytes (word 0xFFFFFFFF:int32) (SUB_LIST(0, n) bs))
                    (word_subword
                      (word(num_of_bytelist
                              (SUB_LIST(n, 4) bs)):int32)
                      (0, 8):byte))
                  (word_subword
                    (word(num_of_bytelist
                            (SUB_LIST(n, 4) bs)):int32)
                    (8, 8):byte))
                (word_subword
                  (word(num_of_bytelist
                          (SUB_LIST(n, 4) bs)):int32)
                  (16, 8):byte))
              (word_subword
                (word(num_of_bytelist
                        (SUB_LIST(n, 4) bs)):int32)
                (24, 8):byte)
            = crc32c_bytes (word 0xFFFFFFFF:int32) bs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?b0 b1 b2 b3:byte.
        SUB_LIST (n, 4) (bs:byte list) = [b0; b1; b2; b3]`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_EQ_4_DECOMP THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTELIST4_BYTE0; WORD_SUBWORD_BYTELIST4_BYTE1;
              WORD_SUBWORD_BYTELIST4_BYTE2; WORD_SUBWORD_BYTELIST4_BYTE3] THEN
  REWRITE_TAC[CRC32CB_BRIDGE] THEN
  TRANS_TAC EQ_TRANS
   `crc32c_bytes (word 0xFFFFFFFF:int32)
      (APPEND (SUB_LIST(0,n) (bs:byte list)) [b0; b1; b2; b3])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[crc32c_bytes_APPEND; crc32c_bytes];
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`bs:byte list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE
      `LENGTH (bs:byte list) = n + 4 ==> LENGTH bs - n = 4`]]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE4_MEMORY_CLOSE: per-buffer memory zero-projection for residue=4.   *)
(* Composes the orthogonal-prefix lift (`bytelist (a, 16*iters) s = ZEROES`) *)
(* with the post-STR tail word (`bytes32 (a + 16*iters) s = word 0`)         *)
(* into the full-buffer zero-fill `bytelist (a, 16*iters + 4) s = ZEROES`.   *)
(* ------------------------------------------------------------------------- *)

let REPLICATE_ZERO_PLUS_FOUR = prove
 (`!k. REPLICATE (k + 4) (word 0:byte) =
       APPEND (REPLICATE k (word 0:byte))
              [word 0:byte; word 0:byte; word 0:byte; word 0:byte]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `k + 4 = (k + 3) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 3 = (k + 2) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 2 = (k + 1) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let RESIDUE4_MEMORY_CLOSE = prove
 (`!(a:int64) (s:armstate) k.
        read (memory :> bytelist (a, k)) s = REPLICATE k (word 0) /\
        read (memory :> bytes32 (word_add a (word k))) s = word 0
        ==> read (memory :> bytelist (a, k + 4)) s =
            REPLICATE (k + 4) (word 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_FOUR] THEN
  SUBGOAL_THEN
    `k + 4 = LENGTH (APPEND (REPLICATE k (word 0:byte))
                            [word 0:byte; word 0:byte;
                             word 0:byte; word 0:byte])`
  SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
  REWRITE_TAC[LENGTH_REPLICATE; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      ACCEPT_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE] th));
    ONCE_REWRITE_TAC[GSYM(SPEC_ALL READ_COMPONENT_COMPOSE)] THEN
    REWRITE_TAC[MEMORY_BYTELIST_4_EQ_BYTES32] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONS_11] THEN CONV_TAC WORD_BLAST]);;

(* ------------------------------------------------------------------------- *)
(* Residue=8 helpers (CRC32CX path).                                          *)
(* Templated from the residue=4 helpers above by widening to 8 bytes /        *)
(* int64. BYTES64_FROM_BYTELIST and CRC32CX_BRIDGE already exist (above).     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* MEMORY_BYTELIST_8_EQ_BYTES64: an 8-byte bytelist read equals the byte     *)
(* decomposition of a single bytes64 read. Used to bridge post-STR state     *)
(* (where bytes64 = word 0) back to the bytelist form.                       *)
(* ------------------------------------------------------------------------- *)

let MEMORY_BYTELIST_8_EQ_BYTES64 = prove
 (`!(a:int64) (s:armstate).
        read (memory :> bytelist (a, 8)) s =
        [word_subword (read (memory :> bytes64 a) s) (0,8):byte;
         word_subword (read (memory :> bytes64 a) s) (8,8):byte;
         word_subword (read (memory :> bytes64 a) s) (16,8):byte;
         word_subword (read (memory :> bytes64 a) s) (24,8):byte;
         word_subword (read (memory :> bytes64 a) s) (32,8):byte;
         word_subword (read (memory :> bytes64 a) s) (40,8):byte;
         word_subword (read (memory :> bytes64 a) s) (48,8):byte;
         word_subword (read (memory :> bytes64 a) s) (56,8):byte]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))`;
              bytelist_clauses;
              READ_COMPONENT_COMPOSE; bytes64;
              asword; through; read; CONS_11] THEN
  REWRITE_TAC[ARITH_RULE `SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))) = 8`;
              ARITH_RULE `SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))) = 7`;
              ARITH_RULE `SUC (SUC (SUC (SUC (SUC (SUC 0))))) = 6`;
              ARITH_RULE `SUC (SUC (SUC (SUC (SUC 0)))) = 5`;
              ARITH_RULE `SUC (SUC (SUC (SUC 0))) = 4`;
              ARITH_RULE `SUC (SUC (SUC 0)) = 3`;
              ARITH_RULE `SUC (SUC 0) = 2`;
              ARITH_RULE `SUC 0 = 1`] THEN
  REWRITE_TAC[ARITH_RULE `8 = 1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))`;
              ARITH_RULE `7 = 1 + (1 + (1 + (1 + (1 + (1 + 1)))))`;
              ARITH_RULE `6 = 1 + (1 + (1 + (1 + (1 + 1))))`;
              ARITH_RULE `5 = 1 + (1 + (1 + (1 + 1)))`;
              ARITH_RULE `4 = 1 + (1 + (1 + 1))`;
              ARITH_RULE `3 = 1 + (1 + 1)`;
              ARITH_RULE `2 = 1 + 1`;
              READ_BYTES_COMBINE; READ_BYTES_1] THEN
  REWRITE_TAC[
    WORD_RULE `word_add (word_add (a:int64) (word 1)) (word 1) =
               word_add a (word 2)`;
    WORD_RULE `word_add (word_add (word_add (a:int64) (word 1)) (word 1))
                        (word 1) = word_add a (word 3)`;
    WORD_RULE `word_add (word_add (word_add (word_add (a:int64) (word 1))
                          (word 1)) (word 1)) (word 1) = word_add a (word 4)`;
    WORD_RULE `word_add (word_add (word_add (word_add (word_add (a:int64)
                          (word 1)) (word 1)) (word 1)) (word 1)) (word 1) =
               word_add a (word 5)`;
    WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (a:int64)
                          (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) =
               word_add a (word 6)`;
    WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (word_add
                          (a:int64) (word 1)) (word 1)) (word 1)) (word 1)) (word 1))
                          (word 1)) (word 1) = word_add a (word 7)`] THEN
  ABBREV_TAC `b0:byte = read memory s (a:int64)` THEN
  ABBREV_TAC `b1:byte = read memory s (word_add (a:int64) (word 1))` THEN
  ABBREV_TAC `b2:byte = read memory s (word_add (a:int64) (word 2))` THEN
  ABBREV_TAC `b3:byte = read memory s (word_add (a:int64) (word 3))` THEN
  ABBREV_TAC `b4:byte = read memory s (word_add (a:int64) (word 4))` THEN
  ABBREV_TAC `b5:byte = read memory s (word_add (a:int64) (word 5))` THEN
  ABBREV_TAC `b6:byte = read memory s (word_add (a:int64) (word 6))` THEN
  ABBREV_TAC `b7:byte = read memory s (word_add (a:int64) (word 7))` THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_1] THEN
  REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THENL
   [(* byte 0: ... MOD 256 = b0 *)
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    (* byte 1 *)
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 2 *)
    SUBGOAL_THEN `(65536:num) = 256 * 256` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 3 *)
    SUBGOAL_THEN `(16777216:num) = 256 * (256 * 256)` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 4 *)
    SUBGOAL_THEN `(4294967296:num) = 256 * (256 * (256 * 256))` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 5 *)
    SUBGOAL_THEN `(1099511627776:num) = 256 * (256 * (256 * (256 * 256)))` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 6 *)
    SUBGOAL_THEN `(281474976710656:num) = 256 * (256 * (256 * (256 * (256 * 256))))` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT];
    (* byte 7 *)
    SUBGOAL_THEN `(72057594037927936:num) = 256 * (256 * (256 * (256 * (256 * (256 * 256)))))` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
                 ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* SUFFIX_BYTELIST_TO_BYTES64: residue=8 per-buffer adapter (k+8, width 8).  *)
(* ------------------------------------------------------------------------- *)

let SUFFIX_BYTELIST_TO_BYTES64 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 8 /\
        read (memory :> bytelist (word_add a (word k), 8)) s =
          SUB_LIST (k, 8) bs
        ==> read (memory :> bytes64 (word_add a (word k))) s =
            word(num_of_bytelist (SUB_LIST(k, 8) bs))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add a (word k):int64`; `s:armstate`;
                 `SUB_LIST(k, 8) (bs:byte list)`; `0:num`]
                BYTES64_FROM_BYTELIST) THEN
  SUBGOAL_THEN `LENGTH (SUB_LIST (k,8) (bs:byte list)) = 8` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 8) (SUB_LIST(k, 8) (bs:byte list)) =
     SUB_LIST(k, 8) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Eight byte-extraction lemmas:                                              *)
(*   word_subword (word(num_of_bytelist [b0..b7]):int64) (k*8, 8) = bk        *)
(* for k=0..7. Used inside RESIDUE8_X_UPDATE to push the loaded int64        *)
(* through the eight CRC32CX byte-step calls.                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_BYTELIST8_BYTE0 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (0, 8):byte = b0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_1] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST8_BYTE1 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (8, 8):byte = b1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST8_BYTE2 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (16, 8):byte = b2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(65536:num) = 256 * 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST8_BYTE3 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (24, 8):byte = b3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(16777216:num) = 256 * (256 * 256)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST8_BYTE4 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (32, 8):byte = b4`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(4294967296:num) = 256 * (256 * (256 * 256))` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST8_BYTE5 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (40, 8):byte = b5`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(1099511627776:num) = 256 * (256 * (256 * (256 * 256)))` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST8_BYTE6 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (48, 8):byte = b6`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(281474976710656:num) = 256 * (256 * (256 * (256 * (256 * 256))))` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

let WORD_SUBWORD_BYTELIST8_BYTE7 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
       word_subword
        (word(num_of_bytelist [b0; b1; b2; b3; b4; b5; b6; b7]):int64) (56, 8):byte = b7`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_bytelist; MULT_0; ADD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b4:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b5:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b6:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b7:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(val (b0:byte) +
      256 * (val (b1:byte) +
       256 * (val (b2:byte) +
        256 * (val (b3:byte) +
         256 * (val (b4:byte) +
          256 * (val (b5:byte) +
           256 * (val (b6:byte) + 256 * val (b7:byte)))))))) MOD 18446744073709551616 =
     val b0 + 256 * (val b1 + 256 * (val b2 + 256 * (val b3 +
      256 * (val b4 + 256 * (val b5 + 256 * (val b6 + 256 * val b7))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(72057594037927936:num) = 256 * (256 * (256 * (256 * (256 * (256 * 256)))))` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; DIV_LT;
               ADD_CLAUSES; MOD_MULT_ADD; MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* LENGTH_EQ_8_DECOMP: a byte list of length 8 decomposes into 8 elements.   *)
(* ------------------------------------------------------------------------- *)

let LENGTH_EQ_8_DECOMP = prove
 (`!l:byte list. LENGTH l = 8
                 ==> ?b0 b1 b2 b3 b4 b5 b6 b7. l = [b0; b1; b2; b3; b4; b5; b6; b7]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 = SUC 7`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `7 = SUC 6`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `6 = SUC 5`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `5 = SUC 4`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC 3`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC 2`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC 1`; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE8_X_UPDATE: per-buffer X-register update fact for residue=8 case.  *)
(* Given a buffer `bs` of length n+8, the CRC32CX chain output on            *)
(* `acc = crc32c_bytes 0xFFFFFFFF (SUB_LIST(0,n) bs)` consuming the 8-byte   *)
(* int64 loaded from `bytes64 (a + n)` (which equals the bytes at positions  *)
(* n..n+7 of bs by SUFFIX_BYTELIST_TO_BYTES64) collapses to                  *)
(* `crc32c_bytes 0xFFFFFFFF bs` --- the full-buffer CRC.                     *)
(*                                                                           *)
(* Like residue=4, the kernel's X-register data path passes the loaded       *)
(* int64 directly into CRC32CX (no word_zx); the 8 word_subword extractions *)
(* (k*8, 8) of `word(num_of_bytelist (SUB_LIST(n,8) bs)):int64` are the      *)
(* eight bytes of bs at positions n..n+7 (LSB-first).                        *)
(* ------------------------------------------------------------------------- *)

let RESIDUE8_X_UPDATE = prove
 (`!(bs:byte list) n.
        LENGTH bs = n + 8
        ==> crc32c_hw_step
              (crc32c_hw_step
                (crc32c_hw_step
                  (crc32c_hw_step
                    (crc32c_hw_step
                      (crc32c_hw_step
                        (crc32c_hw_step
                          (crc32c_hw_step
                            (crc32c_bytes (word 0xFFFFFFFF:int32) (SUB_LIST(0, n) bs))
                            (word_subword
                              (word(num_of_bytelist
                                      (SUB_LIST(n, 8) bs)):int64)
                              (0, 8):byte))
                          (word_subword
                            (word(num_of_bytelist
                                    (SUB_LIST(n, 8) bs)):int64)
                            (8, 8):byte))
                        (word_subword
                          (word(num_of_bytelist
                                  (SUB_LIST(n, 8) bs)):int64)
                          (16, 8):byte))
                      (word_subword
                        (word(num_of_bytelist
                                (SUB_LIST(n, 8) bs)):int64)
                        (24, 8):byte))
                    (word_subword
                      (word(num_of_bytelist
                              (SUB_LIST(n, 8) bs)):int64)
                      (32, 8):byte))
                  (word_subword
                    (word(num_of_bytelist
                            (SUB_LIST(n, 8) bs)):int64)
                    (40, 8):byte))
                (word_subword
                  (word(num_of_bytelist
                          (SUB_LIST(n, 8) bs)):int64)
                  (48, 8):byte))
              (word_subword
                (word(num_of_bytelist
                        (SUB_LIST(n, 8) bs)):int64)
                (56, 8):byte)
            = crc32c_bytes (word 0xFFFFFFFF:int32) bs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?b0 b1 b2 b3 b4 b5 b6 b7:byte.
        SUB_LIST (n, 8) (bs:byte list) = [b0; b1; b2; b3; b4; b5; b6; b7]`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_EQ_8_DECOMP THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTELIST8_BYTE0; WORD_SUBWORD_BYTELIST8_BYTE1;
              WORD_SUBWORD_BYTELIST8_BYTE2; WORD_SUBWORD_BYTELIST8_BYTE3;
              WORD_SUBWORD_BYTELIST8_BYTE4; WORD_SUBWORD_BYTELIST8_BYTE5;
              WORD_SUBWORD_BYTELIST8_BYTE6; WORD_SUBWORD_BYTELIST8_BYTE7] THEN
  REWRITE_TAC[CRC32CB_BRIDGE] THEN
  TRANS_TAC EQ_TRANS
   `crc32c_bytes (word 0xFFFFFFFF:int32)
      (APPEND (SUB_LIST(0,n) (bs:byte list))
              [b0; b1; b2; b3; b4; b5; b6; b7])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[crc32c_bytes_APPEND; crc32c_bytes];
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`bs:byte list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE
      `LENGTH (bs:byte list) = n + 8 ==> LENGTH bs - n = 8`]]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE8_MEMORY_CLOSE: per-buffer memory zero-projection for residue=8.   *)
(* Composes the orthogonal-prefix lift (`bytelist (a, k) s = ZEROES`) with    *)
(* the post-STR tail int64 (`bytes64 (a + k) s = word 0`) into the           *)
(* full-buffer zero-fill `bytelist (a, k + 8) s = ZEROES`.                   *)
(* ------------------------------------------------------------------------- *)

let REPLICATE_ZERO_PLUS_EIGHT = prove
 (`!k. REPLICATE (k + 8) (word 0:byte) =
       APPEND (REPLICATE k (word 0:byte))
              [word 0:byte; word 0:byte; word 0:byte; word 0:byte;
               word 0:byte; word 0:byte; word 0:byte; word 0:byte]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `k + 8 = (k + 7) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 7 = (k + 6) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 6 = (k + 5) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 5 = (k + 4) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 4 = (k + 3) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 3 = (k + 2) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[ARITH_RULE `k + 2 = (k + 1) + 1`] THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_ONE] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let RESIDUE8_MEMORY_CLOSE = prove
 (`!(a:int64) (s:armstate) k.
        read (memory :> bytelist (a, k)) s = REPLICATE k (word 0) /\
        read (memory :> bytes64 (word_add a (word k))) s = word 0
        ==> read (memory :> bytelist (a, k + 8)) s =
            REPLICATE (k + 8) (word 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REPLICATE_ZERO_PLUS_EIGHT] THEN
  SUBGOAL_THEN
    `k + 8 = LENGTH (APPEND (REPLICATE k (word 0:byte))
                            [word 0:byte; word 0:byte;
                             word 0:byte; word 0:byte;
                             word 0:byte; word 0:byte;
                             word 0:byte; word 0:byte])`
  SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
  REWRITE_TAC[LENGTH_REPLICATE; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      ACCEPT_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE] th));
    ONCE_REWRITE_TAC[GSYM(SPEC_ALL READ_COMPONENT_COMPOSE)] THEN
    REWRITE_TAC[MEMORY_BYTELIST_8_EQ_BYTES64] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONS_11] THEN CONV_TAC WORD_BLAST]);;

(* ------------------------------------------------------------------------- *)
(* Residue=12 helpers (8-byte CRC32CX path then 4-byte CRC32CW path).         *)
(* Composed from RESIDUE8_X_UPDATE and RESIDUE4_X_UPDATE via                   *)
(* crc32c_bytes_APPEND, splitting the 12-byte tail of bs into [n,n+8) and     *)
(* [n+8,n+12).                                                                *)
(* ------------------------------------------------------------------------- *)

let RESIDUE12_X_UPDATE = prove
 (`!(bs:byte list) n.
        LENGTH bs = n + 12
        ==> crc32c_hw_step
              (crc32c_hw_step
                (crc32c_hw_step
                  (crc32c_hw_step
                    (crc32c_hw_step
                      (crc32c_hw_step
                        (crc32c_hw_step
                          (crc32c_hw_step
                            (crc32c_hw_step
                              (crc32c_hw_step
                                (crc32c_hw_step
                                  (crc32c_hw_step
                                    (crc32c_bytes (word 0xFFFFFFFF:int32)
                                                  (SUB_LIST(0, n) bs))
                                    (word_subword
                                      (word(num_of_bytelist
                                              (SUB_LIST(n, 8) bs)):int64)
                                      (0, 8):byte))
                                  (word_subword
                                    (word(num_of_bytelist
                                            (SUB_LIST(n, 8) bs)):int64)
                                    (8, 8):byte))
                                (word_subword
                                  (word(num_of_bytelist
                                          (SUB_LIST(n, 8) bs)):int64)
                                  (16, 8):byte))
                              (word_subword
                                (word(num_of_bytelist
                                        (SUB_LIST(n, 8) bs)):int64)
                                (24, 8):byte))
                            (word_subword
                              (word(num_of_bytelist
                                      (SUB_LIST(n, 8) bs)):int64)
                              (32, 8):byte))
                          (word_subword
                            (word(num_of_bytelist
                                    (SUB_LIST(n, 8) bs)):int64)
                            (40, 8):byte))
                        (word_subword
                          (word(num_of_bytelist
                                  (SUB_LIST(n, 8) bs)):int64)
                          (48, 8):byte))
                      (word_subword
                        (word(num_of_bytelist
                                (SUB_LIST(n, 8) bs)):int64)
                        (56, 8):byte))
                    (word_subword
                      (word(num_of_bytelist
                              (SUB_LIST(n + 8, 4) bs)):int32)
                      (0, 8):byte))
                  (word_subword
                    (word(num_of_bytelist
                            (SUB_LIST(n + 8, 4) bs)):int32)
                    (8, 8):byte))
                (word_subword
                  (word(num_of_bytelist
                          (SUB_LIST(n + 8, 4) bs)):int32)
                  (16, 8):byte))
              (word_subword
                (word(num_of_bytelist
                        (SUB_LIST(n + 8, 4) bs)):int32)
                (24, 8):byte)
            = crc32c_bytes (word 0xFFFFFFFF:int32) bs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?b0 b1 b2 b3 b4 b5 b6 b7:byte.
        SUB_LIST (n, 8) (bs:byte list) = [b0; b1; b2; b3; b4; b5; b6; b7]`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_EQ_8_DECOMP THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `?c0 c1 c2 c3:byte.
        SUB_LIST (n + 8, 4) (bs:byte list) = [c0; c1; c2; c3]`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_EQ_4_DECOMP THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTELIST8_BYTE0; WORD_SUBWORD_BYTELIST8_BYTE1;
              WORD_SUBWORD_BYTELIST8_BYTE2; WORD_SUBWORD_BYTELIST8_BYTE3;
              WORD_SUBWORD_BYTELIST8_BYTE4; WORD_SUBWORD_BYTELIST8_BYTE5;
              WORD_SUBWORD_BYTELIST8_BYTE6; WORD_SUBWORD_BYTELIST8_BYTE7] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTELIST4_BYTE0; WORD_SUBWORD_BYTELIST4_BYTE1;
              WORD_SUBWORD_BYTELIST4_BYTE2; WORD_SUBWORD_BYTELIST4_BYTE3] THEN
  REWRITE_TAC[CRC32CB_BRIDGE] THEN
  TRANS_TAC EQ_TRANS
   `crc32c_bytes (word 0xFFFFFFFF:int32)
      (APPEND
        (APPEND (SUB_LIST(0,n) (bs:byte list))
                [b0; b1; b2; b3; b4; b5; b6; b7])
        [c0; c1; c2; c3])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[crc32c_bytes_APPEND; crc32c_bytes];
    AP_TERM_TAC THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    SUBGOAL_THEN
      `APPEND [b0; b1; b2; b3; b4; b5; b6; b7] [c0; c1; c2; c3] =
       SUB_LIST(n, 12) (bs:byte list)`
    SUBST1_TAC THENL
     [POP_ASSUM(SUBST1_TAC o SYM) THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`bs:byte list`; `8:num`; `4:num`; `n:num`]
                    SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ARITH_RULE `8 + 4 = 12`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bs:byte list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE
      `LENGTH (bs:byte list) = n + 12 ==> LENGTH bs - n = 12`]]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE12_MEMORY_CLOSE: per-buffer memory zero-projection for residue=12. *)
(* Composes the orthogonal-prefix lift `bytelist (a, k) s = ZEROES`           *)
(* with the post-STR int64 zero `bytes64 (a + k) s = word 0`                  *)
(* and the post-STR int32 zero `bytes32 (a + k + 8) s = word 0`               *)
(* into the full-buffer zero-fill `bytelist (a, k + 12) s = ZEROES`.          *)
(* ------------------------------------------------------------------------- *)

let RESIDUE12_MEMORY_CLOSE = prove
 (`!(a:int64) (s:armstate) k.
        read (memory :> bytelist (a, k)) s = REPLICATE k (word 0) /\
        read (memory :> bytes64 (word_add a (word k))) s = word 0 /\
        read (memory :> bytes32 (word_add a (word (k + 8)))) s = word 0
        ==> read (memory :> bytelist (a, k + 12)) s =
            REPLICATE (k + 12) (word 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k + 12 = (k + 8) + 4` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RESIDUE4_MEMORY_CLOSE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RESIDUE8_MEMORY_CLOSE THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Residue=12 per-buffer cut-state adapters.                                  *)
(* The cut state on entry to the residue=12 case has a 12-byte suffix         *)
(* bytelist hypothesis                                                       *)
(*    read (memory :> bytelist (word_add a (word k), 12)) s =                 *)
(*      SUB_LIST(k, 12) bs                                                    *)
(* (with LENGTH bs = k + 12). The kernel's tail-block performs both an LDR X  *)
(* (8 bytes at offset k) and an LDR W (4 bytes at offset k+8); we stage the   *)
(* corresponding bytes64 / bytes32 reads at s0 so ARM_STEPS_TAC can resolve   *)
(* both. They are pre-store reads at s0 — the post-imm STR XZR writes at      *)
(* a + k overlap only the 8-byte half, leaving the 4-byte half of the         *)
(* bytelist intact at a + (k + 8) for the subsequent LDR W.                   *)
(* ------------------------------------------------------------------------- *)

let RESIDUE12_BYTELIST_TO_BYTES64 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 12 /\
        read (memory :> bytelist (word_add a (word k), 12)) s =
          SUB_LIST (k, 12) bs
        ==> read (memory :> bytes64 (word_add a (word k))) s =
            word(num_of_bytelist (SUB_LIST(k, 8) bs))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `read (memory :> bytelist (word_add a (word k), 8)) (s:armstate) =
     SUB_LIST (k, 8) (bs:byte list)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
      `SUB_LIST(k, 12) (bs:byte list) =
       APPEND (SUB_LIST(k, 8) bs) (SUB_LIST(k + 8, 4) bs)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`bs:byte list`; `8:num`; `4:num`; `k:num`]
                    SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ARITH_RULE `8 + 4 = 12`];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `LENGTH (SUB_LIST(k, 8) (bs:byte list)) = 8 /\
       LENGTH (SUB_LIST(k + 8, 4) (bs:byte list)) = 4`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `read (memory :> bytelist (word_add a (word k), 12)) s =
                 SUB_LIST (k, 12) (bs:byte list)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `12 = LENGTH (APPEND (SUB_LIST(k, 8) (bs:byte list))
                           (SUB_LIST(k + 8, 4) bs))`
    SUBST1_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word k):int64`; `s:armstate`;
                 `SUB_LIST(k, 8) (bs:byte list)`; `0:num`]
                BYTES64_FROM_BYTELIST) THEN
  SUBGOAL_THEN `LENGTH (SUB_LIST (k,8) (bs:byte list)) = 8` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH; LE_REFL] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 8) (SUB_LIST(k, 8) (bs:byte list)) =
     SUB_LIST(k, 8) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;

let RESIDUE12_BYTELIST_TO_BYTES32 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 12 /\
        read (memory :> bytelist (word_add a (word k), 12)) s =
          SUB_LIST (k, 12) bs
        ==> read (memory :> bytes32 (word_add a (word (k + 8)))) s =
            word(num_of_bytelist (SUB_LIST(k + 8, 4) bs))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `LENGTH (SUB_LIST(k, 8) (bs:byte list)) = 8 /\
     LENGTH (SUB_LIST(k + 8, 4) (bs:byte list)) = 4`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `read (memory :> bytelist
       (word_add a (word (k + 8)), 4)) (s:armstate) =
     SUB_LIST (k + 8, 4) (bs:byte list)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
      `read (memory :> bytelist (word_add a (word k), 12)) (s:armstate) =
       APPEND (SUB_LIST(k, 8) (bs:byte list)) (SUB_LIST(k + 8, 4) bs)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`bs:byte list`; `8:num`; `4:num`; `k:num`]
                    SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ARITH_RULE `8 + 4 = 12`];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `12 = LENGTH (APPEND (SUB_LIST(k, 8) (bs:byte list))
                           (SUB_LIST(k + 8, 4) bs))`
    SUBST1_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `word_add (word_add (a:int64) (word k)) (word 8) =
       word_add a (word (k + 8))`
    SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word (k + 8)):int64`; `s:armstate`;
                 `SUB_LIST(k + 8, 4) (bs:byte list)`; `0:num`]
                BYTES32_FROM_BYTELIST) THEN
  ASM_REWRITE_TAC[ARITH; LE_REFL] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 4) (SUB_LIST(k + 8, 4) (bs:byte list)) =
     SUB_LIST(k + 8, 4) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Residue=10 helpers (8-byte CRC32CX path then 2-byte CRC32CH path).         *)
(* Composed from RESIDUE8_X_UPDATE and RESIDUE2_X_UPDATE via                   *)
(* crc32c_bytes_APPEND, splitting the 10-byte tail of bs into [n,n+8) and     *)
(* [n+8,n+10).                                                                *)
(* ------------------------------------------------------------------------- *)

let RESIDUE10_X_UPDATE = prove
 (`!(bs:byte list) n.
        LENGTH bs = n + 10
        ==> crc32c_hw_step
              (crc32c_hw_step
                (crc32c_hw_step
                  (crc32c_hw_step
                    (crc32c_hw_step
                      (crc32c_hw_step
                        (crc32c_hw_step
                          (crc32c_hw_step
                            (crc32c_hw_step
                              (crc32c_hw_step
                                (crc32c_bytes (word 0xFFFFFFFF:int32)
                                              (SUB_LIST(0, n) bs))
                                (word_subword
                                  (word(num_of_bytelist
                                          (SUB_LIST(n, 8) bs)):int64)
                                  (0, 8):byte))
                              (word_subword
                                (word(num_of_bytelist
                                        (SUB_LIST(n, 8) bs)):int64)
                                (8, 8):byte))
                            (word_subword
                              (word(num_of_bytelist
                                      (SUB_LIST(n, 8) bs)):int64)
                              (16, 8):byte))
                          (word_subword
                            (word(num_of_bytelist
                                    (SUB_LIST(n, 8) bs)):int64)
                            (24, 8):byte))
                        (word_subword
                          (word(num_of_bytelist
                                  (SUB_LIST(n, 8) bs)):int64)
                          (32, 8):byte))
                      (word_subword
                        (word(num_of_bytelist
                                (SUB_LIST(n, 8) bs)):int64)
                        (40, 8):byte))
                    (word_subword
                      (word(num_of_bytelist
                              (SUB_LIST(n, 8) bs)):int64)
                      (48, 8):byte))
                  (word_subword
                    (word(num_of_bytelist
                            (SUB_LIST(n, 8) bs)):int64)
                    (56, 8):byte))
                (word_subword
                  (word_zx
                    (word(num_of_bytelist
                            (SUB_LIST(n + 8, 2) bs)):int16):int32)
                  (0, 8):byte))
              (word_subword
                (word_zx
                  (word(num_of_bytelist
                          (SUB_LIST(n + 8, 2) bs)):int16):int32)
                (8, 8):byte)
            = crc32c_bytes (word 0xFFFFFFFF:int32) bs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_SUBWORD_ZX_INT16_BYTE0; WORD_SUBWORD_ZX_INT16_BYTE1] THEN
  SUBGOAL_THEN
    `?b0 b1 b2 b3 b4 b5 b6 b7:byte.
        SUB_LIST (n, 8) (bs:byte list) = [b0; b1; b2; b3; b4; b5; b6; b7]`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_EQ_8_DECOMP THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `?c0 c1:byte.
        SUB_LIST (n + 8, 2) (bs:byte list) = [c0; c1]`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_EQ_2_DECOMP THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTELIST8_BYTE0; WORD_SUBWORD_BYTELIST8_BYTE1;
              WORD_SUBWORD_BYTELIST8_BYTE2; WORD_SUBWORD_BYTELIST8_BYTE3;
              WORD_SUBWORD_BYTELIST8_BYTE4; WORD_SUBWORD_BYTELIST8_BYTE5;
              WORD_SUBWORD_BYTELIST8_BYTE6; WORD_SUBWORD_BYTELIST8_BYTE7] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTELIST2_LSB; WORD_SUBWORD_BYTELIST2_MSB] THEN
  REWRITE_TAC[CRC32CB_BRIDGE] THEN
  TRANS_TAC EQ_TRANS
   `crc32c_bytes (word 0xFFFFFFFF:int32)
      (APPEND
        (APPEND (SUB_LIST(0,n) (bs:byte list))
                [b0; b1; b2; b3; b4; b5; b6; b7])
        [c0; c1])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[crc32c_bytes_APPEND; crc32c_bytes];
    AP_TERM_TAC THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    SUBGOAL_THEN
      `APPEND [b0; b1; b2; b3; b4; b5; b6; b7] [c0; c1] =
       SUB_LIST(n, 10) (bs:byte list)`
    SUBST1_TAC THENL
     [POP_ASSUM(SUBST1_TAC o SYM) THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`bs:byte list`; `8:num`; `2:num`; `n:num`]
                    SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ARITH_RULE `8 + 2 = 10`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bs:byte list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE
      `LENGTH (bs:byte list) = n + 10 ==> LENGTH bs - n = 10`]]);;

(* ------------------------------------------------------------------------- *)
(* RESIDUE10_MEMORY_CLOSE: per-buffer memory zero-projection for residue=10. *)
(* Composes the orthogonal-prefix lift `bytelist (a, k) s = ZEROES`           *)
(* with the post-STR int64 zero `bytes64 (a + k) s = word 0`                  *)
(* and the post-STRH int16 zero `bytes16 (a + (k + 8)) s = word 0`            *)
(* into the full-buffer zero-fill `bytelist (a, k + 10) s = ZEROES`.          *)
(* ------------------------------------------------------------------------- *)

let RESIDUE10_MEMORY_CLOSE = prove
 (`!(a:int64) (s:armstate) k.
        read (memory :> bytelist (a, k)) s = REPLICATE k (word 0) /\
        read (memory :> bytes64 (word_add a (word k))) s = word 0 /\
        read (memory :> bytes16 (word_add a (word (k + 8)))) s = word 0
        ==> read (memory :> bytelist (a, k + 10)) s =
            REPLICATE (k + 10) (word 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k + 10 = (k + 8) + 2` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RESIDUE2_MEMORY_CLOSE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RESIDUE8_MEMORY_CLOSE THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Residue=10 per-buffer cut-state adapters.                                  *)
(* The cut state on entry to the residue=10 case has a 10-byte suffix         *)
(* bytelist hypothesis                                                       *)
(*    read (memory :> bytelist (word_add a (word k), 10)) s =                 *)
(*      SUB_LIST(k, 10) bs                                                    *)
(* (with LENGTH bs = k + 10). The kernel's tail-block performs both an LDR X  *)
(* (8 bytes at offset k) and an LDRH (2 bytes at offset k+8); we stage the    *)
(* corresponding bytes64 / bytes16 reads at s0 so ARM_STEPS_TAC can resolve   *)
(* both. They are pre-store reads at s0 — the post-imm STR XZR writes at      *)
(* a + k overlap only the 8-byte half, leaving the 2-byte half of the         *)
(* bytelist intact at a + (k + 8) for the subsequent LDRH.                    *)
(* ------------------------------------------------------------------------- *)

let RESIDUE10_BYTELIST_TO_BYTES64 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 10 /\
        read (memory :> bytelist (word_add a (word k), 10)) s =
          SUB_LIST (k, 10) bs
        ==> read (memory :> bytes64 (word_add a (word k))) s =
            word(num_of_bytelist (SUB_LIST(k, 8) bs))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `read (memory :> bytelist (word_add a (word k), 8)) (s:armstate) =
     SUB_LIST (k, 8) (bs:byte list)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
      `SUB_LIST(k, 10) (bs:byte list) =
       APPEND (SUB_LIST(k, 8) bs) (SUB_LIST(k + 8, 2) bs)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`bs:byte list`; `8:num`; `2:num`; `k:num`]
                    SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ARITH_RULE `8 + 2 = 10`];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `LENGTH (SUB_LIST(k, 8) (bs:byte list)) = 8 /\
       LENGTH (SUB_LIST(k + 8, 2) (bs:byte list)) = 2`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `read (memory :> bytelist (word_add a (word k), 10)) s =
                 SUB_LIST (k, 10) (bs:byte list)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `10 = LENGTH (APPEND (SUB_LIST(k, 8) (bs:byte list))
                           (SUB_LIST(k + 8, 2) bs))`
    SUBST1_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word k):int64`; `s:armstate`;
                 `SUB_LIST(k, 8) (bs:byte list)`; `0:num`]
                BYTES64_FROM_BYTELIST) THEN
  SUBGOAL_THEN `LENGTH (SUB_LIST (k,8) (bs:byte list)) = 8` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH; LE_REFL] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 8) (SUB_LIST(k, 8) (bs:byte list)) =
     SUB_LIST(k, 8) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;

let RESIDUE10_BYTELIST_TO_BYTES16 = prove
 (`!(a:int64) (s:armstate) (bs:byte list) k.
        LENGTH bs = k + 10 /\
        read (memory :> bytelist (word_add a (word k), 10)) s =
          SUB_LIST (k, 10) bs
        ==> read (memory :> bytes16 (word_add a (word (k + 8)))) s =
            word(num_of_bytelist (SUB_LIST(k + 8, 2) bs))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `LENGTH (SUB_LIST(k, 8) (bs:byte list)) = 8 /\
     LENGTH (SUB_LIST(k + 8, 2) (bs:byte list)) = 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `read (memory :> bytelist
       (word_add a (word (k + 8)), 2)) (s:armstate) =
     SUB_LIST (k + 8, 2) (bs:byte list)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
      `read (memory :> bytelist (word_add a (word k), 10)) (s:armstate) =
       APPEND (SUB_LIST(k, 8) (bs:byte list)) (SUB_LIST(k + 8, 2) bs)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`bs:byte list`; `8:num`; `2:num`; `k:num`]
                    SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ARITH_RULE `8 + 2 = 10`];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `10 = LENGTH (APPEND (SUB_LIST(k, 8) (bs:byte list))
                           (SUB_LIST(k + 8, 2) bs))`
    SUBST1_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; read_bytelist_append] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `word_add (word_add (a:int64) (word k)) (word 8) =
       word_add a (word (k + 8))`
    SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word (k + 8)):int64`; `s:armstate`;
                 `SUB_LIST(k + 8, 2) (bs:byte list)`; `0:num`]
                BYTES16_FROM_BYTELIST) THEN
  ASM_REWRITE_TAC[ARITH; LE_REFL] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 2) (SUB_LIST(k + 8, 2) (bs:byte list)) =
     SUB_LIST(k + 8, 2) bs`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[SUB_LIST_LENGTH];
    DISCH_THEN ACCEPT_TAC]);;
