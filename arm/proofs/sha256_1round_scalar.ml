(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 single round using scalar instructions.                          *)
(* Validates that ROR/EOR/AND/BIC/ADD correctly compute one compression     *)
(* round against sha256_compress_round from sha256_spec.ml.                 *)
(* ========================================================================= *)

needs "arm/proofs/utils/sha256_spec.ml";;

(* Machine code *)

let sha256_1round_scalar_mc = define_from_elf "sha256_1round_scalar_mc"
  (file_on_path !load_path "arm/sha2/sha256_1round_scalar.o");;

let SCALAR1_EXEC = ARM_MK_EXEC_RULE sha256_1round_scalar_mc;;

(* Injectivity of word_zx : int32 -> int64 *)

let WORD_ZX_INJ_32_64 = prove
 (`!(x:int32) (y:int32). ((word_zx:int32->int64) x = word_zx y) <=> (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `word_zx:int64->int32`) THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH];
    ASM_REWRITE_TAC[]]);;

(* Correctness theorem *)

let SHA256_1ROUND_SCALAR_CORRECT = prove
 (`!a b c d e f g h k_t w_t pc.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) sha256_1round_scalar_mc /\
           read PC s = word pc /\
           read X0 s = word_zx (k_t:int32) /\
           read X1 s = word_zx (w_t:int32) /\
           read X4 s = word_zx (a:int32) /\
           read X5 s = word_zx (b:int32) /\
           read X6 s = word_zx (c:int32) /\
           read X7 s = word_zx (d:int32) /\
           read X8 s = word_zx (e:int32) /\
           read X9 s = word_zx (f:int32) /\
           read X10 s = word_zx (g:int32) /\
           read X11 s = word_zx (h:int32))
      (\s. read PC s = word(pc + 0x7c) /\
           read X4 s = word_zx (EL 0 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])) /\
           read X5 s = word_zx (EL 1 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])) /\
           read X6 s = word_zx (EL 2 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])) /\
           read X7 s = word_zx (EL 3 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])) /\
           read X8 s = word_zx (EL 4 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])) /\
           read X9 s = word_zx (EL 5 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])) /\
           read X10 s = word_zx (EL 6 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])) /\
           read X11 s = word_zx (EL 7 (sha256_compress_round k_t w_t [a;b;c;d;e;f;g;h])))
      (MAYCHANGE [PC; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15] ,,
       MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])`,
  let BIC_NORM = WORD_RULE
    `word_and (x:(N)word) (word_not y) = word_and (word_not y) x` in
  REWRITE_TAC[sha256_compress_round; sha256_Sigma0; sha256_Sigma1;
              sha256_Ch; sha256_Maj; EL; HD; TL; LET_DEF; LET_END_DEF] THEN
  SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[DIMINDEX_32; EL; HD; TL; ARITH] THEN
  REWRITE_TAC[fst SCALAR1_EXEC; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC SCALAR1_EXEC (1--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_TRIVIAL]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_TRIVIAL]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_TRIVIAL]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_INJ_32_64] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
           WORD_ZX_TRIVIAL] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[BIC_NORM] THEN
  REFL_TAC);;
