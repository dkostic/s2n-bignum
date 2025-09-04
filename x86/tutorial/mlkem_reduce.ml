(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Proving a simple property about program 'simple.S'
******************************************************************************)

(* Please copy this file to the root directory of s2n-bignum, then
   follow the instructions. *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

print_literal_from_elf "x86/tutorial/mlkem_reduce.o";;

(* Or, you can read .o file and store the byte list as follows:
*)
let simple_mc1 = define_assert_from_elf "simple_mc1" "x86/tutorial/mlkem_reduce.o"
[
  0xc5; 0xfd; 0x6f; 0x17;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0x6d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0xed; 0xf9; 0xd0;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0xfd; 0x7f; 0x17   (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
];;

let MLKEM_POLY_REDUCE_EXEC = X86_MK_EXEC_RULE simple_mc1;;

(* Enable simplification of word_subwords by default.
   Nedded to prevent the symbolic simulation to explode
   as we add more instructions. *)
let org_extra_word_conv = !extra_word_CONV;;
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ !extra_word_CONV;;

let lemma_rem = prove
 (`(y == x) (mod &3329) /\
   &0 <= y /\ y < &6658
   ==> x rem &3329 = if y >= &3329 then y - &3329 else y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
  SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE);;

let overall_lemma = prove
 (`!x:int16.
        ival(word_add (word_sub (barred_x86 x) (word 3329))
                      (word_and (word_ishr (word_sub (barred_x86 x) (word 3329)) 15)
                                (word 3329))) =
        ival x rem &3329`,
  REWRITE_TAC[MATCH_MP lemma_rem (CONGBOUND_RULE `barred_x86 x`)] THEN
  GEN_TAC THEN MP_TAC(CONGBOUND_RULE `barred_x86 x`) THEN
  BITBLAST_TAC);;

let overall_lemma2 = SPEC_ALL overall_lemma;;
let overall_lemma3 = AP_TERM `iword:int -> (16)word` overall_lemma2 ;;
let overall_lemma4 = REWRITE_RULE[IWORD_IVAL] overall_lemma3;;

let SIMD_SIMPLIFY_TAC_LOCAL unfold_defs = RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV unfold_defs));;

let helper_lemma = prove
 (`!x:int16. ival(iword(ival x rem &3329):int16) = ival x rem &3329`,
  GEN_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN INT_ARITH_TAC);;

let MLKEM_REDUCE_CORRECT = prove(
  `forall pc a b.
  nonoverlapping (word pc, LENGTH simple_mc1) (a, 32) /\
  aligned 32 a ==>
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) simple_mc1 /\
         read RIP s = word pc /\
         read YMM0 s = word 0x0d010d010d010d010d010d010d010d010d010d010d010d010d010d010d010d01 /\
         read YMM1 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
         C_ARGUMENTS [a] s /\
         !i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i)
    // Postcondition
    (\s. read RIP s = word (pc+45) /\
         !i. i < 256
               ==> ival(read(memory :> bytes16(word_add a (word(2 * i)))) s)= ival(x i) rem &3329)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [memory :> bytes(a,32)] ,, MAYCHANGE [RIP] ,, MAYCHANGE[ZMM12] ,, MAYCHANGE[ZMM2])`,

  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REWRITE_TAC[fst MLKEM_POLY_REDUCE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS] THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add a (word n))) s0`))
            (0--15))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN


  (* X86_STEPS_TAC MLKEM_POLY_REDUCE_EXEC (1--10) THEN *)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_REDUCE_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC_LOCAL[barred_x86])
            (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN


  RULE_ASSUM_TAC(REWRITE_RULE[GSYM barred_x86]) THEN
  SIMD_SIMPLIFY_TAC_LOCAL [] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[overall_lemma4]) THEN

  (* Try to prove the postcondition and frame as much as possible *)
  ENSURES_FINAL_STATE_TAC THEN


   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  (*** Now the result is just a replicated instance of our lemma ***)

  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s10" THEN
  REWRITE_TAC[GSYM barred_x86; overall_lemma4] THEN
  REWRITE_TAC[helper_lemma] THEN

  ASM_REWRITE_TAC[] THEN

(* 

  (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)

  (* Proving equivalence *)
  (* Use all_simd_rules to rewrite simd16, simd8, simd4, and simd2 *)
  REWRITE_TAC all_simd_rules THEN 
  (* Rewrite DIMINDEX *)
  DIMINDEX_TAC THEN

  CONV_TAC (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN 
    
  REFL_TAC *)


  );;