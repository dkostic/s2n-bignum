(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Deduce if a bignum is zero.                                               *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/generic/bignum_iszero.o";;
 ****)

let bignum_iszero_mc =
  define_assert_from_elf "bignum_iszero_mc" "x86/generic/bignum_iszero.o"
[
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x10;              (* JE (Imm8 (word 16)) *)
  0x48; 0x0b; 0x44; 0xfe; 0xf8;
                           (* OR (% rax) (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf6;              (* JNE (Imm8 (word 246)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0xc3                     (* RET *)
];;

let BIGNUM_ISZERO_EXEC = X86_MK_CORE_EXEC_RULE bignum_iszero_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_ISZERO_CORRECT = prove
 (`!k a x pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST bignum_iszero_mc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read RIP s' = word(pc + 0x1b) /\
                C_RETURN s' = if x = 0 then word 1 else word 0)
          (MAYCHANGE [RIP; RAX; RDI] ,,
           MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; BIGNUM_ISZERO_EXEC] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    X86_SIM_TAC BIGNUM_ISZERO_EXEC (1--4);
    ALL_TAC] THEN

  ENSURES_WHILE_PDOWN_TAC `k:num` `pc + 0x08` `pc + 0x10`
   `\i s. (bignum_from_memory (a,i) s = lowdigits x i /\
           read RSI s = a /\
           read RDI s = word i /\
           (read RAX s = word 0 <=> highdigits x i = 0)) /\
          (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    X86_SIM_TAC BIGNUM_ISZERO_EXEC (1--3);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i + 1` THEN
    GHOST_INTRO_TAC `d:int64` `read RAX` THEN
    MP_TAC(SPEC `i:num` WORD_INDEX_WRAP) THEN DISCH_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
    X86_SIM_TAC BIGNUM_ISZERO_EXEC (1--2) THEN
    REWRITE_TAC[WORD_OR_EQ_0; VAL_WORD_1] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC; ARITH_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_0; VAL_WORD_BIGDIGIT];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN X86_SIM_TAC BIGNUM_ISZERO_EXEC [1];
    X86_SIM_TAC BIGNUM_ISZERO_EXEC (1--4) THEN
    REWRITE_TAC[HIGHDIGITS_0; WORD_BITVAL; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV]);;

let BIGNUM_ISZERO_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_iszero_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                C_RETURN s' = if x = 0 then word 1 else word 0)
          (MAYCHANGE [RIP; RSP; RAX; RDI] ,,
           MAYCHANGE SOME_FLAGS)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_iszero_mc BIGNUM_ISZERO_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_bignum_iszero_mc = define_from_elf
   "windows_bignum_iszero_mc" "x86/generic/bignum_iszero.obj";;

let WINDOWS_BIGNUM_ISZERO_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,0x26); (a,8 * val k)]
        ==> ensures x86
              (\s. bytes_loaded s (word pc) windows_bignum_iszero_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [k;a] s /\
                   bignum_from_memory(a,val k) s = x)
              (\s'. read RIP s' = returnaddress /\
                    read RSP s' = word_add stackpointer (word 8) /\
                    WINDOWS_C_RETURN s' = if x = 0 then word 1 else word 0)
              (MAYCHANGE [RIP; RSP; RAX] ,,
               MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_bignum_iszero_mc bignum_iszero_mc
    BIGNUM_ISZERO_CORRECT);;
