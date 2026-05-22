(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multi-iteration loop16 kernel for crc32c_octo_zerofill_xor.               *)
(* Wraps the Phase 7 single-iteration body in ENSURES_WHILE_UP_TAC.          *)
(*                                                                           *)
(* This is Phase 8 of the crc32c_octo_zerofill_xor plan.                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_bridge.ml";;
needs "arm/proofs/crc32c_loop16_body.ml";;

(**** print_literal_from_elf "arm/crc32/crc32c_loop16.o";;
 ****)

let crc32c_loop16_mc = define_assert_from_elf
 "crc32c_loop16_mc" "arm/crc32/crc32c_loop16.o"
[
  0xa9404410;       (* arm_LDP X16 X17 X0 (Immediate_Offset (iword (&0))) *)
  0x9ad05d08;       (* arm_CRC32CX W8 W8 X16 *)
  0x9ad15d08;       (* arm_CRC32CX W8 W8 X17 *)
  0xa8817c1f;       (* arm_STP XZR XZR X0 (Postimmediate_Offset (iword (&16))) *)
  0xa9404430;       (* arm_LDP X16 X17 X1 (Immediate_Offset (iword (&0))) *)
  0x9ad05d29;       (* arm_CRC32CX W9 W9 X16 *)
  0x9ad15d29;       (* arm_CRC32CX W9 W9 X17 *)
  0xa8817c3f;       (* arm_STP XZR XZR X1 (Postimmediate_Offset (iword (&16))) *)
  0xa9404450;       (* arm_LDP X16 X17 X2 (Immediate_Offset (iword (&0))) *)
  0x9ad05d4a;       (* arm_CRC32CX W10 W10 X16 *)
  0x9ad15d4a;       (* arm_CRC32CX W10 W10 X17 *)
  0xa8817c5f;       (* arm_STP XZR XZR X2 (Postimmediate_Offset (iword (&16))) *)
  0xa9404470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&0))) *)
  0x9ad05d6b;       (* arm_CRC32CX W11 W11 X16 *)
  0x9ad15d6b;       (* arm_CRC32CX W11 W11 X17 *)
  0xa8817c7f;       (* arm_STP XZR XZR X3 (Postimmediate_Offset (iword (&16))) *)
  0xa9404490;       (* arm_LDP X16 X17 X4 (Immediate_Offset (iword (&0))) *)
  0x9ad05d8c;       (* arm_CRC32CX W12 W12 X16 *)
  0x9ad15d8c;       (* arm_CRC32CX W12 W12 X17 *)
  0xa8817c9f;       (* arm_STP XZR XZR X4 (Postimmediate_Offset (iword (&16))) *)
  0xa94044b0;       (* arm_LDP X16 X17 X5 (Immediate_Offset (iword (&0))) *)
  0x9ad05dad;       (* arm_CRC32CX W13 W13 X16 *)
  0x9ad15dad;       (* arm_CRC32CX W13 W13 X17 *)
  0xa8817cbf;       (* arm_STP XZR XZR X5 (Postimmediate_Offset (iword (&16))) *)
  0xa94044d0;       (* arm_LDP X16 X17 X6 (Immediate_Offset (iword (&0))) *)
  0x9ad05dce;       (* arm_CRC32CX W14 W14 X16 *)
  0x9ad15dce;       (* arm_CRC32CX W14 W14 X17 *)
  0xa8817cdf;       (* arm_STP XZR XZR X6 (Postimmediate_Offset (iword (&16))) *)
  0xa94044f0;       (* arm_LDP X16 X17 X7 (Immediate_Offset (iword (&0))) *)
  0x9ad05def;       (* arm_CRC32CX W15 W15 X16 *)
  0x9ad15def;       (* arm_CRC32CX W15 W15 X17 *)
  0xa8817cff;       (* arm_STP XZR XZR X7 (Postimmediate_Offset (iword (&16))) *)
  0xd1004273;       (* arm_SUB X19 X19 (rvalue (word 16)) *)
  0xf100427f;       (* arm_CMP X19 (rvalue (word 16)) *)
  0x54fffbca;       (* arm_BGE (word 2097044) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CRC32C_LOOP16_EXEC = ARM_MK_EXEC_RULE crc32c_loop16_mc;;

(* ------------------------------------------------------------------------- *)
(* Helper: list of 16 LE bytes from a (lo,hi) pair of int64s.                *)
(* This is the byte enumeration the postcondition feeds into crc32c_bytes,   *)
(* matching the layout already established in Phase 7.                       *)
(* ------------------------------------------------------------------------- *)

let chunk16_bytes = define
 `chunk16_bytes (lo:int64) (hi:int64) : byte list =
   [word_subword lo (0,8); word_subword lo (8,8);
    word_subword lo (16,8); word_subword lo (24,8);
    word_subword lo (32,8); word_subword lo (40,8);
    word_subword lo (48,8); word_subword lo (56,8);
    word_subword hi (0,8); word_subword hi (8,8);
    word_subword hi (16,8); word_subword hi (24,8);
    word_subword hi (32,8); word_subword hi (40,8);
    word_subword hi (48,8); word_subword hi (56,8)]`;;

(* ------------------------------------------------------------------------- *)
(* Iterated chunk concatenation: bytes consumed by buffer n through          *)
(* iteration count i, given per-iteration ghosts m_lo/m_hi (j:num).          *)
(* Defined recursively over j with APPEND so it interacts cleanly with       *)
(* crc32c_bytes_APPEND in the body subgoal.                                  *)
(* ------------------------------------------------------------------------- *)

let consumed_bytes = define
 `(consumed_bytes (m_lo:num->int64) (m_hi:num->int64) 0 = []) /\
  (consumed_bytes (m_lo:num->int64) (m_hi:num->int64) (SUC j) =
     APPEND (consumed_bytes m_lo m_hi j) (chunk16_bytes (m_lo j) (m_hi j)))`;;

let CONSUMED_BYTES_STEP = prove
 (`!m_lo m_hi j.
        consumed_bytes m_lo m_hi (j + 1) =
        APPEND (consumed_bytes m_lo m_hi j) (chunk16_bytes (m_lo j) (m_hi j))`,
  REWRITE_TAC[GSYM ADD1; consumed_bytes]);;

(* ------------------------------------------------------------------------- *)
(* Loop16 multi-iteration correctness.                                       *)
(*                                                                           *)
(* For iters >= 1 and residue < 16 with 16*iters + residue < 2^64, starting  *)
(* with X19 = word(16*iters + residue), the loop runs exactly `iters`        *)
(* iterations: each pointer X0..X7 advances by 16*iters bytes; the consumed  *)
(* prefix at each buffer becomes zero; each accumulator W8..W15 folds the    *)
(* concatenation of all per-iteration 16-byte chunks; X19 ends at            *)
(* word residue. PC ends at pc + 0x8c (at RET, after b.ge falls through).    *)
(* ------------------------------------------------------------------------- *)

let CRC32C_LOOP16_CORRECT = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7
    init0 init1 init2 init3 init4 init5 init6 init7
    (m0_lo:num->int64) (m0_hi:num->int64)
    (m1_lo:num->int64) (m1_hi:num->int64)
    (m2_lo:num->int64) (m2_hi:num->int64)
    (m3_lo:num->int64) (m3_hi:num->int64)
    (m4_lo:num->int64) (m4_hi:num->int64)
    (m5_lo:num->int64) (m5_hi:num->int64)
    (m6_lo:num->int64) (m6_hi:num->int64)
    (m7_lo:num->int64) (m7_hi:num->int64)
    iters residue pc.
        1 <= iters /\
        residue < 16 /\
        16 * iters + residue < 2 EXP 63 /\
        PAIRWISE nonoverlapping
         [(word pc, LENGTH crc32c_loop16_mc);
          (a0, 16 * iters); (a1, 16 * iters);
          (a2, 16 * iters); (a3, 16 * iters);
          (a4, 16 * iters); (a5, 16 * iters);
          (a6, 16 * iters); (a7, 16 * iters)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) crc32c_loop16_mc /\
                  read PC s = word pc /\
                  read X0 s = a0 /\ read X1 s = a1 /\
                  read X2 s = a2 /\ read X3 s = a3 /\
                  read X4 s = a4 /\ read X5 s = a5 /\
                  read X6 s = a6 /\ read X7 s = a7 /\
                  read X8 s = word_zx (init0:int32) /\
                  read X9 s = word_zx (init1:int32) /\
                  read X10 s = word_zx (init2:int32) /\
                  read X11 s = word_zx (init3:int32) /\
                  read X12 s = word_zx (init4:int32) /\
                  read X13 s = word_zx (init5:int32) /\
                  read X14 s = word_zx (init6:int32) /\
                  read X15 s = word_zx (init7:int32) /\
                  read X19 s = word(16 * iters + residue) /\
                  (!j. j < iters ==>
                     read (memory :> bytes64
                            (word_add a0 (word(16 * j)))) s = m0_lo j /\
                     read (memory :> bytes64
                            (word_add a0 (word(16 * j + 8)))) s = m0_hi j /\
                     read (memory :> bytes64
                            (word_add a1 (word(16 * j)))) s = m1_lo j /\
                     read (memory :> bytes64
                            (word_add a1 (word(16 * j + 8)))) s = m1_hi j /\
                     read (memory :> bytes64
                            (word_add a2 (word(16 * j)))) s = m2_lo j /\
                     read (memory :> bytes64
                            (word_add a2 (word(16 * j + 8)))) s = m2_hi j /\
                     read (memory :> bytes64
                            (word_add a3 (word(16 * j)))) s = m3_lo j /\
                     read (memory :> bytes64
                            (word_add a3 (word(16 * j + 8)))) s = m3_hi j /\
                     read (memory :> bytes64
                            (word_add a4 (word(16 * j)))) s = m4_lo j /\
                     read (memory :> bytes64
                            (word_add a4 (word(16 * j + 8)))) s = m4_hi j /\
                     read (memory :> bytes64
                            (word_add a5 (word(16 * j)))) s = m5_lo j /\
                     read (memory :> bytes64
                            (word_add a5 (word(16 * j + 8)))) s = m5_hi j /\
                     read (memory :> bytes64
                            (word_add a6 (word(16 * j)))) s = m6_lo j /\
                     read (memory :> bytes64
                            (word_add a6 (word(16 * j + 8)))) s = m6_hi j /\
                     read (memory :> bytes64
                            (word_add a7 (word(16 * j)))) s = m7_lo j /\
                     read (memory :> bytes64
                            (word_add a7 (word(16 * j + 8)))) s = m7_hi j))
             (\s. read PC s = word(pc + 0x8c) /\
                  read X0 s = word_add a0 (word(16 * iters)) /\
                  read X1 s = word_add a1 (word(16 * iters)) /\
                  read X2 s = word_add a2 (word(16 * iters)) /\
                  read X3 s = word_add a3 (word(16 * iters)) /\
                  read X4 s = word_add a4 (word(16 * iters)) /\
                  read X5 s = word_add a5 (word(16 * iters)) /\
                  read X6 s = word_add a6 (word(16 * iters)) /\
                  read X7 s = word_add a7 (word(16 * iters)) /\
                  read X8 s =
                    word_zx
                     (crc32c_bytes init0 (consumed_bytes m0_lo m0_hi iters)) /\
                  read X9 s =
                    word_zx
                     (crc32c_bytes init1 (consumed_bytes m1_lo m1_hi iters)) /\
                  read X10 s =
                    word_zx
                     (crc32c_bytes init2 (consumed_bytes m2_lo m2_hi iters)) /\
                  read X11 s =
                    word_zx
                     (crc32c_bytes init3 (consumed_bytes m3_lo m3_hi iters)) /\
                  read X12 s =
                    word_zx
                     (crc32c_bytes init4 (consumed_bytes m4_lo m4_hi iters)) /\
                  read X13 s =
                    word_zx
                     (crc32c_bytes init5 (consumed_bytes m5_lo m5_hi iters)) /\
                  read X14 s =
                    word_zx
                     (crc32c_bytes init6 (consumed_bytes m6_lo m6_hi iters)) /\
                  read X15 s =
                    word_zx
                     (crc32c_bytes init7 (consumed_bytes m7_lo m7_hi iters)) /\
                  read X19 s = word residue /\
                  (!j. j < iters ==>
                     read (memory :> bytes64
                            (word_add a0 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a0 (word(16 * j + 8)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a1 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a1 (word(16 * j + 8)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a2 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a2 (word(16 * j + 8)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a3 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a3 (word(16 * j + 8)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a4 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a4 (word(16 * j + 8)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a5 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a5 (word(16 * j + 8)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a6 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a6 (word(16 * j + 8)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a7 (word(16 * j)))) s = word 0 /\
                     read (memory :> bytes64
                            (word_add a7 (word(16 * j + 8)))) s = word 0))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7;
                      X8; X9; X10; X11; X12; X13; X14; X15;
                      X16; X17; X19] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a0, 16 * iters);
                      memory :> bytes(a1, 16 * iters);
                      memory :> bytes(a2, 16 * iters);
                      memory :> bytes(a3, 16 * iters);
                      memory :> bytes(a4, 16 * iters);
                      memory :> bytes(a5, 16 * iters);
                      memory :> bytes(a6, 16 * iters);
                      memory :> bytes(a7, 16 * iters)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  STRIP_TAC THEN

  ENSURES_WHILE_UP_TAC `iters:num` `pc:num` `pc + 0x84`
   `\i s. aligned_bytes_loaded s (word pc) crc32c_loop16_mc /\
          read X0 s = word_add a0 (word(16 * i)) /\
          read X1 s = word_add a1 (word(16 * i)) /\
          read X2 s = word_add a2 (word(16 * i)) /\
          read X3 s = word_add a3 (word(16 * i)) /\
          read X4 s = word_add a4 (word(16 * i)) /\
          read X5 s = word_add a5 (word(16 * i)) /\
          read X6 s = word_add a6 (word(16 * i)) /\
          read X7 s = word_add a7 (word(16 * i)) /\
          read X8 s = word_zx
            (crc32c_bytes init0 (consumed_bytes m0_lo m0_hi i)) /\
          read X9 s = word_zx
            (crc32c_bytes init1 (consumed_bytes m1_lo m1_hi i)) /\
          read X10 s = word_zx
            (crc32c_bytes init2 (consumed_bytes m2_lo m2_hi i)) /\
          read X11 s = word_zx
            (crc32c_bytes init3 (consumed_bytes m3_lo m3_hi i)) /\
          read X12 s = word_zx
            (crc32c_bytes init4 (consumed_bytes m4_lo m4_hi i)) /\
          read X13 s = word_zx
            (crc32c_bytes init5 (consumed_bytes m5_lo m5_hi i)) /\
          read X14 s = word_zx
            (crc32c_bytes init6 (consumed_bytes m6_lo m6_hi i)) /\
          read X15 s = word_zx
            (crc32c_bytes init7 (consumed_bytes m7_lo m7_hi i)) /\
          read X19 s = word(16 * (iters - i) + residue) /\
          (!j. j < i ==>
             read (memory :> bytes64 (word_add a0 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a0 (word(16 * j + 8)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a1 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a1 (word(16 * j + 8)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a2 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a2 (word(16 * j + 8)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a3 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a3 (word(16 * j + 8)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a4 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a4 (word(16 * j + 8)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a5 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a5 (word(16 * j + 8)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a6 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a6 (word(16 * j + 8)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a7 (word(16 * j)))) s
                = word 0 /\
             read (memory :> bytes64 (word_add a7 (word(16 * j + 8)))) s
                = word 0) /\
          (!j. i <= j /\ j < iters ==>
             read (memory :> bytes64 (word_add a0 (word(16 * j)))) s
                = m0_lo j /\
             read (memory :> bytes64 (word_add a0 (word(16 * j + 8)))) s
                = m0_hi j /\
             read (memory :> bytes64 (word_add a1 (word(16 * j)))) s
                = m1_lo j /\
             read (memory :> bytes64 (word_add a1 (word(16 * j + 8)))) s
                = m1_hi j /\
             read (memory :> bytes64 (word_add a2 (word(16 * j)))) s
                = m2_lo j /\
             read (memory :> bytes64 (word_add a2 (word(16 * j + 8)))) s
                = m2_hi j /\
             read (memory :> bytes64 (word_add a3 (word(16 * j)))) s
                = m3_lo j /\
             read (memory :> bytes64 (word_add a3 (word(16 * j + 8)))) s
                = m3_hi j /\
             read (memory :> bytes64 (word_add a4 (word(16 * j)))) s
                = m4_lo j /\
             read (memory :> bytes64 (word_add a4 (word(16 * j + 8)))) s
                = m4_hi j /\
             read (memory :> bytes64 (word_add a5 (word(16 * j)))) s
                = m5_lo j /\
             read (memory :> bytes64 (word_add a5 (word(16 * j + 8)))) s
                = m5_hi j /\
             read (memory :> bytes64 (word_add a6 (word(16 * j)))) s
                = m6_lo j /\
             read (memory :> bytes64 (word_add a6 (word(16 * j + 8)))) s
                = m6_hi j /\
             read (memory :> bytes64 (word_add a7 (word(16 * j)))) s
                = m7_lo j /\
             read (memory :> bytes64 (word_add a7 (word(16 * j + 8)))) s
                = m7_hi j)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [
    (* Subgoal 0: ~(iters = 0), discharged from `1 <= iters`. *)
    ASM_ARITH_TAC;
    (* Subgoal 1: pc -> pc1 (i.e. pc -> pc), i = 0. Trivial since pc = pc1. *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[consumed_bytes; crc32c_bytes_NIL; MULT_CLAUSES;
                    SUB_0; WORD_ADD_0; LT; LE_0];
    (* Subgoal 2: body, invariant(i) at pc -> invariant(i+1) at pc + 0x84. *)
    CHEAT_TAC;
    (* Subgoal 3: back-edge, invariant(i) at pc + 0x84 -> invariant(i) at pc.
       After CMP + BGE, the conditional collapses to `word pc` because the
       value `16 * (iters - i) + residue` is in [16, 2^63) and BGE-taken iff
       NF == VF. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC CRC32C_LOOP16_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `16 * (iters - i) + residue < 2 EXP 63 /\
       16 <= 16 * (iters - i) + residue`
    MP_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
        [`16 * iters + residue < 2 EXP 63`;
         `0 < i`; `i < iters:num`; `residue < 16`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`16 * (iters - i) + residue:num`, `n:num`) THEN
    GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `ival(word n:int64) = &n` SUBST1_TAC THENL
     [REWRITE_TAC[ival; DIMINDEX_64; VAL_WORD] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 2 EXP 63 ==> n < 2 EXP 64`] THEN
      COND_CASES_TAC THENL
       [REFL_TAC;
        UNDISCH_TAC `n < 2 EXP 63` THEN
        UNDISCH_TAC `~(n < 2 EXP (64 - 1))` THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `word_sub (word n:int64) (word 16) = word(n - 16):int64`
    SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `ival(word(n - 16):int64) = &n - &16` SUBST1_TAC THENL
     [REWRITE_TAC[ival; DIMINDEX_64; VAL_WORD] THEN
      ASM_SIMP_TAC[MOD_LT;
        ARITH_RULE `n < 2 EXP 63 /\ 16 <= n ==> n - 16 < 2 EXP 64`] THEN
      COND_CASES_TAC THENL
       [MAP_EVERY (fun t -> UNDISCH_TAC t) [`16 <= n:num`; `n < 2 EXP 63`] THEN
        ARITH_TAC;
        MAP_EVERY (fun t -> UNDISCH_TAC t) [`16 <= n:num`; `n < 2 EXP 63`] THEN
        UNDISCH_TAC `~(n - 16 < 2 EXP (64 - 1))` THEN ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[INT_LT_SUB_RADD; INT_ADD_LID; INT_OF_NUM_LT] THEN
    COND_CASES_TAC THENL [REFL_TAC; ASM_ARITH_TAC];
    (* Subgoal 4: exit, invariant(iters) at pc + 0x84 -> postcondition. *)
    CHEAT_TAC
  ]);;
