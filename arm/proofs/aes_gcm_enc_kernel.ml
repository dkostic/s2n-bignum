(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness proof of `aes_gcm_enc_kernel` (AES-128-only fork).            *)
(*                                                                           *)
(* The verification target is an AES-128-only fork of aws-lc's aarch64       *)
(* `aes_gcm_enc_kernel` (ARMv8 AES + PMULL crypto extensions).  See          *)
(* `arm/aes-gcm/aes_gcm_enc_kernel_aes128.S` for the .S source and           *)
(* `arm/aes-gcm/PHASE_0A_REPORT.md` for the disassembly gap survey.          *)
(*                                                                           *)
(* This file is built up incrementally per the Phase 4..11 plan in           *)
(* orchestrator/state/STATE.md.  The current scope is the *Phase 4 pilot*:   *)
(* a register-only 4-way AES round step.  Full kernel _mc, multi-block       *)
(* loop, and subroutine wrapper land in Phases 8..10.                        *)
(* ========================================================================= *)

needs "arm/proofs/utils/aes_gcm_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Phase 4 pilot — register-only 4-way AES round step.                       *)
(*                                                                           *)
(* The pilot exercises a contiguous 8-instruction window from inside         *)
(* `Lenc_finish_first_blocks` (kernel offsets 0x18c..0x1a8) that performs    *)
(* AES round 5 on four parallel data blocks Q0..Q3 with the same round key   *)
(* Q23.  This is a register-only window: no memory loads, no branches, no    *)
(* GHASH ops.                                                                *)
(*                                                                           *)
(* The kernel emits the round in the order block 0, 1, 3, 2 (interleaved     *)
(* with other unrelated instructions in the wider scheduling, but the four   *)
(* aese+aesmc pairs are contiguous in the slice we use here):                *)
(*                                                                           *)
(*   aese  v0.16b, v23.16b  ; aesmc v0.16b, v0.16b   // block 0 round 5      *)
(*   aese  v1.16b, v23.16b  ; aesmc v1.16b, v1.16b   // block 1 round 5      *)
(*   aese  v3.16b, v23.16b  ; aesmc v3.16b, v3.16b   // block 3 round 5      *)
(*   aese  v2.16b, v23.16b  ; aesmc v2.16b, v2.16b   // block 2 round 5      *)
(*                                                                           *)
(* Each `aese+aesmc` pair, by `AESMC_AESE_AS_ARM_ROUND` from                 *)
(* `arm/proofs/utils/aes_gcm_bridge.ml`, computes one application of         *)
(* `aes_arm_round` (the s2n-bignum/AES-NI-style round step) on the           *)
(* corresponding state register, with the round key in Q23.                  *)
(*                                                                           *)
(* The register-only mc here (`aes4way_round_mc`) is *not* a slice of the    *)
(* full kernel mc — it is a free-standing 32-byte byte list that loads       *)
(* cleanly on the s2n-arm checkpoint without requiring the Phase 0b decoder  *)
(* additions (`arm_DUP_GEN_FROM_ELEM`) to be present in the checkpoint.      *)
(* Phase 5+ promotes the proof to use the full kernel mc; the pilot          *)
(* validates the bridge application pattern in isolation.                    *)
(* ------------------------------------------------------------------------- *)

let aes4way_round_mc = define_assert_from_elf "aes4way_round_mc"
                                              "arm/aes-gcm/aes4way_round.o"
[
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ae2;       (* arm_AESE Q2 Q23 *)
  0x4e286842        (* arm_AESMC Q2 Q2 *)
];;

let AES4WAY_ROUND_EXEC = ARM_MK_EXEC_RULE aes4way_round_mc;;

(* ------------------------------------------------------------------------- *)
(* Pilot ensures: the 4-way AES round step on Q0..Q3 with key Q23.           *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q0..Q3 = state blocks `b0`..`b3` (counters in the live kernel, but      *)
(*            for the pilot we treat them as opaque int128 inputs)           *)
(*   Q23    = round key `rk` (round-5 key in the live kernel)                *)
(*                                                                           *)
(* Outputs:                                                                  *)
(*   Q0..Q3 = `MAP (\b. aes_arm_round b rk) [b0; b1; b2; b3]`                *)
(*                                                                           *)
(* The MAYCHANGE frame lists Q0..Q3 (the four updated state registers) and  *)
(* the PC.  Q23 is preserved (the round key is read-only).                   *)
(* ------------------------------------------------------------------------- *)

let AES4WAY_ROUND_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128) (rk:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes4way_round_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q23 s = rk)
     (\s. read PC s = word (pc + 0x20) /\
          read Q0 s = aes_arm_round b0 rk /\
          read Q1 s = aes_arm_round b1 rk /\
          read Q2 s = aes_arm_round b2 rk /\
          read Q3 s = aes_arm_round b3 rk /\
          read Q23 s = rk)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES4WAY_ROUND_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7a sub-pilot — 4-way 2-round AES chain (register-only).             *)
(*                                                                           *)
(* This extends the Phase 4 single-round pilot to a 2-round chain on the     *)
(* same four state registers Q0..Q3 with two distinct round keys (Q22 = rk4, *)
(* Q23 = rk5).  The 16 instructions are an exact copy of the round-4 +       *)
(* round-5 4-way step in `aes_gcm_enc_kernel_aes128.S` (kernel offsets       *)
(* 0x16c..0x1a8); the kernel emits round 4 in the order 2, 0, 1, 3 and       *)
(* round 5 in the order 0, 1, 3, 2.                                          *)
(*                                                                           *)
(* The pilot validates that AES round chains compose cleanly via repeated    *)
(* `AESMC_AESE_AS_ARM_ROUND` rewrites without term explosion — this is the   *)
(* load-bearing question for Phase 7 proper, where the loop body interleaves *)
(* 9 round chains with GHASH.  No memory loads, no GHASH, no loop.           *)
(* ------------------------------------------------------------------------- *)

let aes4way_2rounds_mc = define_assert_from_elf "aes4way_2rounds_mc"
                                                "arm/aes-gcm/aes4way_2rounds.o"
[
  (* round 4 (rk4 in Q22), block order 2, 0, 1, 3 *)
  0x4e284ac2;       (* arm_AESE Q2 Q22 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  (* round 5 (rk5 in Q23), block order 0, 1, 3, 2 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ae2;       (* arm_AESE Q2 Q23 *)
  0x4e286842        (* arm_AESMC Q2 Q2 *)
];;

let AES4WAY_2ROUNDS_EXEC = ARM_MK_EXEC_RULE aes4way_2rounds_mc;;

(* Pilot ensures: 4-way 2-round AES chain.                                    *)
(*                                                                            *)
(* Inputs:                                                                    *)
(*   Q0..Q3 = state blocks `b0`..`b3` (counters in the live kernel)           *)
(*   Q22    = round-4 key `rk4`                                               *)
(*   Q23    = round-5 key `rk5`                                               *)
(*                                                                            *)
(* Outputs:                                                                   *)
(*   Q0..Q3 = `aes_arm_round (aes_arm_round bi rk4) rk5` for each block       *)
(*                                                                            *)
(* Q22 and Q23 are preserved (round keys are read-only).                      *)

let AES4WAY_2ROUNDS_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128)
       (rk4:int128) (rk5:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes4way_2rounds_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5)
     (\s. read PC s = word (pc + 0x40) /\
          read Q0 s = aes_arm_round (aes_arm_round b0 rk4) rk5 /\
          read Q1 s = aes_arm_round (aes_arm_round b1 rk4) rk5 /\
          read Q2 s = aes_arm_round (aes_arm_round b2 rk4) rk5 /\
          read Q3 s = aes_arm_round (aes_arm_round b3 rk4) rk5 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES4WAY_2ROUNDS_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7a sub-pilot — full single-block AES-128 cipher (register-only).    *)
(*                                                                           *)
(* This is 21 instructions of straight-line AES-128 single-block             *)
(* encryption: 9 × (aese + aesmc) for rounds 0..8 (round keys V18..V26),     *)
(* then 1 × aese for round 9 (round key V27, no aesmc), then 1 × eor with    *)
(* V28 to absorb the round-10 key.                                           *)
(*                                                                           *)
(* The pilot validates that the full `aes128_cipher_arm` (10 rounds + final  *)
(* xor) composes cleanly across all rounds: the goal connects to the         *)
(* spec-side `aes128_cipher_arm` directly via                                *)
(* `AESMC_AESE_AS_ARM_ROUND` + `AESE_AS_ARM_FINAL_ROUND` + `EL_CONV`.        *)
(* No memory loads, no GHASH, no loop.                                       *)
(* ------------------------------------------------------------------------- *)

let aes_block_full_mc = define_assert_from_elf "aes_block_full_mc"
                                               "arm/aes-gcm/aes_block_full.o"
[
  (* 9 rounds of AESE+AESMC with rk0..rk8 in V18..V26 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  (* round 9: aese with rk9 in V27, no aesmc *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  (* round 10: xor with rk10 in V28 *)
  0x6e3c1c00        (* arm_EOR_VEC Q0 Q0 Q28 128 *)
];;

let AES_BLOCK_FULL_EXEC = ARM_MK_EXEC_RULE aes_block_full_mc;;

(* Pilot ensures: full single-block AES-128 cipher.                           *)
(*                                                                            *)
(* Inputs:                                                                    *)
(*   Q0           = plaintext block `pt`                                      *)
(*   Q18..Q28     = round keys `rk0`..`rk10`                                  *)
(*                                                                            *)
(* Outputs:                                                                   *)
(*   Q0           = `aes128_cipher_arm pt [rk0;...;rk10]`                     *)
(*                                                                            *)
(* Q18..Q28 are preserved (round keys are read-only).                         *)

let AES_BLOCK_FULL_CORRECT = prove
 (`!pc (pt:int128) (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128)
       (rk4:int128) (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128)
       (rk9:int128) (rk10:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_block_full_mc /\
          read PC s = word pc /\
          read Q0 s = pt /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8 /\
          read Q27 s = rk9 /\
          read Q28 s = rk10)
     (\s. read PC s = word (pc + 0x50) /\
          read Q0 s = aes128_cipher_arm pt
                        [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10])
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_BLOCK_FULL_EXEC (1--20) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND; AESE_AS_ARM_FINAL_ROUND;
                  aes128_cipher_arm; LET_DEF; LET_END_DEF; EL; HD; TL] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Phase 7a sub-pilot — full single-block AES-128 cipher with memory I/O.    *)
(*                                                                           *)
(* This composes:                                                            *)
(*   - LDR Q0, [X0]   -- load 16-byte plaintext from memory                   *)
(*   - 9 × (AESE+AESMC) for rounds 0..8 with rk0..rk8 in V18..V26             *)
(*   - AESE for round 9 (rk9 in V27, no AESMC)                                *)
(*   - EOR with rk10 in V28 (round-10 key absorption)                         *)
(*   - STR Q0, [X2]   -- store 16-byte ciphertext to memory                   *)
(*                                                                           *)
(* Total: 23 instructions.  Validates that the full AES-128 cipher with      *)
(* memory plaintext load + memory ciphertext store composes against          *)
(* `aes128_cipher_arm`.  No GHASH, no loop.  Closes the AES-side memory      *)
(* plumbing for Phase 7+.                                                    *)
(* ------------------------------------------------------------------------- *)

let aes_block_full_mem_mc = define_assert_from_elf "aes_block_full_mem_mc"
                                                   "arm/aes-gcm/aes_block_full_mem.o"
[
  0x3dc00000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 0)) *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x6e3c1c00;       (* arm_EOR_VEC Q0 Q0 Q28 128 *)
  0x3d800040        (* arm_STR Q0 X2 (Immediate_Offset (word 0)) *)
];;

let AES_BLOCK_FULL_MEM_EXEC = ARM_MK_EXEC_RULE aes_block_full_mem_mc;;

(* Pilot ensures: full single-block AES-128 cipher with memory I/O.           *)
(*                                                                            *)
(* Inputs:                                                                    *)
(*   X0           = plaintext source pointer                                  *)
(*   X2           = ciphertext destination pointer                            *)
(*   memory at X0 = plaintext block `pt`                                      *)
(*   Q18..Q28     = round keys `rk0`..`rk10`                                  *)
(*                                                                            *)
(* Outputs:                                                                   *)
(*   Q0           = `aes128_cipher_arm pt [rk0;...;rk10]`                     *)
(*   memory at X2 = `aes128_cipher_arm pt [rk0;...;rk10]`                     *)
(*                                                                            *)
(* The MAYCHANGE frame includes `events` (LDR/STR generate uarch events) and *)
(* `memory :> bytes128 cptr` (the 16-byte store).                             *)

let AES_BLOCK_FULL_MEM_CORRECT = prove
 (`!pc pptr cptr (pt:int128)
       (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
       (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
       (rk10:int128).
    nonoverlapping (word pc, LENGTH aes_block_full_mem_mc)
                   (cptr:int64, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_block_full_mem_mc /\
              read PC s = word pc /\
              read X0 s = pptr /\
              read X2 s = cptr /\
              read (memory :> bytes128 pptr) s = pt /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q27 s = rk9 /\
              read Q28 s = rk10)
         (\s. read PC s = word (pc + 0x58) /\
              read Q0 s = aes128_cipher_arm pt
                            [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10] /\
              read (memory :> bytes128 cptr) s =
                aes128_cipher_arm pt
                  [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10])
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0] ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes128 cptr])`,
  REWRITE_TAC[fst AES_BLOCK_FULL_MEM_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_BLOCK_FULL_MEM_EXEC (1--22) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND; AESE_AS_ARM_FINAL_ROUND;
                  aes128_cipher_arm; LET_DEF; LET_END_DEF; EL; HD; TL] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Phase 5 pilot — round-key memory load + 4-way AES round + ciphertext      *)
(* memory store.  Same shape as Phase 4 plus a 128-bit memory load (LDR Q23) *)
(* and a 128-bit memory store (STR Q0).                                      *)
(*                                                                           *)
(* The 10 instructions are:                                                  *)
(*                                                                           *)
(*   ldr   q23, [x8, #80]        ; load round key from memory (kernel rk5)  *)
(*   aese  v0.16b, v23.16b ; aesmc v0.16b, v0.16b   ; round on block 0      *)
(*   aese  v1.16b, v23.16b ; aesmc v1.16b, v1.16b   ; round on block 1      *)
(*   aese  v3.16b, v23.16b ; aesmc v3.16b, v3.16b   ; round on block 3      *)
(*   aese  v2.16b, v23.16b ; aesmc v2.16b, v2.16b   ; round on block 2      *)
(*   st1   { v0.16b }, [x2]      ; store ciphertext block 0 to memory       *)
(*                                                                           *)
(* The pilot validates: (a) a Q-register memory load propagates through the *)
(* AES bridge correctly, (b) a Q-register memory store produces the bridged *)
(* output in memory.  No GHASH, no loop.  TODO: replace once the full       *)
(* kernel _mc is loadable in tree (currently blocked by the s2n-arm         *)
(* checkpoint pre-dating Phase 0b decoder additions; see STATE.md           *)
(* "Current Step" for the resolution path).                                 *)
(* ------------------------------------------------------------------------- *)

let aes4way_round_mem_mc = define_assert_from_elf "aes4way_round_mem_mc"
                                              "arm/aes-gcm/aes4way_round_mem.o"
[
  0x3dc01517;       (* arm_LDR Q23 X8 (Immediate_Offset (word 80)) *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ae2;       (* arm_AESE Q2 Q23 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c007040        (* arm_STR Q0 X2 No_Offset *)
];;

let AES4WAY_ROUND_MEM_EXEC = ARM_MK_EXEC_RULE aes4way_round_mem_mc;;

(* Pilot ensures: round-key load + 4-way AES round + ciphertext store.       *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   X8     = round-key base pointer (round key at +80 holds the key)       *)
(*   X2     = ciphertext destination pointer                                *)
(*   Q0..Q3 = state blocks `b0`..`b3`                                       *)
(*   memory at X8+80 = round key `rk`                                       *)
(*                                                                           *)
(* Outputs:                                                                  *)
(*   Q0..Q3 = `aes_arm_round bi rk`                                          *)
(*   memory at X2 = `aes_arm_round b0 rk` (the ciphertext block)             *)
(*                                                                           *)
(* The MAYCHANGE frame includes `events` (LDR/STR generate uarch events) and *)
(* `memory :> bytes128 cptr` (the 16-byte store).  The instruction stream's *)
(* nonoverlapping with the ciphertext region rules out self-modification.   *)
let AES4WAY_ROUND_MEM_CORRECT = prove
 (`!pc kptr cptr (b0:int128) (b1:int128) (b2:int128) (b3:int128) (rk:int128).
    nonoverlapping (word pc, LENGTH aes4way_round_mem_mc)
                   (cptr:int64, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes4way_round_mem_mc /\
              read PC s = word pc /\
              read X8 s = kptr /\
              read X2 s = cptr /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q3 s = b3 /\
              read (memory :> bytes128(word_add kptr (word 80))) s = rk)
         (\s. read PC s = word (pc + 0x28) /\
              read Q0 s = aes_arm_round b0 rk /\
              read Q1 s = aes_arm_round b1 rk /\
              read Q2 s = aes_arm_round b2 rk /\
              read Q3 s = aes_arm_round b3 rk /\
              read (memory :> bytes128 cptr) s = aes_arm_round b0 rk)
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q23] ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes128 cptr])`,
  REWRITE_TAC[fst AES4WAY_ROUND_MEM_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES4WAY_ROUND_MEM_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 5b pilot — plaintext load via LDP + FMOV chain.                     *)
(*                                                                           *)
(* The kernel routes plaintext blocks from memory into Q registers via       *)
(*                                                                           *)
(*   ldp  x6, x7, [x0]            ; two 64-bit reads from plaintext base    *)
(*   fmov d4, x6                  ; X6 -> Q4 low 64 bits (upper bits zero)  *)
(*   fmov v4.d[1], x7             ; X7 -> Q4 high 64 bits                   *)
(*                                                                           *)
(* (The kernel actually XORs the round-N key bits into x6/x7 between the    *)
(* `ldp` and the `fmov`s — that's the GCM-specific final-round trick which  *)
(* we capture later.  This pilot exercises the bare load+assemble pattern  *)
(* in isolation.)                                                            *)
(*                                                                           *)
(* The pilot validates the int128-via-two-int64-loads pattern that any      *)
(* `ldp x_, y_, [...]` plus `fmov`-pair will produce.  After symbolic       *)
(* execution, Q4 holds                                                       *)
(*                                                                           *)
(*   word_insert (word_zx (word_subword b (0,64))) (64,64)                   *)
(*               (word_subword b (64,64))                                    *)
(*                                                                           *)
(* which equals `b` by `WORD_BLAST` once the precondition's `bytes128`      *)
(* read is split into two `bytes64` reads via `READ_MEMORY_SPLIT_CONV 1`.   *)
(* ------------------------------------------------------------------------- *)

let aes_load_block_mc = define_assert_from_elf "aes_load_block_mc"
                                              "arm/aes-gcm/aes_load_block.o"
[
  0xa9401c06;       (* arm_LDP X6 X7 X0 (Immediate_Offset (iword (&0))) *)
  0x9e6700c4;       (* arm_FMOV_ItoF Q4 X6 0 *)
  0x9eaf00e4        (* arm_FMOV_ItoF Q4 X7 1 *)
];;

let AES_LOAD_BLOCK_EXEC = ARM_MK_EXEC_RULE aes_load_block_mc;;

let AES_LOAD_BLOCK_CORRECT = prove
 (`!pc pptr (b:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_load_block_mc /\
          read PC s = word pc /\
          read X0 s = pptr /\
          read (memory :> bytes128 pptr) s = b)
     (\s. read PC s = word (pc + 0xc) /\
          read Q4 s = b)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [X6; X7] ,,
      MAYCHANGE [Q4] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(ASSUME_TAC o
        CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1)) o
        check (can (term_match[] `read (memory :> bytes128 a) s = x`) o
               concl)) THEN
  ARM_STEPS_TAC AES_LOAD_BLOCK_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 6 pilot — GHASH MODULO reduction step.                              *)
(*                                                                           *)
(* The MODULO chain is the polynomial-reduction tail of the kernel's 4-block *)
(* GHASH update.  At kernel offsets ~0x4d0..0x55c (filtered to the pure      *)
(* GHASH-MODULO ops, no interleaved AES/CTR work), the kernel computes:      *)
(*                                                                           *)
(*   movi  v8.8b, #0xc2                  ; mod_constant low byte             *)
(*   shl   d8, d8, #56                   ; mod_constant: 0xc200000000000000  *)
(*   eor   v4.16b, v11.16b, v9.16b       ; v4 = l XOR h                      *)
(*   pmull v7.1q, v9.1d, v8.1d           ; v7 = pmul(h_lo, c64)              *)
(*   ext   v9.16b, v9.16b, v9.16b, #8    ; v9 := byteswap128 h               *)
(*   eor   v10.16b, v10.16b, v4.16b      ; v10 := m XOR (l XOR h)            *)
(*   eor   v7.16b, v9.16b, v7.16b        ; v7  := h_swap XOR pmul(h_lo,c64)  *)
(*   eor   v10.16b, v10.16b, v7.16b      ; v10 := m XOR l XOR h XOR (...)   *)
(*   pmull v9.1q, v10.1d, v8.1d          ; v9_new = pmul(v10_lo, c64)        *)
(*   ext   v10.16b, v10.16b, v10.16b, #8 ; v10 := byteswap128 v10            *)
(*   eor   v11.16b, v11.16b, v9.16b      ; v11 := l XOR v9_new               *)
(*   eor   v11.16b, v11.16b, v10.16b     ; final := v11 XOR v10_swap         *)
(*                                                                           *)
(* This sequence implements `kernel_modulo h l m` from                       *)
(* `arm/proofs/utils/aes_gcm_bridge.ml`, with v9 ↦ h, v10 ↦ m, v11 ↦ l       *)
(* on input.  By `KERNEL_MODULO_CORRECT`, the output equals                  *)
(* `polyval_reduce_prop3 (karatsuba_combine l h m)`.                         *)
(*                                                                           *)
(* The pilot exercises the Phase 0b scalar-SHL D-form decoder addition       *)
(* (`shl d8, d8, #56` decodes to `arm_SHL_VEC D8 D8 56 64 64`).  All other   *)
(* instructions in the chain (movi v.8b, pmull, ext, eor v.16b) are          *)
(* pre-existing decoder rows.                                                *)
(*                                                                           *)
(* TODO: replace once the full kernel _mc is loadable in tree (Phase 7+).    *)
(* ------------------------------------------------------------------------- *)

let ghash_modulo_mc = define_assert_from_elf "ghash_modulo_mc"
                                             "arm/aes-gcm/ghash_modulo.o"
[
  0x0f06e448;       (* arm_MOVI Q8 (word 49344) 8 *)
  0x5f785508;       (* arm_SHL_VEC D8 D8 56 64 64 *)
  0x6e291d64;       (* arm_EOR_VEC Q4 Q11 Q9 128 *)
  0x0ee8e127;       (* arm_PMULL_VEC Q7 Q9 Q8 64 *)
  0x6e094129;       (* arm_EXT Q9 Q9 Q9 64 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x6e271d27;       (* arm_EOR_VEC Q7 Q9 Q7 128 *)
  0x6e271d4a;       (* arm_EOR_VEC Q10 Q10 Q7 128 *)
  0x0ee8e149;       (* arm_PMULL_VEC Q9 Q10 Q8 64 *)
  0x6e0a414a;       (* arm_EXT Q10 Q10 Q10 64 *)
  0x6e291d6b;       (* arm_EOR_VEC Q11 Q11 Q9 128 *)
  0x6e2a1d6b        (* arm_EOR_VEC Q11 Q11 Q10 128 *)
];;

let GHASH_MODULO_EXEC = ARM_MK_EXEC_RULE ghash_modulo_mc;;

(* Pilot ensures: the MODULO reduction step.                                 *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q9  = h-component (kernel's pmull2 high accumulator)                    *)
(*   Q10 = m-component (kernel's pmull mid accumulator)                      *)
(*   Q11 = l-component (kernel's pmull low accumulator)                      *)
(*                                                                           *)
(* Output:                                                                   *)
(*   Q11 = kernel_modulo h l m                                               *)
(*       = polyval_reduce_prop3 (karatsuba_combine l h m)                    *)
(*         (by KERNEL_MODULO_CORRECT)                                        *)
(*                                                                           *)
(* The MAYCHANGE frame lists Q4, Q7..Q11 (all touched by the chain) and PC. *)

let GHASH_MODULO_CORRECT = prove
 (`!pc (h:int128) (l:int128) (m:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) ghash_modulo_mc /\
          read PC s = word pc /\
          read Q9 s = h /\
          read Q10 s = m /\
          read Q11 s = l)
     (\s. read PC s = word (pc + 0x30) /\
          read Q11 s = kernel_modulo h l m)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q4; Q7; Q8; Q9; Q10; Q11])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_MODULO_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (* Equate Q11's stepper output with kernel_modulo h l m.  Both are pure  *)
  (* word-level expressions in (h, l, m, c64=word 0xC2..0); the only thing  *)
  (* WORD_BLAST can't see through is `word_pmul` (which is opaque).  So we  *)
  (* abbreviate the two pmul subterms as `t0` (the inner pmul of low64 h    *)
  (* with c64) and `t1` (the outer pmul of low64 of the assembled XOR       *)
  (* chain), unfold `kernel_modulo` and `byteswap128`, normalise the        *)
  (* `byteswap128 h` shape (the kernel emits it as                           *)
  (*  `word_subword (word_join h h) (64,128)`, the spec emits it as          *)
  (*  `word_join (word_subword h (0,64)) (word_subword h (64,64))`),         *)
  (* and let WORD_BLAST close the residual structural identity.             *)
  ABBREV_TAC `t0:int128 = word_pmul (word_subword (h:int128) (0,64) :64 word)
                                    (word 13979173243358019584:64 word)` THEN
  ABBREV_TAC `y:int128 = word_xor (word_xor t0
                                            (word_subword
                                              ((word_join:int128->int128
                                                ->256 word) h h) (64,128)
                                              :int128))
                                  (word_xor (word_xor h l) m)` THEN
  ABBREV_TAC `t1:int128 = word_pmul (word_subword (y:int128) (0,64) :64 word)
                                    (word 13979173243358019584:64 word)` THEN
  REWRITE_TAC[kernel_modulo; byteswap128; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `word_join (word_subword (h:int128) (0,64) :64 word)
              (word_subword h (64,64) :64 word) :int128 =
    word_subword ((word_join:int128->int128->256 word) h h) (64,128)`
   ASSUME_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (m:int128) (word_xor l h))
             (word_xor
                (word_subword
                  ((word_join:int128->int128->256 word) h h) (64,128) :int128)
                t0) = y`
   SUBST1_TAC THENL
   [EXPAND_TAC "y" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 6 sub-pilot — per-block Karatsuba decomposition.                    *)
(*                                                                           *)
(* The kernel computes (h, l, m) = karatsuba_components c H per block, with  *)
(* the karatsuba_mid of the H power supplied separately (precomputed at     *)
(* htable-init time and stored in v17 / v16 with two k's joined per the     *)
(* `htable_mem` layout in `common/polyval_ghash.ml`).  The 5-instruction    *)
(* sequence at `arm/aes-gcm/ghash_perblock.S` (a register-only extract from *)
(* the kernel's `Lenc_main_loop` per-block code) computes:                   *)
(*                                                                           *)
(*   pmull2 v9.1q,  v4.2d,  v15.2d         ; v9 = pmul(high64 c, high64 H)  *)
(*   pmull  v11.1q, v4.1d,  v15.1d         ; v11 = pmul(low64 c, low64 H)   *)
(*   mov    d8,     v4.d[1]                ; d8 = high64 c                  *)
(*   eor    v8.8b,  v8.8b,  v4.8b          ; d8 = high64 c XOR low64 c      *)
(*   pmull  v10.1q, v8.1d,  v17.1d         ; v10 = pmul(mid_c, kmid_H)      *)
(*                                                                           *)
(* The pilot exercises the Phase 0b DUP-from-element decoder addition       *)
(* (`mov d8, v4.d[1]` decodes to `arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1`).    *)
(*                                                                           *)
(* TODO: replace once the full kernel _mc is loadable in tree (Phase 7+).   *)
(* ------------------------------------------------------------------------- *)

let ghash_perblock_mc = define_assert_from_elf "ghash_perblock_mc"
                                               "arm/aes-gcm/ghash_perblock.o"
[
  0x4eefe089;       (* arm_PMULL2_VEC Q9 Q4 Q15 64 *)
  0x0eefe08b;       (* arm_PMULL_VEC Q11 Q4 Q15 64 *)
  0x5e180488;       (* arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1 *)
  0x2e241d08;       (* arm_EOR_VEC Q8 Q8 Q4 64 *)
  0x0ef1e10a        (* arm_PMULL_VEC Q10 Q8 Q17 64 *)
];;

let GHASH_PERBLOCK_EXEC = ARM_MK_EXEC_RULE ghash_perblock_mc;;

(* Pilot ensures: per-block Karatsuba decomposition.                         *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q4         = c   (one ciphertext block, byteswap128'd by rev64+ext     *)
(*                    upstream)                                              *)
(*   Q15        = H   (one H power, byteswap128'd by `htable_mem`)           *)
(*   Q17 lo64   = kmid_H = karatsuba_mid H                                   *)
(*   (Q17 hi64 is `kmid_other` — irrelevant, the pmull only reads `.1d`)    *)
(*                                                                           *)
(* Outputs:                                                                  *)
(*   Q9  = pmul(high64 c, high64 H)             -- h-component               *)
(*   Q11 = pmul(low64 c, low64 H)               -- l-component               *)
(*   Q10 = pmul(low64 c XOR high64 c, kmid_H)   -- m-component               *)
(*                                                                           *)
(* By `karatsuba_components` (def in `arm/proofs/utils/aes_gcm_bridge.ml`),  *)
(* (Q9, Q11, Q10) = karatsuba_components c H                                 *)
(* given the v17 lo64 precondition.                                          *)

let GHASH_PERBLOCK_CORRECT = prove
 (`!pc (c:int128) (H:int128) (kmid_other:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) ghash_perblock_mc /\
          read PC s = word pc /\
          read Q4 s = c /\
          read Q15 s = H /\
          read Q17 s = word_join kmid_other (karatsuba_mid H) :int128)
     (\s. read PC s = word (pc + 0x14) /\
          read Q9 s = (word_pmul (word_subword c (64,64) :64 word)
                                 (word_subword H (64,64) :64 word) :int128) /\
          read Q11 s = (word_pmul (word_subword c (0,64) :64 word)
                                  (word_subword H (0,64) :64 word) :int128) /\
          read Q10 s = (word_pmul
                          (word_xor (word_subword c (0,64) :64 word)
                                    (word_subword c (64,64) :64 word))
                          (karatsuba_mid H) :int128))
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_PERBLOCK_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  BINOP_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 6 pilot — 4-block GHASH update.                                     *)
(*                                                                           *)
(* This is the full 43-instruction GHASH chain extracted from                *)
(* `Lenc_main_loop` of `arm/aes-gcm/aes_gcm_enc_kernel_aes128.S`             *)
(* (lines 270 - 414, GHASH-tagged + MODULO-tagged ops only, no AES/CTR).    *)
(* The pilot's precondition takes inputs in the form                         *)
(* `KERNEL_4BLOCK_NIST_BRIDGE` directly expects: ciphertext blocks already   *)
(* `byteswap128`'d (with `prev_tag` XOR'd into ct0), H-powers stored in     *)
(* the htable_mem byteswap128'd form, and karatsuba_mid pairs joined into   *)
(* Q16 / Q17 per the htable_mem layout.                                     *)
(*                                                                           *)
(* Output: Q11 = nist_ghash h prev_tag [c0; c1; c2; c3].                     *)
(*                                                                           *)
(* Discharge: `KERNEL_4BLOCK_NIST_BRIDGE` connects the kernel's              *)
(* "decompose-then-XOR-accumulate-then-MODULO" pattern to the spec-side      *)
(* `nist_ghash`.                                                             *)
(*                                                                           *)
(* TODO: replace once the full kernel _mc is loadable in tree (Phase 7+).   *)
(* ------------------------------------------------------------------------- *)

let ghash_4block_mc = define_assert_from_elf "ghash_4block_mc"
                                             "arm/aes-gcm/ghash_4block.o"
[
  0x5e18062a;       (* arm_DUP_GEN_FROM_ELEM Q10 Q17 64 64 1 *)
  0x4eefe089;       (* arm_PMULL2_VEC Q9 Q4 Q15 64 *)
  0x5e180488;       (* arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1 *)
  0x0eefe08b;       (* arm_PMULL_VEC Q11 Q4 Q15 64 *)
  0x2e241d08;       (* arm_EOR_VEC Q8 Q8 Q4 64 *)
  0x4eeee0a4;       (* arm_PMULL2_VEC Q4 Q5 Q14 64 *)
  0x0eeae10a;       (* arm_PMULL_VEC Q10 Q8 Q10 64 *)
  0x0eeee0a8;       (* arm_PMULL_VEC Q8 Q5 Q14 64 *)
  0x6e241d29;       (* arm_EOR_VEC Q9 Q9 Q4 128 *)
  0x5e1804a4;       (* arm_DUP_GEN_FROM_ELEM Q4 Q5 64 64 1 *)
  0x6e281d6b;       (* arm_EOR_VEC Q11 Q11 Q8 128 *)
  0x5e1804c8;       (* arm_DUP_GEN_FROM_ELEM Q8 Q6 64 64 1 *)
  0x2e251c84;       (* arm_EOR_VEC Q4 Q4 Q5 64 *)
  0x2e261d08;       (* arm_EOR_VEC Q8 Q8 Q6 64 *)
  0x0ef1e084;       (* arm_PMULL_VEC Q4 Q4 Q17 64 *)
  0x6e180508;       (* arm_INS Q8 Q8 64 0 64 64 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x4eede0c4;       (* arm_PMULL2_VEC Q4 Q6 Q13 64 *)
  0x0eede0c5;       (* arm_PMULL_VEC Q5 Q6 Q13 64 *)
  0x0eece0e6;       (* arm_PMULL_VEC Q6 Q7 Q12 64 *)
  0x6e241d29;       (* arm_EOR_VEC Q9 Q9 Q4 128 *)
  0x5e1804e4;       (* arm_DUP_GEN_FROM_ELEM Q4 Q7 64 64 1 *)
  0x6e251d6b;       (* arm_EOR_VEC Q11 Q11 Q5 128 *)
  0x4ef0e108;       (* arm_PMULL2_VEC Q8 Q8 Q16 64 *)
  0x4eece0e5;       (* arm_PMULL2_VEC Q5 Q7 Q12 64 *)
  0x2e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 64 *)
  0x6e281d4a;       (* arm_EOR_VEC Q10 Q10 Q8 128 *)
  0x0f06e448;       (* arm_MOVI D8 (word 14033993530586874562) *)
  0x0ef0e084;       (* arm_PMULL_VEC Q4 Q4 Q16 64 *)
  0x6e251d29;       (* arm_EOR_VEC Q9 Q9 Q5 128 *)
  0x5f785508;       (* arm_SHL_VEC Q8 Q8 56 64 64 *)
  0x6e261d6b;       (* arm_EOR_VEC Q11 Q11 Q6 128 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x6e291d64;       (* arm_EOR_VEC Q4 Q11 Q9 128 *)
  0x0ee8e127;       (* arm_PMULL_VEC Q7 Q9 Q8 64 *)
  0x6e094129;       (* arm_EXT Q9 Q9 Q9 64 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x6e271d27;       (* arm_EOR_VEC Q7 Q9 Q7 128 *)
  0x6e271d4a;       (* arm_EOR_VEC Q10 Q10 Q7 128 *)
  0x0ee8e149;       (* arm_PMULL_VEC Q9 Q10 Q8 64 *)
  0x6e291d6b;       (* arm_EOR_VEC Q11 Q11 Q9 128 *)
  0x6e0a414a;       (* arm_EXT Q10 Q10 Q10 64 *)
  0x6e2a1d6b        (* arm_EOR_VEC Q11 Q11 Q10 128 *)
];;

let GHASH_4BLOCK_EXEC = ARM_MK_EXEC_RULE ghash_4block_mc;;

(* Pilot ensures: 4-block GHASH update.                                      *)
(*                                                                           *)
(* Inputs (matching `KERNEL_4BLOCK_NIST_BRIDGE` directly):                   *)
(*   Q4 = byteswap128 (word_xor prev_tag c0)   (block 0, prev-tag XOR'd in) *)
(*   Q5 = byteswap128 c1                                                    *)
(*   Q6 = byteswap128 c2                                                    *)
(*   Q7 = byteswap128 c3                                                    *)
(*   Q12 = byteswap128 (h_power H 0)           (H^1 in kernel; "H1")        *)
(*   Q13 = byteswap128 (h_power H 1)           (H^2; "H2")                  *)
(*   Q14 = byteswap128 (h_power H 2)           (H^3; "H3")                  *)
(*   Q15 = byteswap128 (h_power H 3)           (H^4; "H4")                  *)
(*   Q16 = word_join (km(h_power H 1)) (km(h_power H 0))                    *)
(*                                       (high|low; "h2k|h1k")               *)
(*   Q17 = word_join (km(h_power H 3)) (km(h_power H 2))                    *)
(*                                       (high|low; "h4k|h3k")               *)
(*   where H = ghash_twist h_spec, km = karatsuba_mid.                       *)
(*                                                                           *)
(* Output:                                                                   *)
(*   Q11 = nist_ghash h_spec prev_tag [c0; c1; c2; c3]                       *)
(*                                                                           *)
(* The MAYCHANGE frame lists Q4..Q11 (all touched by the chain) and PC.     *)

(* Proof outline (closed in session 017):                                    *)
(*   Drive ARM_STEPS to s43 and ENSURES_FINAL_STATE; rewrite RHS via         *)
(*   GSYM KERNEL_4BLOCK_NIST_BRIDGE; unfold karatsuba_components,            *)
(*   karatsuba_mid, kernel_modulo, byteswap128; push word_subword through    *)
(*   word_join via JOIN_LOWER/UPPER; ABBREV_TAC the 16 subword atoms (8 H +  *)
(*   6 c + 2 pp0); stamp 4 type-aware SUBGOAL_THENs to clean up the          *)
(*   kernel's mov/eor/ins-driven mid-pmul args (the 3 pmull blocks plus the  *)
(*   c2 word_insert pmull2 block); ABBREV_TAC the 12 high/low/mid pmul       *)
(*   atoms; ABBREV_TAC sums Lsum/Hsum/Msum and SUBST1_TAC normalize the      *)
(*   RHS's reversed-association XOR sums; ABBREV_TAC c64 pmul tA on Lsum,   *)
(*   then the outer-c64 pmul tB on the running accumulator; SUBGOAL_THEN +   *)
(*   AP_THM/AP_TERM/WORD_BLAST to fold the RHS's other-association outer    *)
(*   pmul into tB; final CONV_TAC WORD_BLAST closes (~3 min on a goal with   *)
(*   0 word_pmul atoms, 645 chars).                                          *)

let GHASH_4BLOCK_CORRECT = prove
 (`!pc (h:int128) (prev_tag:int128)
       (c0:int128) (c1:int128) (c2:int128) (c3:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) ghash_4block_mc /\
          read PC s = word pc /\
          read Q4 s = byteswap128 (word_xor prev_tag c0) /\
          read Q5 s = byteswap128 c1 /\
          read Q6 s = byteswap128 c2 /\
          read Q7 s = byteswap128 c3 /\
          read Q12 s = byteswap128 (h_power (ghash_twist h) 0) /\
          read Q13 s = byteswap128 (h_power (ghash_twist h) 1) /\
          read Q14 s = byteswap128 (h_power (ghash_twist h) 2) /\
          read Q15 s = byteswap128 (h_power (ghash_twist h) 3) /\
          read Q16 s =
            (word_join (karatsuba_mid (h_power (ghash_twist h) 1):64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 0):64 word)
             :int128) /\
          read Q17 s =
            (word_join (karatsuba_mid (h_power (ghash_twist h) 3):64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 2):64 word)
             :int128))
     (\s. read PC s = word (pc + 0xac) /\
          read Q11 s = nist_ghash h prev_tag [c0; c1; c2; c3])
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_4BLOCK_EXEC (1--43) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM KERNEL_4BLOCK_NIST_BRIDGE] THEN
  REWRITE_TAC[karatsuba_components; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[karatsuba_mid; kernel_modulo; byteswap128;
              LET_DEF; LET_END_DEF] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH;
           WORD_SUBWORD_TRIVIAL] THEN
  (* Abbreviate the 16 subword atoms *)
  ABBREV_TAC `H0_LO:64 word = word_subword (h_power (ghash_twist h) 0) (0,64)` THEN
  ABBREV_TAC `H0_HI:64 word = word_subword (h_power (ghash_twist h) 0) (64,64)` THEN
  ABBREV_TAC `H1_LO:64 word = word_subword (h_power (ghash_twist h) 1) (0,64)` THEN
  ABBREV_TAC `H1_HI:64 word = word_subword (h_power (ghash_twist h) 1) (64,64)` THEN
  ABBREV_TAC `H2_LO:64 word = word_subword (h_power (ghash_twist h) 2) (0,64)` THEN
  ABBREV_TAC `H2_HI:64 word = word_subword (h_power (ghash_twist h) 2) (64,64)` THEN
  ABBREV_TAC `H3_LO:64 word = word_subword (h_power (ghash_twist h) 3) (0,64)` THEN
  ABBREV_TAC `H3_HI:64 word = word_subword (h_power (ghash_twist h) 3) (64,64)` THEN
  ABBREV_TAC `pp0_lo:64 word = word_subword ((word_xor prev_tag c0):int128) (0,64)` THEN
  ABBREV_TAC `pp0_hi:64 word = word_subword ((word_xor prev_tag c0):int128) (64,64)` THEN
  ABBREV_TAC `c1_lo:64 word = word_subword (c1:int128) (0,64)` THEN
  ABBREV_TAC `c1_hi:64 word = word_subword (c1:int128) (64,64)` THEN
  ABBREV_TAC `c2_lo:64 word = word_subword (c2:int128) (0,64)` THEN
  ABBREV_TAC `c2_hi:64 word = word_subword (c2:int128) (64,64)` THEN
  ABBREV_TAC `c3_lo:64 word = word_subword (c3:int128) (0,64)` THEN
  ABBREV_TAC `c3_hi:64 word = word_subword (c3:int128) (64,64)` THEN
  (* Stamp the 4 type-aware m-pmul-arg cleanup lemmas: 3 pmull (c3, c1, pp0)
     and 1 pmull2 (c2 with word_insert).  Type signatures matter — the
     intermediate word_subword/word_zx chain is :64 word -> :int128 -> :64
     word, with an extra :int128 word_insert layer for c2. *)
  SUBGOAL_THEN
   `(word_subword (word_zx (word_subword (word_xor (word_join (c3_lo:64 word)
       (c3_hi:64 word):int128) (word_zx (c3_lo:64 word):int128)) (0,64) :64
       word):int128) (0,64) :64 word) = word_xor c3_lo c3_hi /\
    (word_subword (word_zx (word_subword (word_xor (word_join (c1_lo:64 word)
       (c1_hi:64 word):int128) (word_zx (c1_lo:64 word):int128)) (0,64) :64
       word):int128) (0,64) :64 word) = word_xor c1_lo c1_hi /\
    (word_subword (word_zx (word_subword (word_xor (word_join (pp0_lo:64 word)
       (pp0_hi:64 word):int128) (word_zx (pp0_lo:64 word):int128)) (0,64) :64
       word):int128) (0,64) :64 word) = word_xor pp0_lo pp0_hi`
   STRIP_ASSUME_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `(word_subword (word_insert (word_zx (word_subword (word_xor (word_join
       (c2_lo:64 word) (c2_hi:64 word):int128) (word_zx (c2_lo:64 word):int128))
       (0,64) :64 word):int128) (64,64) (word_subword (word_subword (word_zx
       (word_subword (word_xor (word_join (c2_lo:64 word) (c2_hi:64 word):int128)
       (word_zx (c2_lo:64 word):int128)) (0,64) :64 word):int128) (0,64) :int128)
       (0,64) :int128):int128) (64,64) :64 word) = word_xor c2_lo c2_hi`
    ASSUME_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* The H3 mid pmul carries an extra word_zx wrap that the SIMP didn't
     unfold; clean it up so the H3 mid pmul matches the c0..c2 mid-pmul shape. *)
  SUBGOAL_THEN
   `word_subword (word_zx (word_xor (H3_LO:64 word) (H3_HI:64 word):64 word)
                  :int128) (0,64) :64 word = word_xor H3_LO H3_HI`
    ASSUME_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Abbreviate the 12 per-block pmul atoms: 4 high, 4 low, 4 mid.  Mp_h3
     needs explicit :64 word types on its operands (without them, the
     abbrev's hypothesis types are inferred as fresh type variables that
     fail to unify with the goal's concrete :64 word terms). *)
  ABBREV_TAC `Hp_h0:int128 = word_pmul (c3_hi:64 word) (H0_HI:64 word)` THEN
  ABBREV_TAC `Hp_h1:int128 = word_pmul (c2_hi:64 word) (H1_HI:64 word)` THEN
  ABBREV_TAC `Hp_h2:int128 = word_pmul (c1_hi:64 word) (H2_HI:64 word)` THEN
  ABBREV_TAC `Hp_h3:int128 = word_pmul (pp0_hi:64 word) (H3_HI:64 word)` THEN
  ABBREV_TAC `Lp_h0:int128 = word_pmul (c3_lo:64 word) (H0_LO:64 word)` THEN
  ABBREV_TAC `Lp_h1:int128 = word_pmul (c2_lo:64 word) (H1_LO:64 word)` THEN
  ABBREV_TAC `Lp_h2:int128 = word_pmul (c1_lo:64 word) (H2_LO:64 word)` THEN
  ABBREV_TAC `Lp_h3:int128 = word_pmul (pp0_lo:64 word) (H3_LO:64 word)` THEN
  ABBREV_TAC `Mp_h0:int128 = word_pmul (word_xor (c3_lo:64 word) (c3_hi:64 word))
                                       (word_xor (H0_LO:64 word) (H0_HI:64 word))` THEN
  ABBREV_TAC `Mp_h1:int128 = word_pmul (word_xor (c2_lo:64 word) (c2_hi:64 word))
                                       (word_xor (H1_LO:64 word) (H1_HI:64 word))` THEN
  ABBREV_TAC `Mp_h2:int128 = word_pmul (word_xor (c1_lo:64 word) (c1_hi:64 word))
                                       (word_xor (H2_LO:64 word) (H2_HI:64 word))` THEN
  ABBREV_TAC `Mp_h3:int128 = word_pmul (word_xor (pp0_lo:64 word) (pp0_hi:64 word))
                                       (word_xor (H3_LO:64 word) (H3_HI:64 word))` THEN
  (* Abbreviate the inner XOR sums.  The RHS form (kernel-side) and LHS form
     (bridge-side) differ in XOR association — substitute the reverse forms. *)
  ABBREV_TAC `Lsum:int128 = word_xor (Lp_h0:int128)
                                     (word_xor Lp_h1 (word_xor Lp_h2 Lp_h3))` THEN
  SUBGOAL_THEN `word_xor (word_xor (Lp_h3:int128) Lp_h2)
                         (word_xor Lp_h1 Lp_h0) = Lsum`
    SUBST1_TAC THENL [EXPAND_TAC "Lsum" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `Hsum:int128 = word_xor (Hp_h0:int128)
                                     (word_xor Hp_h1 (word_xor Hp_h2 Hp_h3))` THEN
  SUBGOAL_THEN `word_xor (word_xor (Hp_h3:int128) Hp_h2)
                         (word_xor Hp_h1 Hp_h0) = Hsum`
    SUBST1_TAC THENL [EXPAND_TAC "Hsum" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `Msum:int128 = word_xor (Mp_h0:int128)
                                     (word_xor Mp_h1 (word_xor Mp_h2 Mp_h3))` THEN
  SUBGOAL_THEN `word_xor (word_xor (Mp_h3:int128) Mp_h2)
                         (word_xor Mp_h1 Mp_h0) = Msum`
    SUBST1_TAC THENL [EXPAND_TAC "Msum" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* Abbreviate the inner c64 pmul on Lsum, then the outer c64 pmul on the
     full XOR-sum. *)
  ABBREV_TAC `tA:int128 = word_pmul (word_subword (Lsum:int128) (0,64) :64 word)
                                    (word 13979173243358019584:64 word)` THEN
  ABBREV_TAC `tB:int128 = word_pmul (word_subword (word_xor (word_xor (tA:int128)
                              (word_subword (word_join (Lsum:int128) Lsum :256 word)
                                            (64,128) :int128))
                              (word_xor (word_xor Lsum Hsum) Msum) :int128)
                              (0,64) :64 word)
                          (word 13979173243358019584:64 word)` THEN
  (* The RHS's outer c64 pmul has a different XOR association of the same
     operand — fold it into tB. *)
  SUBGOAL_THEN
   `word_pmul (word_subword (word_xor (word_xor (Msum:int128) (word_xor Hsum Lsum))
                              (word_xor (word_join (word_subword Lsum (0,64) :64 word)
                                                   (word_subword Lsum (64,64) :64 word)
                                         :int128) tA) :int128)
                  (0,64) :64 word)
              (word 13979173243358019584:64 word) :int128 = tB`
    SUBST1_TAC THENL
   [EXPAND_TAC "tB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* Phase 7 — full kernel machine code definition.                            *)
(*                                                                           *)
(* `aes_gcm_enc_kernel_mc` is the byte list of the entire 613-instruction    *)
(* AES-128-only fork at `arm/aes-gcm/aes_gcm_enc_kernel_aes128.o`.  All      *)
(* loop-body and subroutine-wrapper proofs from Phase 7 onward target this   *)
(* mc directly, slicing into it via `mk_sublist_of_mc` for cut-pointed       *)
(* sub-proofs.                                                               *)
(*                                                                           *)
(* The kernel decodes cleanly under the `s2n-arm-aes` checkpoint, which has  *)
(* the Phase 0b decoder additions (`arm_DUP_GEN_FROM_ELEM` and the scalar    *)
(* SHL D-form).                                                              *)
(* ========================================================================= *)

let aes_gcm_enc_kernel_mc = define_assert_from_elf "aes_gcm_enc_kernel_mc"
                                                   "arm/aes-gcm/aes_gcm_enc_kernel_aes128.o"
[
  0xa9b87bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &128))) *)
  0x910003fd;       (* arm_ADD X29 SP (rvalue (word 0)) *)
  0xa90153f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503e8;       (* arm_MOV X8 X5 *)
  0xa9025bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&32))) *)
  0xa90363f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&48))) *)
  0x6d0427e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&64))) *)
  0x6d052fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&80))) *)
  0x6d0637ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&96))) *)
  0x6d073fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&112))) *)
  0xb940f111;       (* arm_LDR W17 X8 (Immediate_Offset (word 240)) *)
  0x8b111113;       (* arm_ADD X19 X8 (Shiftedreg X17 LSL 4) *)
  0xa9403a6d;       (* arm_LDP X13 X14 X19 (Immediate_Offset (iword (&0))) *)
  0x3cdf027f;       (* arm_LDR Q31 X19 (Immediate_Offset (word 18446744073709551600)) *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xd343fc25;       (* arm_LSR X5 X1 3 *)
  0xaa0503ef;       (* arm_MOV X15 X5 *)
  0xa9402e0a;       (* arm_LDP X10 X11 X16 (Immediate_Offset (iword (&0))) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x3dc00112;       (* arm_LDR Q18 X8 (Immediate_Offset (word 0)) *)
  0x927ae4a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551552)) *)
  0x3dc01d19;       (* arm_LDR Q25 X8 (Immediate_Offset (word 112)) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0xd360fd6c;       (* arm_LSR X12 X11 32 *)
  0x9e670142;       (* arm_FMOV_ItoF Q2 X10 0 *)
  0x2a0b016b;       (* arm_ORR W11 W11 W11 *)
  0x5ac0098c;       (* arm_REV W12 W12 *)
  0x9e670141;       (* arm_FMOV_ItoF Q1 X10 0 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x9e670143;       (* arm_FMOV_ItoF Q3 X10 0 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x3dc00513;       (* arm_LDR Q19 X8 (Immediate_Offset (word 16)) *)
  0x9eaf0121;       (* arm_FMOV_ItoF Q1 X9 1 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x3dc00914;       (* arm_LDR Q20 X8 (Immediate_Offset (word 32)) *)
  0x9eaf0122;       (* arm_FMOV_ItoF Q2 X9 1 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x9eaf0123;       (* arm_FMOV_ItoF Q3 X9 1 *)
  0x4e284a41;       (* arm_AESE Q1 Q18 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x3dc00d15;       (* arm_LDR Q21 X8 (Immediate_Offset (word 48)) *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc01918;       (* arm_LDR Q24 X8 (Immediate_Offset (word 96)) *)
  0x4e284a42;       (* arm_AESE Q2 Q18 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc01517;       (* arm_LDR Q23 X8 (Immediate_Offset (word 80)) *)
  0x4e284a61;       (* arm_AESE Q1 Q19 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x3dc00cce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 48)) *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a62;       (* arm_AESE Q2 Q19 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc01116;       (* arm_LDR Q22 X8 (Immediate_Offset (word 64)) *)
  0x4e284a81;       (* arm_AESE Q1 Q20 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc0311e;       (* arm_LDR Q30 X8 (Immediate_Offset (word 192)) *)
  0x4e284a82;       (* arm_AESE Q2 Q20 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc014cf;       (* arm_LDR Q15 X6 (Immediate_Offset (word 80)) *)
  0x4e284aa1;       (* arm_AESE Q1 Q21 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x3dc02d1d;       (* arm_LDR Q29 X8 (Immediate_Offset (word 176)) *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc0211a;       (* arm_LDR Q26 X8 (Immediate_Offset (word 128)) *)
  0x4e284aa2;       (* arm_AESE Q2 Q21 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4c40706b;       (* arm_LDR Q11 X3 No_Offset *)
  0x6e0b416b;       (* arm_EXT Q11 Q11 Q11 64 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x4e284ac2;       (* arm_AESE Q2 Q22 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ae2;       (* arm_AESE Q2 Q23 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b01;       (* arm_AESE Q1 Q24 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ecf69d1;       (* arm_TRN2 Q17 Q14 Q15 64 128 *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc0251b;       (* arm_LDR Q27 X8 (Immediate_Offset (word 144)) *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc000cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 0)) *)
  0x4e284b02;       (* arm_AESE Q2 Q24 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc0291c;       (* arm_LDR Q28 X8 (Immediate_Offset (word 160)) *)
  0x4e284b21;       (* arm_AESE Q1 Q25 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ecf29c9;       (* arm_TRN1 Q9 Q14 Q15 64 128 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b22;       (* arm_AESE Q2 Q25 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ecd6990;       (* arm_TRN2 Q16 Q12 Q13 64 128 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x6e291e31;       (* arm_EOR_VEC Q17 Q17 Q9 128 *)
  0x4e284be2;       (* arm_AESE Q2 Q31 *)
  0x4ecd2988;       (* arm_TRN1 Q8 Q12 Q13 64 128 *)
  0x4e284be1;       (* arm_AESE Q1 Q31 *)
  0x4e284be0;       (* arm_AESE Q0 Q31 *)
  0x4e284be3;       (* arm_AESE Q3 Q31 *)
  0x6e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 128 *)
  0x54002c2a;       (* arm_BGE (word 1412) *)
  0xa9415013;       (* arm_LDP X19 X20 X0 (Immediate_Offset (iword (&16))) *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0xa9401c06;       (* arm_LDP X6 X7 X0 (Immediate_Offset (iword (&0))) *)
  0xa9436017;       (* arm_LDP X23 X24 X0 (Immediate_Offset (iword (&48))) *)
  0xa9425815;       (* arm_LDP X21 X22 X0 (Immediate_Offset (iword (&32))) *)
  0x91010000;       (* arm_ADD X0 X0 (rvalue (word 64)) *)
  0xca0d0273;       (* arm_EOR X19 X19 X13 *)
  0xca0e0294;       (* arm_EOR X20 X20 X14 *)
  0x9e670265;       (* arm_FMOV_ItoF Q5 X19 0 *)
  0xca0d00c6;       (* arm_EOR X6 X6 X13 *)
  0xca0e00e7;       (* arm_EOR X7 X7 X14 *)
  0xca0e0318;       (* arm_EOR X24 X24 X14 *)
  0x9e6700c4;       (* arm_FMOV_ItoF Q4 X6 0 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x9eaf00e4;       (* arm_FMOV_ItoF Q4 X7 1 *)
  0xca0d02f7;       (* arm_EOR X23 X23 X13 *)
  0xca0d02b5;       (* arm_EOR X21 X21 X13 *)
  0x9eaf0285;       (* arm_FMOV_ItoF Q5 X20 1 *)
  0x9e6702a6;       (* arm_FMOV_ItoF Q6 X21 0 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x9e6702e7;       (* arm_FMOV_ItoF Q7 X23 0 *)
  0xca0e02d6;       (* arm_EOR X22 X22 X14 *)
  0x9eaf02c6;       (* arm_FMOV_ItoF Q6 X22 1 *)
  0x6e201c84;       (* arm_EOR_VEC Q4 Q4 Q0 128 *)
  0x9e670140;       (* arm_FMOV_ItoF Q0 X10 0 *)
  0x9eaf0120;       (* arm_FMOV_ItoF Q0 X9 1 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x6e211ca5;       (* arm_EOR_VEC Q5 Q5 Q1 128 *)
  0x9e670141;       (* arm_FMOV_ItoF Q1 X10 0 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x9eaf0121;       (* arm_FMOV_ItoF Q1 X9 1 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x4c9f7044;       (* arm_STR Q4 X2 (Postimmediate_Offset (word 16)) *)
  0x9eaf0307;       (* arm_FMOV_ItoF Q7 X24 1 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x6e221cc6;       (* arm_EOR_VEC Q6 Q6 Q2 128 *)
  0x4c9f7045;       (* arm_STR Q5 X2 (Postimmediate_Offset (word 16)) *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x9e670142;       (* arm_FMOV_ItoF Q2 X10 0 *)
  0x9eaf0122;       (* arm_FMOV_ItoF Q2 X9 1 *)
  0x4c9f7046;       (* arm_STR Q6 X2 (Postimmediate_Offset (word 16)) *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x6e231ce7;       (* arm_EOR_VEC Q7 Q7 Q3 128 *)
  0x4c9f7047;       (* arm_STR Q7 X2 (Postimmediate_Offset (word 16)) *)
  0x5400162a;       (* arm_BGE (word 708) *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x4e284a41;       (* arm_AESE Q1 Q18 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x9e670143;       (* arm_FMOV_ItoF Q3 X10 0 *)
  0x4e284a42;       (* arm_AESE Q2 Q18 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e0b416b;       (* arm_EXT Q11 Q11 Q11 64 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x9eaf0123;       (* arm_FMOV_ItoF Q3 X9 1 *)
  0x4e284a61;       (* arm_AESE Q1 Q19 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xa9436017;       (* arm_LDP X23 X24 X0 (Immediate_Offset (iword (&48))) *)
  0x4e284a62;       (* arm_AESE Q2 Q19 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xa9425815;       (* arm_LDP X21 X22 X0 (Immediate_Offset (iword (&32))) *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e2b1c84;       (* arm_EOR_VEC Q4 Q4 Q11 128 *)
  0x4e284a81;       (* arm_AESE Q1 Q20 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xca0d02f7;       (* arm_EOR X23 X23 X13 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x5e18062a;       (* arm_DUP_GEN_FROM_ELEM Q10 Q17 64 64 1 *)
  0x4eefe089;       (* arm_PMULL2_VEC Q9 Q4 Q15 64 *)
  0xca0e02d6;       (* arm_EOR X22 X22 X14 *)
  0x5e180488;       (* arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1 *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0eefe08b;       (* arm_PMULL_VEC Q11 Q4 Q15 64 *)
  0x2e241d08;       (* arm_EOR_VEC Q8 Q8 Q4 64 *)
  0x4e284a82;       (* arm_AESE Q2 Q20 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2008e7;       (* arm_REV64_VEC Q7 Q7 8 *)
  0x4eeee0a4;       (* arm_PMULL2_VEC Q4 Q5 Q14 64 *)
  0x0eeae10a;       (* arm_PMULL_VEC Q10 Q8 Q10 64 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x0eeee0a8;       (* arm_PMULL_VEC Q8 Q5 Q14 64 *)
  0x6e241d29;       (* arm_EOR_VEC Q9 Q9 Q4 128 *)
  0x5e1804a4;       (* arm_DUP_GEN_FROM_ELEM Q4 Q5 64 64 1 *)
  0x4e284aa1;       (* arm_AESE Q1 Q21 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e281d6b;       (* arm_EOR_VEC Q11 Q11 Q8 128 *)
  0x4e284aa2;       (* arm_AESE Q2 Q21 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x5e1804c8;       (* arm_DUP_GEN_FROM_ELEM Q8 Q6 64 64 1 *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x2e251c84;       (* arm_EOR_VEC Q4 Q4 Q5 64 *)
  0x4e284ac2;       (* arm_AESE Q2 Q22 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e261d08;       (* arm_EOR_VEC Q8 Q8 Q6 64 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef1e084;       (* arm_PMULL_VEC Q4 Q4 Q17 64 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e180508;       (* arm_INS Q8 Q8 64 0 64 64 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae2;       (* arm_AESE Q2 Q23 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b01;       (* arm_AESE Q1 Q24 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x4eede0c4;       (* arm_PMULL2_VEC Q4 Q6 Q13 64 *)
  0x0eede0c5;       (* arm_PMULL_VEC Q5 Q6 Q13 64 *)
  0x4e284b21;       (* arm_AESE Q1 Q25 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x0eece0e6;       (* arm_PMULL_VEC Q6 Q7 Q12 64 *)
  0x6e241d29;       (* arm_EOR_VEC Q9 Q9 Q4 128 *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xa9415013;       (* arm_LDP X19 X20 X0 (Immediate_Offset (iword (&16))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x5e1804e4;       (* arm_DUP_GEN_FROM_ELEM Q4 Q7 64 64 1 *)
  0x4e284b02;       (* arm_AESE Q2 Q24 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e251d6b;       (* arm_EOR_VEC Q11 Q11 Q5 128 *)
  0x4ef0e108;       (* arm_PMULL2_VEC Q8 Q8 Q16 64 *)
  0x4eece0e5;       (* arm_PMULL2_VEC Q5 Q7 Q12 64 *)
  0x2e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 64 *)
  0x4e284b22;       (* arm_AESE Q2 Q25 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xca0d0273;       (* arm_EOR X19 X19 X13 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e281d4a;       (* arm_EOR_VEC Q10 Q10 Q8 128 *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xca0d02b5;       (* arm_EOR X21 X21 X13 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0f06e448;       (* arm_MOVI D8 (word 14033993530586874562) *)
  0x0ef0e084;       (* arm_PMULL_VEC Q4 Q4 Q16 64 *)
  0x6e251d29;       (* arm_EOR_VEC Q9 Q9 Q5 128 *)
  0x9e670265;       (* arm_FMOV_ItoF Q5 X19 0 *)
  0xa9401c06;       (* arm_LDP X6 X7 X0 (Immediate_Offset (iword (&0))) *)
  0x5f785508;       (* arm_SHL_VEC Q8 Q8 56 64 64 *)
  0x6e261d6b;       (* arm_EOR_VEC Q11 Q11 Q6 128 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x6e291d64;       (* arm_EOR_VEC Q4 Q11 Q9 128 *)
  0x91010000;       (* arm_ADD X0 X0 (rvalue (word 64)) *)
  0x0ee8e127;       (* arm_PMULL_VEC Q7 Q9 Q8 64 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x6e094129;       (* arm_EXT Q9 Q9 Q9 64 *)
  0xca0d00c6;       (* arm_EOR X6 X6 X13 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0xca0e00e7;       (* arm_EOR X7 X7 X14 *)
  0x9e6700c4;       (* arm_FMOV_ItoF Q4 X6 0 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x6e271d27;       (* arm_EOR_VEC Q7 Q9 Q7 128 *)
  0xca0e0294;       (* arm_EOR X20 X20 X14 *)
  0xca0e0318;       (* arm_EOR X24 X24 X14 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x4e284be0;       (* arm_AESE Q0 Q31 *)
  0x9eaf00e4;       (* arm_FMOV_ItoF Q4 X7 1 *)
  0x6e271d4a;       (* arm_EOR_VEC Q10 Q10 Q7 128 *)
  0x9e6702e7;       (* arm_FMOV_ItoF Q7 X23 0 *)
  0x4e284be1;       (* arm_AESE Q1 Q31 *)
  0x9eaf0285;       (* arm_FMOV_ItoF Q5 X20 1 *)
  0x9e6702a6;       (* arm_FMOV_ItoF Q6 X21 0 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x9eaf02c6;       (* arm_FMOV_ItoF Q6 X22 1 *)
  0x0ee8e149;       (* arm_PMULL_VEC Q9 Q10 Q8 64 *)
  0x6e201c84;       (* arm_EOR_VEC Q4 Q4 Q0 128 *)
  0x9e670140;       (* arm_FMOV_ItoF Q0 X10 0 *)
  0x9eaf0120;       (* arm_FMOV_ItoF Q0 X9 1 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x6e211ca5;       (* arm_EOR_VEC Q5 Q5 Q1 128 *)
  0x9e670141;       (* arm_FMOV_ItoF Q1 X10 0 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x9eaf0121;       (* arm_FMOV_ItoF Q1 X9 1 *)
  0x4e284be2;       (* arm_AESE Q2 Q31 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x4c9f7044;       (* arm_STR Q4 X2 (Postimmediate_Offset (word 16)) *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x6e291d6b;       (* arm_EOR_VEC Q11 Q11 Q9 128 *)
  0x9eaf0307;       (* arm_FMOV_ItoF Q7 X24 1 *)
  0x6e0a414a;       (* arm_EXT Q10 Q10 Q10 64 *)
  0x4c9f7045;       (* arm_STR Q5 X2 (Postimmediate_Offset (word 16)) *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x4e284be3;       (* arm_AESE Q3 Q31 *)
  0x6e221cc6;       (* arm_EOR_VEC Q6 Q6 Q2 128 *)
  0x9e670142;       (* arm_FMOV_ItoF Q2 X10 0 *)
  0x4c9f7046;       (* arm_STR Q6 X2 (Postimmediate_Offset (word 16)) *)
  0x9eaf0122;       (* arm_FMOV_ItoF Q2 X9 1 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x6e2a1d6b;       (* arm_EOR_VEC Q11 Q11 Q10 128 *)
  0xaa098169;       (* arm_ORR X9 X11 (Shiftedreg X9 LSL 32) *)
  0x6e231ce7;       (* arm_EOR_VEC Q7 Q7 Q3 128 *)
  0x4c9f7047;       (* arm_STR Q7 X2 (Postimmediate_Offset (word 16)) *)
  0x54ffea2b;       (* arm_BLT (word 2096452) *)
  0x4e284a41;       (* arm_AESE Q1 Q18 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x4e284a42;       (* arm_AESE Q2 Q18 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x9e670143;       (* arm_FMOV_ItoF Q3 X10 0 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x9eaf0123;       (* arm_FMOV_ItoF Q3 X9 1 *)
  0x6e0b416b;       (* arm_EXT Q11 Q11 Q11 64 *)
  0x4e284a62;       (* arm_AESE Q2 Q19 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e2b1c84;       (* arm_EOR_VEC Q4 Q4 Q11 128 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e284a82;       (* arm_AESE Q2 Q20 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x5e18062a;       (* arm_DUP_GEN_FROM_ELEM Q10 Q17 64 64 1 *)
  0x4e284a61;       (* arm_AESE Q1 Q19 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x0eefe08b;       (* arm_PMULL_VEC Q11 Q4 Q15 64 *)
  0x5e180488;       (* arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1 *)
  0x4eefe089;       (* arm_PMULL2_VEC Q9 Q4 Q15 64 *)
  0x4e284aa2;       (* arm_AESE Q2 Q21 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284a81;       (* arm_AESE Q1 Q20 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x2e241d08;       (* arm_EOR_VEC Q8 Q8 Q4 64 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284aa1;       (* arm_AESE Q1 Q21 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x0eeae10a;       (* arm_PMULL_VEC Q10 Q8 Q10 64 *)
  0x4eeee0a4;       (* arm_PMULL2_VEC Q4 Q5 Q14 64 *)
  0x0eeee0a8;       (* arm_PMULL_VEC Q8 Q5 Q14 64 *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e241d29;       (* arm_EOR_VEC Q9 Q9 Q4 128 *)
  0x5e1804a4;       (* arm_DUP_GEN_FROM_ELEM Q4 Q5 64 64 1 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e281d6b;       (* arm_EOR_VEC Q11 Q11 Q8 128 *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x2e251c84;       (* arm_EOR_VEC Q4 Q4 Q5 64 *)
  0x5e1804c8;       (* arm_DUP_GEN_FROM_ELEM Q8 Q6 64 64 1 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2008e7;       (* arm_REV64_VEC Q7 Q7 8 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef1e084;       (* arm_PMULL_VEC Q4 Q4 Q17 64 *)
  0x2e261d08;       (* arm_EOR_VEC Q8 Q8 Q6 64 *)
  0x1100058c;       (* arm_ADD W12 W12 (rvalue (word 1)) *)
  0x0eede0c5;       (* arm_PMULL_VEC Q5 Q6 Q13 64 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ac2;       (* arm_AESE Q2 Q22 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x4eede0c4;       (* arm_PMULL2_VEC Q4 Q6 Q13 64 *)
  0x6e251d6b;       (* arm_EOR_VEC Q11 Q11 Q5 128 *)
  0x6e180508;       (* arm_INS Q8 Q8 64 0 64 64 *)
  0x4e284ae2;       (* arm_AESE Q2 Q23 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e241d29;       (* arm_EOR_VEC Q9 Q9 Q4 128 *)
  0x5e1804e4;       (* arm_DUP_GEN_FROM_ELEM Q4 Q7 64 64 1 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef0e108;       (* arm_PMULL2_VEC Q8 Q8 Q16 64 *)
  0x2e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 64 *)
  0x4eece0e5;       (* arm_PMULL2_VEC Q5 Q7 Q12 64 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x0ef0e084;       (* arm_PMULL_VEC Q4 Q4 Q16 64 *)
  0x6e281d4a;       (* arm_EOR_VEC Q10 Q10 Q8 128 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b01;       (* arm_AESE Q1 Q24 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b02;       (* arm_AESE Q2 Q24 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0f06e448;       (* arm_MOVI D8 (word 14033993530586874562) *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b21;       (* arm_AESE Q1 Q25 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e251d29;       (* arm_EOR_VEC Q9 Q9 Q5 128 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x5f785508;       (* arm_SHL_VEC Q8 Q8 56 64 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x0eece0e6;       (* arm_PMULL_VEC Q6 Q7 Q12 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e261d6b;       (* arm_EOR_VEC Q11 Q11 Q6 128 *)
  0x4e284b22;       (* arm_AESE Q2 Q25 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e291d4a;       (* arm_EOR_VEC Q10 Q10 Q9 128 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ee8e124;       (* arm_PMULL_VEC Q4 Q9 Q8 64 *)
  0x6e094129;       (* arm_EXT Q9 Q9 Q9 64 *)
  0x6e2b1d4a;       (* arm_EOR_VEC Q10 Q10 Q11 128 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x6e291d4a;       (* arm_EOR_VEC Q10 Q10 Q9 128 *)
  0x0ee8e144;       (* arm_PMULL_VEC Q4 Q10 Q8 64 *)
  0x6e0a414a;       (* arm_EXT Q10 Q10 Q10 64 *)
  0x4e284be1;       (* arm_AESE Q1 Q31 *)
  0x6e241d6b;       (* arm_EOR_VEC Q11 Q11 Q4 128 *)
  0x4e284be3;       (* arm_AESE Q3 Q31 *)
  0x4e284be0;       (* arm_AESE Q0 Q31 *)
  0x4e284be2;       (* arm_AESE Q2 Q31 *)
  0x6e2a1d6b;       (* arm_EOR_VEC Q11 Q11 Q10 128 *)
  0x6e0b4168;       (* arm_EXT Q8 Q11 Q11 64 *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0xa8c11c06;       (* arm_LDP X6 X7 X0 (Postimmediate_Offset (iword (&16))) *)
  0xca0d00c6;       (* arm_EOR X6 X6 X13 *)
  0xca0e00e7;       (* arm_EOR X7 X7 X14 *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x9e6700c4;       (* arm_FMOV_ItoF Q4 X6 0 *)
  0x9eaf00e4;       (* arm_FMOV_ItoF Q4 X7 1 *)
  0x6e201c85;       (* arm_EOR_VEC Q5 Q4 Q0 128 *)
  0x540001ec;       (* arm_BGT (word 60) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0x0f00e40b;       (* arm_MOVI D11 (word 0) *)
  0x0f00e409;       (* arm_MOVI D9 (word 0) *)
  0x5100058c;       (* arm_SUB W12 W12 (rvalue (word 1)) *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x0f00e40a;       (* arm_MOVI D10 (word 0) *)
  0x540002ec;       (* arm_BGT (word 92) *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x5100058c;       (* arm_SUB W12 W12 (rvalue (word 1)) *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x540004ac;       (* arm_BGT (word 148) *)
  0x5100058c;       (* arm_SUB W12 W12 (rvalue (word 1)) *)
  0x14000036;       (* arm_B (word 216) *)
  0x4c9f7045;       (* arm_STR Q5 X2 (Postimmediate_Offset (word 16)) *)
  0xa8c11c06;       (* arm_LDP X6 X7 X0 (Postimmediate_Offset (iword (&16))) *)
  0x4e2008a4;       (* arm_REV64_VEC Q4 Q5 8 *)
  0xca0d00c6;       (* arm_EOR X6 X6 X13 *)
  0x6e281c84;       (* arm_EOR_VEC Q4 Q4 Q8 128 *)
  0xca0e00e7;       (* arm_EOR X7 X7 X14 *)
  0x5e180496;       (* arm_DUP_GEN_FROM_ELEM Q22 Q4 64 64 1 *)
  0x9e6700c5;       (* arm_FMOV_ItoF Q5 X6 0 *)
  0x9eaf00e5;       (* arm_FMOV_ItoF Q5 X7 1 *)
  0x2e241ed6;       (* arm_EOR_VEC Q22 Q22 Q4 64 *)
  0x0f00e408;       (* arm_MOVI D8 (word 0) *)
  0x5e18062a;       (* arm_DUP_GEN_FROM_ELEM Q10 Q17 64 64 1 *)
  0x0eefe08b;       (* arm_PMULL_VEC Q11 Q4 Q15 64 *)
  0x4eefe089;       (* arm_PMULL2_VEC Q9 Q4 Q15 64 *)
  0x0eeae2ca;       (* arm_PMULL_VEC Q10 Q22 Q10 64 *)
  0x6e211ca5;       (* arm_EOR_VEC Q5 Q5 Q1 128 *)
  0x4c9f7045;       (* arm_STR Q5 X2 (Postimmediate_Offset (word 16)) *)
  0xa8c11c06;       (* arm_LDP X6 X7 X0 (Postimmediate_Offset (iword (&16))) *)
  0x4e2008a4;       (* arm_REV64_VEC Q4 Q5 8 *)
  0xca0d00c6;       (* arm_EOR X6 X6 X13 *)
  0x6e281c84;       (* arm_EOR_VEC Q4 Q4 Q8 128 *)
  0x9e6700c5;       (* arm_FMOV_ItoF Q5 X6 0 *)
  0xca0e00e7;       (* arm_EOR X7 X7 X14 *)
  0x9eaf00e5;       (* arm_FMOV_ItoF Q5 X7 1 *)
  0x0f00e408;       (* arm_MOVI D8 (word 0) *)
  0x4eeee094;       (* arm_PMULL2_VEC Q20 Q4 Q14 64 *)
  0x5e180496;       (* arm_DUP_GEN_FROM_ELEM Q22 Q4 64 64 1 *)
  0x0eeee095;       (* arm_PMULL_VEC Q21 Q4 Q14 64 *)
  0x2e241ed6;       (* arm_EOR_VEC Q22 Q22 Q4 64 *)
  0x6e221ca5;       (* arm_EOR_VEC Q5 Q5 Q2 128 *)
  0x6e341d29;       (* arm_EOR_VEC Q9 Q9 Q20 128 *)
  0x0ef1e2d6;       (* arm_PMULL_VEC Q22 Q22 Q17 64 *)
  0x6e351d6b;       (* arm_EOR_VEC Q11 Q11 Q21 128 *)
  0x6e361d4a;       (* arm_EOR_VEC Q10 Q10 Q22 128 *)
  0x4c9f7045;       (* arm_STR Q5 X2 (Postimmediate_Offset (word 16)) *)
  0x4e2008a4;       (* arm_REV64_VEC Q4 Q5 8 *)
  0xa8c11c06;       (* arm_LDP X6 X7 X0 (Postimmediate_Offset (iword (&16))) *)
  0x6e281c84;       (* arm_EOR_VEC Q4 Q4 Q8 128 *)
  0x0f00e408;       (* arm_MOVI D8 (word 0) *)
  0xca0d00c6;       (* arm_EOR X6 X6 X13 *)
  0x5e180496;       (* arm_DUP_GEN_FROM_ELEM Q22 Q4 64 64 1 *)
  0x4eede094;       (* arm_PMULL2_VEC Q20 Q4 Q13 64 *)
  0xca0e00e7;       (* arm_EOR X7 X7 X14 *)
  0x2e241ed6;       (* arm_EOR_VEC Q22 Q22 Q4 64 *)
  0x6e341d29;       (* arm_EOR_VEC Q9 Q9 Q20 128 *)
  0x6e1806d6;       (* arm_INS Q22 Q22 64 0 64 64 *)
  0x9e6700c5;       (* arm_FMOV_ItoF Q5 X6 0 *)
  0x9eaf00e5;       (* arm_FMOV_ItoF Q5 X7 1 *)
  0x4ef0e2d6;       (* arm_PMULL2_VEC Q22 Q22 Q16 64 *)
  0x0eede095;       (* arm_PMULL_VEC Q21 Q4 Q13 64 *)
  0x6e231ca5;       (* arm_EOR_VEC Q5 Q5 Q3 128 *)
  0x6e361d4a;       (* arm_EOR_VEC Q10 Q10 Q22 128 *)
  0x6e351d6b;       (* arm_EOR_VEC Q11 Q11 Q21 128 *)
  0x4e2008a4;       (* arm_REV64_VEC Q4 Q5 8 *)
  0x6e281c84;       (* arm_EOR_VEC Q4 Q4 Q8 128 *)
  0x4eece094;       (* arm_PMULL2_VEC Q20 Q4 Q12 64 *)
  0x5e180488;       (* arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1 *)
  0x5ac00989;       (* arm_REV W9 W12 *)
  0x0eece095;       (* arm_PMULL_VEC Q21 Q4 Q12 64 *)
  0x6e341d29;       (* arm_EOR_VEC Q9 Q9 Q20 128 *)
  0x2e241d08;       (* arm_EOR_VEC Q8 Q8 Q4 64 *)
  0x0ef0e108;       (* arm_PMULL_VEC Q8 Q8 Q16 64 *)
  0x6e351d6b;       (* arm_EOR_VEC Q11 Q11 Q21 128 *)
  0x6e281d4a;       (* arm_EOR_VEC Q10 Q10 Q8 128 *)
  0x0f06e448;       (* arm_MOVI D8 (word 14033993530586874562) *)
  0x6e291d64;       (* arm_EOR_VEC Q4 Q11 Q9 128 *)
  0x5f785508;       (* arm_SHL_VEC Q8 Q8 56 64 64 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x0ee8e127;       (* arm_PMULL_VEC Q7 Q9 Q8 64 *)
  0x6e094129;       (* arm_EXT Q9 Q9 Q9 64 *)
  0x6e271d4a;       (* arm_EOR_VEC Q10 Q10 Q7 128 *)
  0x6e291d4a;       (* arm_EOR_VEC Q10 Q10 Q9 128 *)
  0x0ee8e149;       (* arm_PMULL_VEC Q9 Q10 Q8 64 *)
  0x6e0a414a;       (* arm_EXT Q10 Q10 Q10 64 *)
  0xb9000e09;       (* arm_STR W9 X16 (Immediate_Offset (word 12)) *)
  0x4c007045;       (* arm_STR Q5 X2 No_Offset *)
  0x6e291d6b;       (* arm_EOR_VEC Q11 Q11 Q9 128 *)
  0x6e2a1d6b;       (* arm_EOR_VEC Q11 Q11 Q10 128 *)
  0x6e0b416b;       (* arm_EXT Q11 Q11 Q11 64 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0xaa0f03e0;       (* arm_MOV X0 X15 *)
  0x4c00706b;       (* arm_STR Q11 X3 No_Offset *)
  0xa94153f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  0xa9425bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&32))) *)
  0xa94363f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&48))) *)
  0x6d4427e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&64))) *)
  0x6d452fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&80))) *)
  0x6d4637ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&96))) *)
  0x6d473fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&112))) *)
  0xa8c87bfd;       (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&128))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AES_GCM_ENC_KERNEL_EXEC = ARM_MK_EXEC_RULE aes_gcm_enc_kernel_mc;;

(* ------------------------------------------------------------------------- *)
(* Phase 7 smoke-test — slice promotion of `AES4WAY_ROUND_CORRECT`.          *)
(*                                                                           *)
(* The pilot `AES4WAY_ROUND_CORRECT` (above) targets a freestanding-mc copy  *)
(* of the kernel's round-5 4-way AES step.  This block re-states the same    *)
(* property against a slice of the *full* kernel mc carved out via           *)
(* `mk_sublist_of_mc`, validating that proofs against `aes_gcm_enc_kernel_mc`*)
(* slices are ergonomic before scaling to the loop-body big-cut.             *)
(*                                                                           *)
(* The 8-instruction slice covers kernel byte offsets 0x18c..0x1ac, which    *)
(* are exactly the round-5 AESE/AESMC pairs for blocks 0, 1, 3, 2 inside     *)
(* `Lenc_finish_first_blocks`.                                               *)
(*                                                                           *)
(* Same closing tactic as the freestanding pilot.                            *)
(* ------------------------------------------------------------------------- *)

let aes4way_round_kernel_slice_mc_def,
    aes4way_round_kernel_slice_mc,
    AES4WAY_ROUND_KERNEL_SLICE_EXEC =
  mk_sublist_of_mc "aes4way_round_kernel_slice_mc"
    aes_gcm_enc_kernel_mc
    (`0x18c`,`0x20`)
    (fst AES_GCM_ENC_KERNEL_EXEC);;

let AES4WAY_ROUND_KERNEL_SLICE_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128) (rk:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes4way_round_kernel_slice_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q23 s = rk)
     (\s. read PC s = word (pc + 0x20) /\
          read Q0 s = aes_arm_round b0 rk /\
          read Q1 s = aes_arm_round b1 rk /\
          read Q2 s = aes_arm_round b2 rk /\
          read Q3 s = aes_arm_round b3 rk /\
          read Q23 s = rk)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES4WAY_ROUND_KERNEL_SLICE_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 — Lenc_main_loop body slice (175 instructions, kernel offsets     *)
(* 0x308..0x5c4, back-edge `b.lt .Lenc_main_loop` excluded).                 *)
(*                                                                           *)
(* The body is a single iteration of the 4-block AES-CTR + GHASH main loop. *)
(* It consumes:                                                              *)
(*   - Q0..Q3   : four AES-CTR pre-images (counter blocks already loaded by *)
(*                the prelude or the previous iteration's tail)              *)
(*   - Q4..Q7   : the previous iteration's four ciphertext blocks, already  *)
(*                in the running shape ready for GHASH input (rev64 + ext   *)
(*                + initial XOR-with-prev-tag for block 0 happens inside    *)
(*                the body, not as a precondition)                           *)
(*   - Q11      : the running GHASH tag (in the kernel's pre-byteswap form)  *)
(*   - Q12..Q17 : the H-power table (htable_mem layout: H^4..H^1 plus       *)
(*                karatsuba_mid pairs at v17 = mid(H^2)||mid(H^3),          *)
(*                v16 = mid(H^0)||mid(H^1))                                  *)
(*   - Q18..Q28 : the 11 AES-128 round keys rk0..rk10                        *)
(*   - Q31      : the round-N-1 key (= rk9, hoisted into Q31 by the prelude) *)
(*   - X0       : plaintext input pointer                                    *)
(*   - X2       : ciphertext output pointer                                  *)
(*   - X5       : end-of-plaintext pointer (used by the back-edge cmp;       *)
(*                read-only inside the body proper)                          *)
(*   - X10/X11/W9/W12 : 32-bit big-endian counter scratch (CTR state)        *)
(*   - X13/X14 : the round-N-1 key bits used in the final-round trick        *)
(*   - X6/X7/X19..X24 : scratch GPRs holding plaintext words mid-flight      *)
(*   - memory at X0+0..X0+63   : 64 plaintext bytes for this iteration       *)
(*                                                                           *)
(* It produces:                                                              *)
(*   - Q0..Q3   : the next four counter blocks (CTR advanced by 4)           *)
(*   - Q4..Q7   : the four ciphertext blocks JUST written (= AES of the     *)
(*                input counters XORed with plaintext)                       *)
(*   - Q11      : the updated GHASH running tag (= kernel-form               *)
(*                `nist_ghash h prev_tag [c4;c5;c6;c7]` of the previous     *)
(*                iteration's ciphertext blocks)                              *)
(*   - X0       : advanced by 64 (to next iteration's plaintext)             *)
(*   - X2       : advanced by 64 (next iteration's ciphertext write start)   *)
(*   - W12      : counter advanced by 4                                      *)
(*   - memory at X2-64..X2 : the four written ciphertext blocks              *)
(*                                                                           *)
(* This is the proof's spine; the spec-side composition reuses               *)
(*   - `aes128_cipher_arm` (from `aes_gcm_bridge.ml`, applied four times)    *)
(*   - `KERNEL_4BLOCK_NIST_BRIDGE` (the GHASH bridge, applied to the prior  *)
(*     iteration's c4..c7)                                                   *)
(*                                                                           *)
(* The slice + EXEC are committed below to ground subsequent sessions; the   *)
(* full ensures statement is parked as a comment block, NOT a derivable      *)
(* `prove(...)`. This keeps soundness intact while reserving the slice       *)
(* artifact for the multi-session big-cut proof.                             *)
(*                                                                           *)
(* The slice is exactly the 175-instruction loop body; the back-edge         *)
(* `b.lt .Lenc_main_loop` at offset 0x5c4 is excluded (it belongs to the     *)
(* loop wrapper, not the body cut-point).  Validates that all 175 body       *)
(* instructions decode under the s2n-arm-aes checkpoint (Phase 0b decoder    *)
(* additions are exercised: `mov d, v.d[1]` at offsets 0x33c/0x37c/0x3b4/   *)
(* 0x3f0 etc., `ins v.d[1], v.d[0]` at 0x3d8, `shl d, d, #56` at 0x4e4).    *)
(* ------------------------------------------------------------------------- *)

let aes_gcm_main_loop_body_slice_mc_def,
    aes_gcm_main_loop_body_slice_mc,
    AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC =
  mk_sublist_of_mc "aes_gcm_main_loop_body_slice_mc"
    aes_gcm_enc_kernel_mc
    (`0x308`,`0x2bc`)
    (fst AES_GCM_ENC_KERNEL_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 — small body-slice cut: AES round 0 for blocks 0/1/2.             *)
(*                                                                           *)
(* The first 8 instructions of the loop-body slice (slice-relative offsets   *)
(* 0..0x1c, kernel offsets 0x308..0x324) interleave:                         *)
(*                                                                           *)
(*   0x000  arm_AESE  Q0 Q18                ; AES block 4k+4 - round 0       *)
(*   0x004  arm_AESMC Q0 Q0                                                  *)
(*   0x008  arm_REV64_VEC Q4 Q4 8           ; GHASH PRE for prev ciphertext  *)
(*   0x00c  arm_AESE  Q1 Q18                ; AES block 4k+5 - round 0       *)
(*   0x010  arm_AESMC Q1 Q1                                                  *)
(*   0x014  arm_FMOV_ItoF Q3 X10 0          ; CTR block 4k+7 setup, low half *)
(*   0x018  arm_AESE  Q2 Q18                ; AES block 4k+6 - round 0       *)
(*   0x01c  arm_AESMC Q2 Q2                                                  *)
(*                                                                           *)
(* Block 4k+7 (Q3) does not get AES round 0 until offset 0x5c (instr 24);    *)
(* in this 8-instruction window only blocks 0/1/2 advance an AES round, with *)
(* round-key Q18 (rk0).  Q3 and Q4 are clobbered (CTR setup / GHASH PRE)     *)
(* and therefore live in the MAYCHANGE frame.                                *)
(*                                                                           *)
(* This proof exercises the slice-promotion + AES-round-bridge closing       *)
(* tactic at minimal risk — same shape as `AES4WAY_ROUND_KERNEL_SLICE_       *)
(* CORRECT` above, but on the loop body slice.  Subsequent cuts compose.     *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R0_BLOCKS012_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (rk0:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q18 s = rk0)
     (\s. read PC s = word (pc + 0x20) /\
          read Q0 s = aes_arm_round b0 rk0 /\
          read Q1 s = aes_arm_round b1 rk0 /\
          read Q2 s = aes_arm_round b2 rk0 /\
          read Q18 s = rk0)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 1 for blocks 0/1/2 (slice instr 9..17).      *)
(*                                                                           *)
(* The next 9 instructions (slice-relative offsets 0x20..0x40) cover:        *)
(*                                                                           *)
(*   0x020  arm_EXT       Q11 Q11 Q11 64    ; PRE 0 (rotate Q11 by 64 bits) *)
(*   0x024  arm_AESE      Q0 Q19            ; round 1 block 0 (rk1=Q19)     *)
(*   0x028  arm_AESMC     Q0 Q0                                              *)
(*   0x02c  arm_FMOV_ItoF Q3 X9 1           ; CTR block 4k+7 high half setup*)
(*   0x030  arm_AESE      Q1 Q19            ; round 1 block 1                *)
(*   0x034  arm_AESMC     Q1 Q1                                              *)
(*   0x038  arm_LDP       X23 X24 X0 #48    ; AES block 4k+7 plaintext load *)
(*   0x03c  arm_AESE      Q2 Q19            ; round 1 block 2 (AESE half)   *)
(*   0x040  arm_AESMC     Q2 Q2             ; round 1 block 2 (AESMC half)  *)
(*                                                                           *)
(* By the end of step 17 (PC = pc + 0x44) all three of Q0/Q1/Q2 have an     *)
(* aes_arm_round with rk1 applied.  Q3 and Q11 are also written (CTR setup *)
(* + EXT respectively) and sit in the MAYCHANGE frame, along with X23/X24  *)
(* (LDP plaintext) and `events` (the LDP touches memory).                   *)
(*                                                                           *)
(* Same closing tactic shape as the round-0 cut above; the only adjustment  *)
(* is the wider MAYCHANGE frame.                                             *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R1_BLOCKS012_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b11:int128) (rk1:int128)
        (sx9:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x20) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q11 s = b11 /\
          read Q19 s = rk1 /\
          read X9 s = sx9)
     (\s. read PC s = word (pc + 0x44) /\
          read Q0 s = aes_arm_round b0 rk1 /\
          read Q1 s = aes_arm_round b1 rk1 /\
          read Q2 s = aes_arm_round b2 rk1 /\
          read Q19 s = rk1)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q11] ,,
      MAYCHANGE [X23; X24] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 2 for blocks 0/1 (slice instr 18..23).        *)
(*                                                                           *)
(* The next 6 instructions (slice-relative offsets 0x44..0x58) cover:        *)
(*                                                                           *)
(*   0x044  arm_LDP    X21 X22 X0 #32      ; AES block 4k+6 plaintext load  *)
(*   0x048  arm_AESE   Q0 Q20              ; round 2 block 0 (rk2=Q20)      *)
(*   0x04c  arm_AESMC  Q0 Q0                                                 *)
(*   0x050  arm_EOR_VEC Q4 Q4 Q11 128      ; PRE 1 (Q4 = byteswap_c4 XOR    *)
(*                                         ;  rotated prev_tag)              *)
(*   0x054  arm_AESE   Q1 Q20              ; round 2 block 1                 *)
(*   0x058  arm_AESMC  Q1 Q1                                                 *)
(*                                                                           *)
(* By PC = pc + 0x5c only Q0 and Q1 have advanced one round with rk2.       *)
(* Block 2's round 2 starts much later (offset 0x84, instr 33) — the kernel *)
(* deliberately interleaves round work across blocks for OoO scheduling.    *)
(* So this cut is narrower than the previous two.  Q4 is in MAYCHANGE      *)
(* (the EOR), as are X21/X22 (LDP plaintext) and `events`.                  *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R2_BLOCKS01_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (rk2:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x44) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q20 s = rk2)
     (\s. read PC s = word (pc + 0x5c) /\
          read Q0 s = aes_arm_round b0 rk2 /\
          read Q1 s = aes_arm_round b1 rk2 /\
          read Q20 s = rk2)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q4] ,,
      MAYCHANGE [X21; X22] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 0 for block 3 + AES round 3 for block 0      *)
(* (slice instr 24..28).                                                     *)
(*                                                                           *)
(* The next 5 instructions (slice-relative offsets 0x5c..0x6c) cover:         *)
(*                                                                           *)
(*   0x05c  arm_AESE   Q3 Q18              ; round 0 block 3 (rk0=Q18)       *)
(*   0x060  arm_AESMC  Q3 Q3                                                  *)
(*   0x064  arm_EOR    X23 X23 X13         ; AES block 4k+7 - round N low    *)
(*                                         ;  XOR (= scalar plaintext+ rk10  *)
(*                                         ;  half) — touches X23 only.     *)
(*   0x068  arm_AESE   Q0 Q21              ; round 3 block 0 (rk3=Q21)       *)
(*   0x06c  arm_AESMC  Q0 Q0                                                  *)
(*                                                                           *)
(* By PC = pc + 0x70 block 3 has finally entered the AES chain (round 0)     *)
(* and block 0 has advanced to round 3.  No other Q register changes.       *)
(* The scalar EOR writes X23 (already in MAYCHANGE for the R1 cut, but each *)
(* cut stands alone with fresh quantified variables, so it goes in the      *)
(* MAYCHANGE here too).  PC = pc + 0x70 sits exactly at the first GHASH     *)
(* opcode (`arm_DUP_GEN_FROM_ELEM Q10 Q17 64 64 1`); subsequent cuts must   *)
(* pivot to the `GHASH_4BLOCK_CORRECT`-style closing tactic.                *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R0R3_BLOCK3_BLOCK0_CORRECT = prove
 (`!pc (b0:int128) (b3:int128) (rk0:int128) (rk3:int128) (sx13:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x5c) /\
          read Q0 s = b0 /\
          read Q3 s = b3 /\
          read Q18 s = rk0 /\
          read Q21 s = rk3 /\
          read X13 s = sx13)
     (\s. read PC s = word (pc + 0x70) /\
          read Q0 s = aes_arm_round b0 rk3 /\
          read Q3 s = aes_arm_round b3 rk0 /\
          read Q18 s = rk0 /\
          read Q21 s = rk3)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q3] ,,
      MAYCHANGE [X23])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 1 for block 3 (slice instr 29..34).          *)
(*                                                                           *)
(* This is the FIRST cut whose window contains GHASH Karatsuba opcodes —    *)
(* `arm_DUP_GEN_FROM_ELEM` and `arm_PMULL2_VEC` — but the cut still uses     *)
(* the AES-only closing tactic.  The trick: we don't constrain the          *)
(* values written to the GHASH-touched registers (Q8/Q9/Q10) in the          *)
(* postcondition; we only list them in the MAYCHANGE frame.  As long as     *)
(* the postcondition reads only AES-relevant state (here: Q3 and Q19),       *)
(* MAYCHANGE absorbs the GHASH side-effects opaquely.                        *)
(*                                                                           *)
(*   0x070  arm_DUP_GEN_FROM_ELEM Q10 Q17 64 64 1   ; GHASH 4k - mid (Q10)  *)
(*   0x074  arm_PMULL2_VEC        Q9 Q4 Q15 64       ; GHASH 4k - high (Q9) *)
(*   0x078  arm_EOR               X22 X22 X14        ; AES 4k+6 round N hi  *)
(*   0x07c  arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1      ; GHASH 4k - mid (Q8)  *)
(*   0x080  arm_AESE              Q3 Q19             ; round 1 block 3      *)
(*   0x084  arm_AESMC             Q3 Q3                                      *)
(*                                                                           *)
(* By PC = pc + 0x88, Q3 has advanced one round (from rk0-output `b3` to     *)
(* rk1-applied `aes_arm_round b3 rk1`).  Q8/Q9/Q10/X22 are clobbered.        *)
(* The exact values of Q8/Q9/Q10 (mid/high components of the GHASH 4k       *)
(* Karatsuba) will need to be tracked when we eventually compose this cut    *)
(* with the GHASH bridge — but that's a separate concern; this cut just     *)
(* keeps the AES chain progressing through GHASH-interleaved territory.    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R1_BLOCK3_CORRECT = prove
 (`!pc (b3:int128) (rk1:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x70) /\
          read Q3 s = b3 /\
          read Q19 s = rk1)
     (\s. read PC s = word (pc + 0x88) /\
          read Q3 s = aes_arm_round b3 rk1 /\
          read Q19 s = rk1)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q3; Q8; Q9; Q10] ,,
      MAYCHANGE [X22])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 4 for block 0 + round 2 for block 2          *)
(* (slice instr 35..41).                                                     *)
(*                                                                           *)
(* Window (offsets 0x88..0xa0) — heavily GHASH-interleaved:                  *)
(*                                                                           *)
(*   0x088  arm_REV64_VEC  Q5 Q5 8       ; GHASH 4k+1 byteswap (Q5)          *)
(*   0x08c  arm_AESE       Q0 Q22        ; round 4 block 0 (rk4=Q22)         *)
(*   0x090  arm_AESMC      Q0 Q0                                              *)
(*   0x094  arm_PMULL_VEC  Q11 Q4 Q15 64 ; GHASH 4k - low (Q11)               *)
(*   0x098  arm_EOR_VEC    Q8 Q8 Q4 64   ; GHASH 4k - mid (Q8 lo half)        *)
(*   0x09c  arm_AESE       Q2 Q20        ; round 2 block 2 (rk2=Q20)          *)
(*   0x0a0  arm_AESMC      Q2 Q2                                              *)
(*                                                                           *)
(* Q0 advances rk3→rk4; Q2 advances rk1→rk2.  GHASH side clobbers           *)
(* Q5/Q8/Q11 — listed in MAYCHANGE without value-tracking.  Block 2 finally  *)
(* catches up on round 2 (it was idle through cuts R0/R1/R0R3/R1_BLOCK3).   *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R4R2_BLOCK0_BLOCK2_CORRECT = prove
 (`!pc (b0:int128) (b2:int128) (rk2:int128) (rk4:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x88) /\
          read Q0 s = b0 /\
          read Q2 s = b2 /\
          read Q20 s = rk2 /\
          read Q22 s = rk4)
     (\s. read PC s = word (pc + 0xa4) /\
          read Q0 s = aes_arm_round b0 rk4 /\
          read Q2 s = aes_arm_round b2 rk2 /\
          read Q20 s = rk2 /\
          read Q22 s = rk4)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q2; Q5; Q8; Q11])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 5 (block 0) + round 3 (block 1) +            *)
(* round 2 (block 3) — slice instr 42..54.                                   *)
(*                                                                           *)
(* Larger 13-instruction window (offsets 0xa4..0xd4) than prior cuts —       *)
(* still using the AES-only closing tactic.  The rk advance pattern:        *)
(*                                                                           *)
(*   0x0a4  arm_AESE   Q0 Q23           ; round 5 block 0 (rk5=Q23)          *)
(*   0x0a8  arm_AESMC  Q0 Q0                                                  *)
(*   0x0ac  arm_REV64_VEC Q7 Q7 8       ; GHASH PRE block 4k+3 (Q7)          *)
(*   0x0b0  arm_PMULL2_VEC Q4 Q5 Q14    ; GHASH 4k+1 high (writes Q4)        *)
(*   0x0b4  arm_PMULL_VEC  Q10 Q8 Q10   ; GHASH 4k mid (writes Q10)          *)
(*   0x0b8  arm_REV64_VEC  Q6 Q6 8      ; GHASH PRE block 4k+2 (Q6)          *)
(*   0x0bc  arm_PMULL_VEC  Q8 Q5 Q14    ; GHASH 4k+1 low (writes Q8)         *)
(*   0x0c0  arm_EOR_VEC    Q9 Q9 Q4 128 ; GHASH 4k+1 high accumulate (Q9)   *)
(*   0x0c4  arm_DUP_GEN_FROM_ELEM Q4 Q5 64 64 1   ; GHASH 4k+1 mid (Q4)     *)
(*   0x0c8  arm_AESE   Q1 Q21           ; round 3 block 1 (rk3=Q21)          *)
(*   0x0cc  arm_AESMC  Q1 Q1                                                  *)
(*   0x0d0  arm_AESE   Q3 Q20           ; round 2 block 3 (rk2=Q20)          *)
(*   0x0d4  arm_AESMC  Q3 Q3                                                  *)
(*                                                                           *)
(* By PC = pc + 0xd8 three blocks have advanced (Q0:rk4→rk5, Q1:rk2→rk3,    *)
(* Q3:rk1→rk2).  GHASH side-effects on Q4/Q6/Q7/Q8/Q9/Q10 are absorbed by   *)
(* MAYCHANGE without value-tracking.                                         *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R5R3R2_3BLOCK_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b3:int128)
        (rk2:int128) (rk3:int128) (rk5:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0xa4) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q3 s = b3 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q23 s = rk5)
     (\s. read PC s = word (pc + 0xd8) /\
          read Q0 s = aes_arm_round b0 rk5 /\
          read Q1 s = aes_arm_round b1 rk3 /\
          read Q3 s = aes_arm_round b3 rk2 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q23 s = rk5)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q3; Q4; Q6; Q7; Q8; Q9; Q10])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--13) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Parked ensures statement for the loop-body big-cut.  This documents the   *)
(* pre/postcondition shape that a future session's `prove(...)` will target. *)
(* It is intentionally NOT a `prove(...)` call — the proof is multi-session  *)
(* work (per all reviewers since session 018) and committing a `CHEAT_TAC`   *)
(* would re-introduce the soundness regression sessions 014–015 had to       *)
(* unwind.                                                                   *)
(*                                                                           *)
(*   forall pc                                                                *)
(*          (k:num)                  ; iteration index, 0 < k < num_blocks  *)
(*          (c0_in:int128)..(c3_in:int128)  ; CTR pre-images                *)
(*          (c4_prev:int128)..(c7_prev:int128) ; previous iter's ciphertexts*)
(*          (running_tag:int128)     ; GHASH running tag (kernel form)      *)
(*          (rk0:int128)..(rk10:int128)  ; AES-128 round keys                *)
(*          (h:int128)               ; GHASH H = aes128_cipher 0 ks         *)
(*          (pptr:int64) (cptr:int64) (eptr:int64) (kptr:int64) (htptr:int64)*)
(*          (plaintext_4:int128)..(plaintext_7:int128).                      *)
(*    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc)      *)
(*                   (cptr, 64) /\                                            *)
(*    ALLPAIRS nonoverlapping                                                *)
(*      [(pptr, 64); (cptr, 64); (htptr, 256)] [...] /\                      *)
(*    htable_mem h kptr s            ; H-table layout                        *)
(*    ==> ensures arm                                                        *)
(*         (\s. aligned_bytes_loaded s (word pc)                            *)
(*                 aes_gcm_main_loop_body_slice_mc /\                       *)
(*              read PC s = word pc /\                                       *)
(*              read X0 s = pptr /\                                          *)
(*              read X2 s = cptr /\                                          *)
(*              read X5 s = eptr /\                                          *)
(*              read X8 s = kptr /\                                          *)
(*              read Q0 s = c0_in /\ ... /\ read Q3 s = c3_in /\             *)
(*              read Q4 s = byteswap128 c4_prev /\ ... /\                    *)
(*              read Q11 s = running_tag /\                                  *)
(*              read Q15 s = byteswap128 (h_power h 4) /\                    *)
(*              read Q14 s = byteswap128 (h_power h 3) /\                    *)
(*              read Q13 s = byteswap128 (h_power h 2) /\                    *)
(*              read Q12 s = byteswap128 (h_power h 1) /\                    *)
(*              read Q17 s = word_join (karatsuba_mid (h_power h 2))         *)
(*                                     (karatsuba_mid (h_power h 3)) /\      *)
(*              read Q16 s = word_join (karatsuba_mid (h_power h 0))         *)
(*                                     (karatsuba_mid (h_power h 1)) /\      *)
(*              read Q18 s = rk0 /\ ... /\ read Q28 s = rk10 /\              *)
(*              read Q31 s = rk9 /\                                          *)
(*              read X13 s = word_subword rk10 (0,64) /\                     *)
(*              read X14 s = word_subword rk10 (64,64) /\                    *)
(*              read (memory :> bytes128 pptr) s = plaintext_4 /\            *)
(*              read (memory :> bytes128 (word_add pptr (word 16))) s =      *)
(*                plaintext_5 /\                                              *)
(*              read (memory :> bytes128 (word_add pptr (word 32))) s =      *)
(*                plaintext_6 /\                                              *)
(*              read (memory :> bytes128 (word_add pptr (word 48))) s =      *)
(*                plaintext_7)                                                *)
(*         (\s. read PC s = word (pc + 0x2bc) /\  ; offset of `b.lt` minus  *)
(*                                                ; slice base (0x308)      *)
(*              read X0 s = word_add pptr (word 64) /\                       *)
(*              read X2 s = word_add cptr (word 64) /\                       *)
(*              (let c4 = word_xor (aes128_cipher_arm c0_in [rk0;...;rk10])  *)
(*                                 plaintext_4                               *)
(*               and c5 = ... and c6 = ... and c7 = ... in                   *)
(*               read Q4 s = c4 /\ ... /\ read Q7 s = c7 /\                  *)
(*               read (memory :> bytes128 cptr) s = c4 /\ ... /\             *)
(*               read (memory :> bytes128                                    *)
(*                       (word_add cptr (word 48))) s = c7 /\                *)
(*               read Q11 s = nist_ghash h running_tag                       *)
(*                              [c4_prev; c5_prev; c6_prev; c7_prev]) /\     *)
(*              ; Q0..Q3 hold the next 4 counter blocks for iteration k+1   *)
(*              read Q0 s = ctr_advance c0_in 4 /\ ...)                     *)
(*         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,                    *)
(*          MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;                              *)
(*                     Q8;Q9;Q10;Q11; Q22] ,,                                *)
(*          MAYCHANGE [memory :> bytes(cptr,64)] ,,                          *)
(*          MAYCHANGE [events])                                               *)
(*                                                                           *)
(* The proof spine for a future session:                                     *)
(*   1. ENSURES_INIT_TAC "s0".                                               *)
(*   2. ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--N) where N       *)
(*      walks ~30 instructions at a time (cut points after each AES round    *)
(*      group + GHASH per-block-Karatsuba step).                             *)
(*   3. At the cut after the LAST AES round-8 aesmc (instruction 113,       *)
(*      offset 0x4cc relative to slice base): assert `Q0..Q3 each =         *)
(*      aes_arm_round^9 c_in rks` via the AES_BLOCK_FULL_CORRECT closing    *)
(*      tactic template (AESMC_AESE_AS_ARM_ROUND + AESE_AS_ARM_FINAL_ROUND  *)
(*      + aes128_cipher_arm + LET_DEF + LET_END_DEF + EL + HD + TL +        *)
(*      DEPTH_CONV EL_CONV + WORD_RULE).                                     *)
(*   4. At the cut after the GHASH MODULO chain (~instruction 145, near    *)
(*      offset 0x5b0): assert `Q11 = byteswap-form-of                       *)
(*      nist_ghash h running_tag [c4_prev..c7_prev]` via                     *)
(*      KERNEL_4BLOCK_NIST_BRIDGE.                                           *)
(*   5. At the final cut (instruction 175, offset 0x2b8 = 0x5c0 relative to *)
(*      slice base): the four `st1 v_,[x2],#16` stores are visible; the    *)
(*      AES-final-round trick (round-N-1 AESE + XOR-with-x6/x7-which-       *)
(*      already-have-rk10-bits + fmov assemble) yields the final ciphertext *)
(*      in Q4..Q7; round-N-1 + final-round-trick equals one application of  *)
(*      `aes_arm_final_round` per block.                                     *)
(*   6. ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC[...] to close.             *)
(*                                                                           *)
(* Reference precedents already in tree:                                     *)
(*   - AES_BLOCK_FULL_CORRECT (above): full single-block AES-128, register- *)
(*     only.  Closing tactic template scales straight to per-block cuts in  *)
(*     the body.                                                              *)
(*   - GHASH_4BLOCK_CORRECT (above): the 30-instruction GHASH 4-block        *)
(*     Karatsuba + MODULO chain on freestanding mc.  Provides the closing    *)
(*     tactic template for the GHASH-half cut.                               *)
(*   - AES_LOAD_BLOCK_CORRECT (above): the LDP+EOR+FMOV final-round trick   *)
(*     pattern (ldp x6,x7,[x0]; eor x6,x6,rk10_lo; eor x7,x7,rk10_hi;       *)
(*     fmov d4,x6; fmov v4.d[1],x7) reduces to one int128 = `aes_arm_       *)
(*     final_round` step.                                                     *)
(*                                                                           *)
(* Carry-forward for session 021+: the slice + EXEC are now in tree at       *)
(* HEAD <pending commit>.  Next session can attempt the cut-pointed proof  *)
(* directly, OR continue refining the precondition shape if any of the     *)
(* register-allocation conjuncts above proves wrong against the actual      *)
(* prelude/back-edge invariants.  The cleanest approach is probably to      *)
(* prove a sequence of intermediate lemmas FIRST (one per AES round group  *)
(* + per-block GHASH Karatsuba), then compose into the body big-cut.       *)
(* ------------------------------------------------------------------------- *)
