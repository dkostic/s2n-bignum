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
(*   - X13/X14 : scalar copy of round-N (= rk10) low/high 64-bit halves —    *)
(*                used by the kernel's "deferred rk10" final-round trick     *)
(*                (eor x6,x6,x13; eor x7,x7,x14; fmov d4,x6; fmov v4.d[1],x7)*)
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
(* Phase 7 small-cut: round 6 b0 + round 4 b1 + 2-round advance b2 (rk3+rk4) *)
(* + round 3 b3 — slice instr 55..67 (offsets 0xd8..0x108).                 *)
(*                                                                           *)
(* First cut where a single block advances TWO rounds within the window:    *)
(* Q2 sees both `aese ... rk3; aesmc` (instr 56-57) and `aese ... rk4; aesmc`*)
(* (instr 64-65).  Postcondition reflects this with nested aes_arm_round    *)
(* calls.  AESMC_AESE_AS_ARM_ROUND rewrites both layers cleanly.            *)
(*                                                                           *)
(*   0x0d8  arm_EOR_VEC Q11 Q11 Q8 128   ; GHASH 4k+1 low accumulate        *)
(*   0x0dc  arm_AESE   Q2 Q21            ; round 3 block 2                  *)
(*   0x0e0  arm_AESMC  Q2 Q2                                                 *)
(*   0x0e4  arm_AESE   Q1 Q22            ; round 4 block 1                  *)
(*   0x0e8  arm_AESMC  Q1 Q1                                                 *)
(*   0x0ec  arm_DUP_GEN_FROM_ELEM Q8 Q6 64 64 1   ; GHASH 4k+2 mid (Q8)     *)
(*   0x0f0  arm_AESE   Q3 Q21            ; round 3 block 3                  *)
(*   0x0f4  arm_AESMC  Q3 Q3                                                 *)
(*   0x0f8  arm_EOR_VEC Q4 Q4 Q5 64      ; GHASH 4k+1 mid                   *)
(*   0x0fc  arm_AESE   Q2 Q22            ; round 4 block 2                  *)
(*   0x100  arm_AESMC  Q2 Q2                                                 *)
(*   0x104  arm_AESE   Q0 Q24            ; round 6 block 0                  *)
(*   0x108  arm_AESMC  Q0 Q0                                                 *)
(*                                                                           *)
(* Q0:rk5→rk6, Q1:rk3→rk4, Q2:rk2→rk3→rk4, Q3:rk2→rk3.                      *)
(* MAYCHANGE absorbs Q4/Q8/Q11 GHASH side-effects.                           *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R6R4R3_4BLOCK_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128)
        (rk3:int128) (rk4:int128) (rk6:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0xd8) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q24 s = rk6)
     (\s. read PC s = word (pc + 0x10c) /\
          read Q0 s = aes_arm_round b0 rk6 /\
          read Q1 s = aes_arm_round b1 rk4 /\
          read Q2 s = aes_arm_round (aes_arm_round b2 rk3) rk4 /\
          read Q3 s = aes_arm_round b3 rk3 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q24 s = rk6)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q8; Q11])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--13) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: 4-block AES advance through GHASH 4k+1 mid             *)
(* — slice instr 68..84 (offsets 0x10c..0x14c, 17 instructions).             *)
(*                                                                           *)
(* Pattern is the same as previous cuts but with all 4 blocks               *)
(* advancing multiple rounds simultaneously.  Each block's per-round        *)
(* advance is captured in a nested `aes_arm_round (aes_arm_round ...) rkN`. *)
(*                                                                           *)
(*   Q0:  rk6 → rk7 (instr 72-73) → rk8 (instr 79-80)                        *)
(*   Q1:  rk4 → rk5 (instr 77-78) → rk6 (instr 83-84)                        *)
(*   Q2:  rk4 → rk5 (instr 81-82)                                            *)
(*   Q3:  rk3 → rk4 (instr 69-70) → rk5 (instr 74-75)                        *)
(*                                                                           *)
(* Clobbers: Q4 (PMULL), Q8 (EOR_VEC + INS).                                 *)
(* End PC = pc + 0x150 (just before the EOR Q10 Q10 Q4 at offset 0x150).    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_AES_PHASE2_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128)
        (rk4:int128) (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x10c) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (\s. read PC s = word (pc + 0x150) /\
          read Q0 s = aes_arm_round (aes_arm_round b0 rk7) rk8 /\
          read Q1 s = aes_arm_round (aes_arm_round b1 rk5) rk6 /\
          read Q2 s = aes_arm_round b2 rk5 /\
          read Q3 s = aes_arm_round (aes_arm_round b3 rk4) rk5 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q8])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: round 7 b1 + round 6 b3 — slice instr 85..93.          *)
(*                                                                           *)
(* 9-instruction window (offsets 0x150..0x170) covers two AES rounds plus    *)
(* a heavy GHASH block (instr 86-87, 90-91 = 4 GHASH ops):                   *)
(*                                                                           *)
(*   0x150  arm_EOR_VEC      Q10 Q10 Q4 128                                  *)
(*   0x154  arm_PMULL2_VEC   Q4 Q6 Q13 64    ; GHASH 4k+2 high               *)
(*   0x158  arm_PMULL_VEC    Q5 Q6 Q13 64    ; GHASH 4k+2 low                *)
(*   0x15c  arm_AESE         Q1 Q25          ; round 7 block 1 (rk7=Q25)     *)
(*   0x160  arm_AESMC        Q1 Q1                                            *)
(*   0x164  arm_PMULL_VEC    Q6 Q7 Q12 64    ; GHASH 4k+3 low                *)
(*   0x168  arm_EOR_VEC      Q9 Q9 Q4 128    ; GHASH 4k+2 high accumulate   *)
(*   0x16c  arm_AESE         Q3 Q24          ; round 6 block 3 (rk6=Q24)     *)
(*   0x170  arm_AESMC        Q3 Q3                                            *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R7R6_BLOCK1_BLOCK3_CORRECT = prove
 (`!pc (b1:int128) (b3:int128) (rk6:int128) (rk7:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x150) /\
          read Q1 s = b1 /\
          read Q3 s = b3 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7)
     (\s. read PC s = word (pc + 0x174) /\
          read Q1 s = aes_arm_round b1 rk7 /\
          read Q3 s = aes_arm_round b3 rk6 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q1; Q3; Q4; Q5; Q6; Q9; Q10])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: round 8 b1 + 2-round advance b2 (rk6+rk7) including    *)
(* an LDP plaintext load — slice instr 94..105.                              *)
(*                                                                           *)
(* 12-instruction window (offsets 0x174..0x1a0).  First cut to include a    *)
(* memory-load instruction (LDP X19 X20 X0 #16 — AES block 4k+5 plaintext) *)
(* in addition to the AES + GHASH body.  X19/X20 + `events` join MAYCHANGE.*)
(*                                                                           *)
(*   0x174  arm_LDP X19 X20 X0 #16   ; AES block 4k+5 plaintext load        *)
(*   0x178  arm_AESE Q1 Q26          ; round 8 block 1 (rk8=Q26)            *)
(*   0x17c  arm_AESMC Q1 Q1                                                  *)
(*   0x180  arm_DUP_GEN_FROM_ELEM Q4 Q7 64 64 1   ; GHASH 4k+3 mid          *)
(*   0x184  arm_AESE Q2 Q24          ; round 6 block 2                      *)
(*   0x188  arm_AESMC Q2 Q2                                                  *)
(*   0x18c  arm_EOR_VEC Q11 Q11 Q5 128  ; GHASH 4k+2 low accumulate         *)
(*   0x190  arm_PMULL2_VEC Q8 Q8 Q16 64 ; GHASH 4k+2 mid                    *)
(*   0x194  arm_PMULL2_VEC Q5 Q7 Q12 64 ; GHASH 4k+3 high                   *)
(*   0x198  arm_EOR_VEC Q4 Q4 Q7 64  ; GHASH 4k+3 mid                       *)
(*   0x19c  arm_AESE Q2 Q25          ; round 7 block 2 (rk7=Q25)            *)
(*   0x1a0  arm_AESMC Q2 Q2                                                  *)
(*                                                                           *)
(* Q1: rk7→rk8.  Q2: rk5→rk6→rk7 (2-round advance again).                    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R8R7_LDP_CORRECT = prove
 (`!pc (b1:int128) (b2:int128)
        (rk6:int128) (rk7:int128) (rk8:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x174) /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (\s. read PC s = word (pc + 0x1a4) /\
          read Q1 s = aes_arm_round b1 rk8 /\
          read Q2 s = aes_arm_round (aes_arm_round b2 rk6) rk7 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q1; Q2; Q4; Q5; Q8; Q11] ,,
      MAYCHANGE [X19; X20] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: round 8 b2 + 2-round advance b3 (rk7+rk8) — slice      *)
(* instr 106..114 (offsets 0x1a4..0x1c8).                                    *)
(*                                                                           *)
(* 9-instruction window.  Two scalar EOR pre-XOR-with-roundkey-N ops on      *)
(* X19/X21 (plaintext halves for blocks 4k+5 and 4k+6) join MAYCHANGE        *)
(* without value tracking, alongside the GHASH 4k+2 high accumulate at      *)
(* 0x1b0.                                                                    *)
(*                                                                           *)
(*   0x1a4  arm_EOR X19 X19 X13         ; AES block 4k+5 - round N low (lo) *)
(*   0x1a8  arm_AESE Q2 Q26              ; round 8 block 2 (rk8=Q26)         *)
(*   0x1ac  arm_AESMC Q2 Q2                                                  *)
(*   0x1b0  arm_EOR_VEC Q10 Q10 Q8 128   ; GHASH 4k+2 mid accumulate         *)
(*   0x1b4  arm_AESE Q3 Q25              ; round 7 block 3 (rk7=Q25)         *)
(*   0x1b8  arm_AESMC Q3 Q3                                                  *)
(*   0x1bc  arm_EOR X21 X21 X13          ; AES block 4k+6 - round N low      *)
(*   0x1c0  arm_AESE Q3 Q26              ; round 8 block 3 (rk8=Q26)         *)
(*   0x1c4  arm_AESMC Q3 Q3                                                  *)
(*                                                                           *)
(* Q2: rk7→rk8 (one round).  Q3: rk6→rk7→rk8 (two rounds).                   *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R8_B2_R7R8_B3_CORRECT = prove
 (`!pc (b2:int128) (b3:int128)
        (rk6:int128) (rk7:int128) (rk8:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x1a4) /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (\s. read PC s = word (pc + 0x1c8) /\
          read Q2 s = aes_arm_round b2 rk8 /\
          read Q3 s = aes_arm_round (aes_arm_round b3 rk7) rk8 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q2; Q3; Q10] ,,
      MAYCHANGE [X19; X21])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: GHASH MODULO + plaintext setup, no AES round changes   *)
(* — slice instr 115..137 (offsets 0x1c8..0x224, 23 instructions).           *)
(*                                                                           *)
(* This is the first AES-passthrough cut in the chain: zero AES round       *)
(* advances on Q0..Q3.  The window covers GHASH 4-block MODULO + counter    *)
(* advance W12 += 1, plaintext-XOR-with-rk0 staging for blocks 4k+4 and    *)
(* 4k+5, plus pointer increment X0 += 64.  Many register clobbers absorbed *)
(* by MAYCHANGE without value tracking.                                     *)
(*                                                                           *)
(*   0x1c8  arm_MOVI D8 (word 0xc200000000000000)   ; MODULO constant       *)
(*   0x1cc  arm_PMULL_VEC Q4 Q4 Q16 64              ; MODULO mid pmul       *)
(*   0x1d0  arm_EOR_VEC Q9 Q9 Q5 128                ; MODULO high accum     *)
(*   0x1d4  arm_FMOV_ItoF Q5 X19 0                  ; CTR setup block 4k+5 *)
(*   0x1d8  arm_LDP X6 X7 X0 #0                     ; load plaintext blk 4k+4*)
(*   0x1dc  arm_SHL_VEC Q8 Q8 56 64 64              ; MODULO shift          *)
(*   0x1e0  arm_EOR_VEC Q11 Q11 Q6 128              ; MODULO mid fold       *)
(*   0x1e4  arm_EOR_VEC Q10 Q10 Q4 128              ; MODULO low fold       *)
(*   0x1e8  arm_ADD W12 W12 #1                      ; CTR counter advance   *)
(*   0x1ec  arm_EOR_VEC Q4 Q11 Q9 128               ; MODULO Karatsuba tidy *)
(*   0x1f0  arm_ADD X0 X0 #64                       ; AES input ptr update *)
(*   0x1f4  arm_PMULL_VEC Q7 Q9 Q8 64               ; MODULO top mid align *)
(*   0x1f8  arm_REV W9 W12                          ; CTR byte-swap        *)
(*   0x1fc  arm_EXT Q9 Q9 Q9 64                     ; MODULO other top     *)
(*   0x200  arm_EOR X6 X6 X13                       ; AES blk 4k+4 round N low *)
(*   0x204  arm_EOR_VEC Q10 Q10 Q4 128              ; MODULO low accum     *)
(*   0x208  arm_EOR X7 X7 X14                       ; AES blk 4k+4 round N high*)
(*   0x20c  arm_FMOV_ItoF Q4 X6 0                   ; CTR-XOR-PT staging   *)
(*   0x210  arm_ORR X9 X11 (X9 LSL 32)              ; CTR scratch          *)
(*   0x214  arm_EOR_VEC Q7 Q9 Q7 128                ; MODULO fold into mid *)
(*   0x218  arm_EOR X20 X20 X14                     ; AES blk 4k+5 round N high*)
(*   0x21c  arm_EOR X24 X24 X14                     ; AES blk 4k+7 round N high*)
(*   0x220  arm_ADD W12 W12 #1                      ; CTR counter advance  *)
(*                                                                           *)
(* No AES round changes on Q0..Q3 — all four blocks remain at their post-   *)
(* round-8 (or earlier) state.  Next cut starts at AESE Q0 Q31 (round 9    *)
(* final for block 0) at offset 0x224.                                      *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_MODULO_CORRECT = prove
 (`!pc (q0:int128) (q1:int128) (q2:int128) (q3:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x1c8) /\
          read Q0 s = q0 /\
          read Q1 s = q1 /\
          read Q2 s = q2 /\
          read Q3 s = q3)
     (\s. read PC s = word (pc + 0x224) /\
          read Q0 s = q0 /\
          read Q1 s = q1 /\
          read Q2 s = q2 /\
          read Q3 s = q3)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q4; Q5; Q7; Q8; Q9; Q10; Q11] ,,
      MAYCHANGE [X0; X6; X7; X9; X12; X20; X24] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--23) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 9 final (AESE-only, no AESMC) for blocks 0  *)
(* and 1 — slice instr 138..142 (offsets 0x224..0x238, 5 instructions).      *)
(*                                                                           *)
(* First cut applying `AESE_AS_ARM_FINAL_ROUND` instead of                  *)
(* `AESMC_AESE_AS_ARM_ROUND`.  The kernel encodes AES-128 round 9 (the     *)
(* "round N-1" in s-file comments) as a bare `AESE Qi, Q31` with no       *)
(* trailing AESMC — this is exactly `aes_arm_final_round`.  Q31 holds      *)
(* rk9 (= EL 9 ks in `aes128_cipher_arm`), pre-loaded by the prologue from *)
(* `[kptr + 144]`.  The XOR with rk10 (= EL 10 ks) is deferred to scalar   *)
(* `eor x_lo,x_lo,X13`/`eor x_hi,x_hi,X14` ops earlier in the body, where *)
(* X13/X14 hold rk10 low/high halves.                                      *)
(*                                                                           *)
(*   0x224  arm_AESE Q0 Q31              ; round 9 final block 0 (rk9=Q31) *)
(*   0x228  arm_FMOV_ItoF Q4 X7 1        ; CTR-XOR-PT staging               *)
(*   0x22c  arm_EOR_VEC Q10 Q10 Q7 128   ; MODULO fold into low             *)
(*   0x230  arm_FMOV_ItoF Q7 X23 0       ; CTR setup block 4k+7             *)
(*   0x234  arm_AESE Q1 Q31              ; round 9 final block 1            *)
(*                                                                           *)
(* Q0: post-aes_arm_round-rk8 → aes_arm_final_round-rk9.                   *)
(* Q1: post-aes_arm_round-rk8 → aes_arm_final_round-rk9.                   *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R9_FINAL_B0_B1_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (rk9:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x224) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q31 s = rk9)
     (\s. read PC s = word (pc + 0x238) /\
          read Q0 s = aes_arm_final_round b0 rk9 /\
          read Q1 s = aes_arm_final_round b1 rk9 /\
          read Q31 s = rk9)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q4; Q7; Q10])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESE_AS_ARM_FINAL_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: post-final-round CTR/GHASH passthrough; AES-final-XOR *)
(* preparation — slice instr 143..156 (offsets 0x238..0x270, 14 instr).      *)
(*                                                                           *)
(* Q0/Q1 (which held the round-9 final-round AES results from the prior     *)
(* cut) are *consumed* by EOR_VEC ops at 0x24c/0x260: Q4 ← Q4 ⊕ Q0          *)
(* (ciphertext block 4k+4 = plaintext_xor_with_rk10 ⊕ AES_b0) and Q5 ← Q5  *)
(* ⊕ Q1 (ciphertext block 4k+5).  After that consumption, Q0 and Q1 are    *)
(* freely overwritten with new CTR setup (FMOV_ItoF) for the *next*        *)
(* iteration's blocks 4k+8 and 4k+9 — so this cut does NOT track Q0/Q1    *)
(* values, only Q2 and Q3 (which haven't yet had their final round).      *)
(*                                                                           *)
(*   0x238  arm_FMOV_ItoF Q5 X20 1                ; CTR-XOR-PT staging       *)
(*   0x23c  arm_FMOV_ItoF Q6 X21 0                ; CTR-XOR-PT staging       *)
(*   0x240  arm_SUBS ZR X0 X5                     ; loop-bound check       *)
(*   0x244  arm_FMOV_ItoF Q6 X22 1                ; CTR-XOR-PT staging       *)
(*   0x248  arm_PMULL_VEC Q9 Q10 Q8 64            ; MODULO mid pmul         *)
(*   0x24c  arm_EOR_VEC Q4 Q4 Q0 128              ; ciphertext block 4k+4  *)
(*   0x250  arm_FMOV_ItoF Q0 X10 0                ; CTR setup next iter b0 *)
(*   0x254  arm_FMOV_ItoF Q0 X9 1                 ; CTR setup next iter b0 *)
(*   0x258  arm_REV W9 W12                        ; CTR byte-swap          *)
(*   0x25c  arm_ADD W12 W12 #1                    ; CTR counter advance    *)
(*   0x260  arm_EOR_VEC Q5 Q5 Q1 128              ; ciphertext block 4k+5  *)
(*   0x264  arm_FMOV_ItoF Q1 X10 0                ; CTR setup next iter b1 *)
(*   0x268  arm_ORR X9 X11 (X9 LSL 32)            ; CTR scratch            *)
(*   0x26c  arm_FMOV_ItoF Q1 X9 1                 ; CTR setup next iter b1 *)
(*                                                                           *)
(* SUBS ZR X0 X5 writes flags (NF/ZF/CF/VF) — handled by REWRITE_TAC        *)
(* [SOME_FLAGS] before ENSURES_INIT_TAC, per feedback memory               *)
(* `some_flags_no_canon.md`.                                                *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_FINAL_XOR_AND_CTR_CORRECT = prove
 (`!pc (q2:int128) (q3:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x238) /\
          read Q2 s = q2 /\
          read Q3 s = q3)
     (\s. read PC s = word (pc + 0x270) /\
          read Q2 s = q2 /\
          read Q3 s = q3)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q4; Q5; Q6; Q9] ,,
      MAYCHANGE [X9; X12] ,,
      MAYCHANGE SOME_FLAGS)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: AES round 9 final for blocks 2 and 3 — slice instr    *)
(* 157..166 (offsets 0x270..0x298, 10 instructions).  First cut to include  *)
(* memory STORES (two STR Q4/Q5 ops at 0x278 and 0x28c — ciphertext for    *)
(* blocks 4k+4 and 4k+5).                                                   *)
(*                                                                           *)
(*   0x270  arm_AESE Q2 Q31              ; round 9 final block 2 (rk9=Q31) *)
(*   0x274  arm_REV W9 W12                ; CTR byte-swap                   *)
(*   0x278  arm_STR Q4 X2 #16             ; store ciphertext block 4k+4    *)
(*   0x27c  arm_ORR X9 X11 (X9 LSL 32)    ; CTR scratch                    *)
(*   0x280  arm_EOR_VEC Q11 Q11 Q9 128    ; MODULO low fold                *)
(*   0x284  arm_FMOV_ItoF Q7 X24 1        ; CTR setup block 4k+11          *)
(*   0x288  arm_EXT Q10 Q10 Q10 64        ; MODULO mid alignment           *)
(*   0x28c  arm_STR Q5 X2 #16             ; store ciphertext block 4k+5    *)
(*   0x290  arm_ADD W12 W12 #1            ; CTR counter advance            *)
(*   0x294  arm_AESE Q3 Q31              ; round 9 final block 3            *)
(*                                                                           *)
(* Q2: post-aes_arm_round-rk8 → aes_arm_final_round-rk9.                   *)
(* Q3: post-aes_arm_round-rk8 → aes_arm_final_round-rk9.                   *)
(* X2 advances by 32 bytes (two STR Q with post-immediate +16).            *)
(*                                                                           *)
(* `nonoverlapping (word pc, LENGTH ...) (cptr, 32)` precondition required  *)
(* for the simulator to discharge "updates will not modify the program     *)
(* code".  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] folds         *)
(* aes_gcm_main_loop_body_slice_mc into its byte-list form so MAYCHANGE    *)
(* on the program-text region can be ruled out.                            *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R9_FINAL_B2_B3_CORRECT = prove
 (`!pc (cptr:int64) (b2:int128) (b3:int128) (rk9:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x270) /\
              read X2 s = cptr /\
              read Q2 s = b2 /\
              read Q3 s = b3 /\
              read Q31 s = rk9)
         (\s. read PC s = word (pc + 0x298) /\
              read X2 s = word_add cptr (word 32) /\
              read Q2 s = aes_arm_final_round b2 rk9 /\
              read Q3 s = aes_arm_final_round b3 rk9 /\
              read Q31 s = rk9)
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q2; Q3; Q7; Q10; Q11] ,,
          MAYCHANGE [X2; X9; X12] ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16))] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESE_AS_ARM_FINAL_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 small-cut: body tail — slice instr 167..175 (offsets             *)
(* 0x298..0x2bc, the END of the loop body slice, 9 instructions).           *)
(*                                                                           *)
(* Final ciphertext stores for blocks 4k+6 and 4k+7, plus the last MODULO  *)
(* fold and CTR setup tail.                                                 *)
(*                                                                           *)
(*   0x298  arm_EOR_VEC Q6 Q6 Q2 128       ; ciphertext block 4k+6         *)
(*   0x29c  arm_FMOV_ItoF Q2 X10 0         ; CTR setup next iter b2        *)
(*   0x2a0  arm_STR Q6 X2 #16              ; store ciphertext block 4k+6   *)
(*   0x2a4  arm_FMOV_ItoF Q2 X9 1          ; CTR setup next iter b2        *)
(*   0x2a8  arm_REV W9 W12                 ; CTR byte-swap                 *)
(*   0x2ac  arm_EOR_VEC Q11 Q11 Q10 128    ; MODULO final fold into low    *)
(*   0x2b0  arm_ORR X9 X11 (X9 LSL 32)     ; CTR scratch                   *)
(*   0x2b4  arm_EOR_VEC Q7 Q7 Q3 128       ; ciphertext block 4k+7         *)
(*   0x2b8  arm_STR Q7 X2 #16              ; store ciphertext block 4k+7   *)
(*                                                                           *)
(* Q2 is consumed by EOR with Q6 then overwritten with new CTR setup; Q3   *)
(* is consumed by EOR with Q7.  Cut postcondition does not track Q2/Q3    *)
(* since their values are no longer relevant (next iteration starts fresh).*)
(* End PC = pc + 0x2bc = end of body slice.                                *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_TAIL_CORRECT = prove
 (`!pc (cptr:int64) (q2:int128) (q3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x298) /\
              read X2 s = cptr /\
              read Q2 s = q2 /\
              read Q3 s = q3)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 32))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q2; Q6; Q7; Q11] ,,
          MAYCHANGE [X2; X9; X12] ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16))] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

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
(*          (c0_in:int128) (c1_in:int128) (c2_in:int128)                    *)
(*                                    ; CTR pre-images for blocks 4k+4..4k+6*)
(*          (c4_prev:int128)..(c7_prev:int128) ; previous iter's ciphertexts*)
(*          (running_tag:int128)     ; GHASH spec-form running tag.  Q11    *)
(*                                    ;  holds byteswap128 running_tag.    *)
(*          (rk0:int128)..(rk10:int128)  ; AES-128 round keys                *)
(*          (h:int128)               ; GHASH spec key (= aes128_cipher 0 ks; *)
(*                                    ;  the H-power table holds powers of  *)
(*                                    ;  ghash_twist h, NOT h itself)       *)
(*          (pptr:int64) (cptr:int64) (eptr:int64)                           *)
(*          (sx10:int64) (sx11:int64) (sx9:int64)  ; counter-scratch state  *)
(*          (sw12:int32)             ; current 32-bit big-endian counter    *)
(*          (plaintext_4:int128)..(plaintext_7:int128).                      *)
(*    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc)      *)
(*                   (cptr, 64) /\                                            *)
(*    ALLPAIRS nonoverlapping                                                *)
(*      [(pptr, 64); (cptr, 64)] [...] /\                                    *)
(*    ; Note: the body slice does NOT touch the H-table memory — Q12..Q17  *)
(*    ; already hold the loaded values from the prelude.  htable_mem is    *)
(*    ; therefore not a body-level precondition; it lives at the           *)
(*    ; subroutine wrapper level where loop iterations rely on it being   *)
(*    ; preserved across iterations.                                       *)
(*    ==> ensures arm                                                        *)
(*         (\s. aligned_bytes_loaded s (word pc)                            *)
(*                 aes_gcm_main_loop_body_slice_mc /\                       *)
(*              read PC s = word pc /\                                       *)
(*              read X0 s = pptr /\                                          *)
(*              read X2 s = cptr /\                                          *)
(*              read X5 s = eptr /\                                          *)
(*              ; Q0..Q2 hold the pre-images for AES blocks 4k+4..4k+6.    *)
(*              ; Q3 is REBUILT inside the body from scalars X9/X10 at     *)
(*              ; slice offsets 0x14 / 0x30 (`fmov d3, x10; fmov v3.d[1],  *)
(*              ; x9`), so its body-entry value is irrelevant — c3_in is   *)
(*              ; expressed in terms of (sx10, sx9), not as a Q3 read.     *)
(*              ; Per session 024's discovery: c3_in =                     *)
(*              ; word_insert (word_zx sx10:int128) (64,64) sx9 :int128.   *)
(*              read Q0 s = c0_in /\ read Q1 s = c1_in /\ read Q2 s = c2_in /\*)
(*              ; Counter scratch live at body entry:                        *)
(*              read X10 s = sx10 /\ read X11 s = sx11 /\                   *)
(*              read X9 s = sx9 /\                                           *)
(*              read W12 s = sw12 /\                                         *)
(*              read Q4 s = byteswap128 c4_prev /\ ... /\                    *)
(*              ; Q11 holds the running tag in the KERNEL form (= byteswap  *)
(*              ; of the spec-form `running_tag`) — the kernel keeps Q11    *)
(*              ; byteswap-flipped throughout the loop, matching the        *)
(*              ; pattern in GHASH_4BLOCK_CORRECT (whose `prev_tag` is the  *)
(*              ; spec form, and whose precondition has Q4 = byteswap128   *)
(*              ; (prev_tag XOR c0)).                                        *)
(*              read Q11 s = byteswap128 running_tag /\                      *)
(*              ; htable_mem layout (h_power numbering: 0 = H^1, 3 = H^4).   *)
(*              ; Same convention as GHASH_4BLOCK_CORRECT.                   *)
(*              read Q12 s = byteswap128 (h_power (ghash_twist h) 0) /\      *)
(*              read Q13 s = byteswap128 (h_power (ghash_twist h) 1) /\      *)
(*              read Q14 s = byteswap128 (h_power (ghash_twist h) 2) /\      *)
(*              read Q15 s = byteswap128 (h_power (ghash_twist h) 3) /\      *)
(*              read Q16 s =                                                  *)
(*                word_join                                                   *)
(*                  (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)     *)
(*                  (karatsuba_mid (h_power (ghash_twist h) 0) :64 word) /\  *)
(*              read Q17 s =                                                  *)
(*                word_join                                                   *)
(*                  (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)     *)
(*                  (karatsuba_mid (h_power (ghash_twist h) 2) :64 word) /\  *)
(*              read Q18 s = rk0 /\ ... /\ read Q26 s = rk8 /\               *)
(*              read Q31 s = rk9 /\                                          *)
(*              ; Q27 = rk9 and Q28 = rk10 are loaded by the prelude but    *)
(*              ; the body uses Q31 (= rk9) and the X13/X14 scalar trick    *)
(*              ; (= rk10 bits) instead.  Q29..Q30 are dead AES-256 slots.  *)
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
(*               ; Postcondition Q11.  Empirically determined in session   *)
(*               ; 026 by setting up the cut and running ARM_STEPS_TAC +   *)
(*               ; ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC[]: the goal  *)
(*               ; reduces to `read Q11 s = nist_ghash h running_tag      *)
(*               ; [c4_prev..c7_prev]` directly, NOT to `byteswap128(...)`.*)
(*               ; Reason: the body's `ext q11,q11,q11,#8` at slice instr *)
(*               ; 11 (offset 0x028) effectively unswaps Q11 (since        *)
(*               ; byteswap128 is the same half-swap operation), and the  *)
(*               ; chain of pmull/eor that follows produces the running   *)
(*               ; tag in spec-form directly.                              *)
(*               read Q11 s = nist_ghash h running_tag                    *)
(*                              [c4_prev; c5_prev; c6_prev; c7_prev]) /\   *)
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
(*                                                                           *)
(* SESSION 026 EMPIRICAL FINDINGS (HIGH confidence):                          *)
(*                                                                           *)
(*  - The above postcondition shape was VERIFIED by setting up the cut       *)
(*    interactively, running                                                  *)
(*      REPEAT GEN_TAC + REWRITE_TAC[SOME_FLAGS] + STRIP_TAC +                *)
(*      ENSURES_INIT_TAC "s0" + ARM_STEPS_TAC ... (1--175) +                  *)
(*      ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC[].                         *)
(*    The goal reduces cleanly to                                              *)
(*      <huge word_pmul/word_join nest of size ~2.5MB>                        *)
(*      = nist_ghash h running_tag [c4_prev; c5_prev; c6_prev; c7_prev]      *)
(*    confirming Q11's exit form is spec-form (NOT byteswap-form).           *)
(*                                                                           *)
(*  - Wall-clock budget:                                                      *)
(*      ARM_STEPS_TAC (1--175):           ~3 minutes                          *)
(*      ENSURES_FINAL_STATE_TAC:           ~30 seconds                        *)
(*      ASM_REWRITE_TAC[]:                 ~5 seconds (small no-op)           *)
(*      The full 8-step ABBREV_TAC chain:  ~30 seconds                        *)
(*    Total to reach the post-ABBREV state: ~5 minutes.                       *)
(*                                                                           *)
(*  - **WORD_BLAST is the problem.**  After the ABBREV_TAC chain, the        *)
(*    goal contains the same Karatsuba pmul atoms as in                        *)
(*    GHASH_4BLOCK_CORRECT, but the symbolic state on the body slice is      *)
(*    ~10x larger than ghash_4block's state because the AES half has         *)
(*    inflated each Q/X register's symbolic shape.  The first SUBGOAL_THEN  *)
(*    in the GHASH_4BLOCK closing template (the one that asserts the 3      *)
(*    pmull-arg cleanups via `CONV_TAC WORD_BLAST`) HUNG indefinitely        *)
(*    in session 026 — the holctl session became unresponsive after          *)
(*    several minutes and required SIGINT + restart.                         *)
(*                                                                           *)
(*  - **Recommended path forward**: split into intermediate cuts.            *)
(*      (a) `GHASH_PRELUDE_CUT`: slice instr 1..21 (slice offsets 0..0x50)  *)
(*          which covers the rev64+ext+eor chain that prepares Q4 in        *)
(*          GHASH_4BLOCK_CORRECT-precondition form (Q4 := byteswap128 c4    *)
(*          XOR running_tag, in some pre-rev64 representation).  With Q5,  *)
(*          Q6, Q7 still in their precondition forms, the post-state of    *)
(*          this cut should match GHASH_4BLOCK_CORRECT's precondition       *)
(*          (modulo the exact byteswap orientation of Q4).                  *)
(*      (b) `GHASH_KARATSUBA_CUT`: slice instr 22..145 (slice offsets       *)
(*          0x50..0x5b0) which is the Karatsuba+MODULO body that            *)
(*          GHASH_4BLOCK_CORRECT proves on freestanding mc.  Stating        *)
(*          this cut on the body slice (with the AES instructions          *)
(*          interleaved) requires absorbing AES side-effects into          *)
(*          MAYCHANGE without value-tracking — the same MAYCHANGE-         *)
(*          absorption pattern session 022 used for the AES-only chain.    *)
(*    These two cuts compose with the existing AES-only cuts via the        *)
(*    brute-force re-symbolic-execution pattern from session 024 (run      *)
(*    ARM_STEPS_TAC over the union range; faster than cut-point machinery).*)
(*                                                                           *)
(*  - **Alternative**: per-block GHASH cut (4 per-block Karatsuba           *)
(*    computations on Q9/Q10/Q11 separately, plus the MODULO chain).        *)
(*    Each per-block cut has ~10 instructions of GHASH ops to value-track, *)
(*    avoiding the full 30-instruction Karatsuba+MODULO state explosion.    *)
(*    Trade-off: 4-5 cuts vs 1, but each closes with WORD_BLAST on a       *)
(*    much smaller goal.                                                     *)
(*                                                                           *)
(*  - **State at SIGINT** in session 026:                                    *)
(*      goal = `(LHS) = nist_ghash h running_tag [c4..c7]` after the        *)
(*             8 H_LO/H_HI + 8 c_lo/c_hi/pp0_lo/pp0_hi ABBREV_TAC steps.    *)
(*      assumptions: 32 (the precondition reads) + the ABBREV_TAC defs.    *)
(*      LHS is a 2.5MB nested word_pmul/word_xor/word_subword/word_join     *)
(*      tree — same shape as GHASH_4BLOCK_CORRECT's post-ABBREV state but  *)
(*      with much heavier word_subword/word_join byte-level accounting.   *)
(*    The next SUBGOAL_THEN (`CONV_TAC WORD_BLAST`) is what hangs.          *)
(*    Splitting cuts as above should keep the LHS small enough to close.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Phase 7 composition pilot: R0_BLOCKS012 + R1_BLOCKS012 fused.             *)
(*                                                                           *)
(* This is the smallest meaningful composition of two adjacent body-slice    *)
(* cuts.  It validates that the natural "compose by re-running symbolic      *)
(* execution over the union range" pattern works cleanly when each cut's    *)
(* closing tactic is the same shape (`ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_     *)
(* ROUND]`).  The composed cut covers slice instructions 1..17 (offsets    *)
(* 0..0x44), which is the full union of R0_BLOCKS012's 8 instructions       *)
(* with R1_BLOCKS012's 9.                                                   *)
(*                                                                           *)
(* Note: the composition is by re-running symbolic execution rather than    *)
(* by cut-point machinery (MATCH_MP_TAC of each individual cut).  The       *)
(* trade-off: re-running adds ~17 instructions of `ARM_STEPS_TAC` time     *)
(* (~0.2s wall) but uses the exact same closing tactic as each individual  *)
(* cut.  The cut-point composition path requires `ENSURES_FRAME_SUBSUMED`  *)
(* + `ENSURES_PRECONDITION_THM` plumbing per cut and a subsumption proof   *)
(* on each step's MAYCHANGE — much heavier per-step but linear in the     *)
(* number of cuts.  For 17 cuts the brute-force re-execution is simpler    *)
(* and still fast (~2s total).                                              *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R0R1_BLOCKS012_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b11:int128)
        (rk0:int128) (rk1:int128) (sx9:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q11 s = b11 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read X9 s = sx9)
     (\s. read PC s = word (pc + 0x44) /\
          read Q0 s = aes_arm_round (aes_arm_round b0 rk0) rk1 /\
          read Q1 s = aes_arm_round (aes_arm_round b1 rk0) rk1 /\
          read Q2 s = aes_arm_round (aes_arm_round b2 rk0) rk1 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q11] ,,
      MAYCHANGE [X23; X24] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 BIG composition cut: full AES rounds 0..8 for all 4 blocks.       *)
(*                                                                           *)
(* Slice offsets 0..0x224 = 137 instructions, ~80% of the body slice.        *)
(* Composes the equivalent of 12 individual cuts (R0_BLOCKS012,               *)
(* R1_BLOCKS012, R2_BLOCKS01, R0R3_BLOCK3_BLOCK0, R1_BLOCK3,                  *)
(* R4R2_BLOCK0_BLOCK2, R5R3R2_3BLOCK, R6R4R3_4BLOCK, AES_PHASE2,              *)
(* R7R6_BLOCK1_BLOCK3, R8R7_LDP, R8_B2_R7R8_B3, GHASH_MODULO).               *)
(*                                                                           *)
(* Block 3's pre-state value is irrelevant at the body slice entry — the    *)
(* kernel BUILDS Q3 from scalar X9/X10 (CTR setup) inside the body.         *)
(* `fmov d3, x10; fmov v3.d[1], x9` at slice offsets 0x14 and 0x30          *)
(* construct Q3 = `word_insert (word_zx sx10) (64,64) sx9`.                 *)
(* All four blocks then traverse rounds 0..8 (9 round applications),       *)
(* ending at PC = pc + 0x224 (right before the round-9 `aese` ops).          *)
(*                                                                           *)
(* The interior GHASH-Karatsuba ops (Q4..Q11 effects) are absorbed in       *)
(* MAYCHANGE without value-tracking — per session 022's MAYCHANGE-          *)
(* absorption discovery.  Round keys Q18..Q26 are preserved, scalar         *)
(* round-N-1 key bits in X13/X14 are preserved.                              *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_AES_8ROUNDS_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b11:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q11 s = b11 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8 /\
          read X9 s = sx9 /\
          read X10 s = sx10 /\
          read X13 s = sx13 /\
          read X14 s = sx14)
     (\s. read PC s = word (pc + 0x224) /\
          read Q0 s =
            aes_arm_round (aes_arm_round (aes_arm_round
              (aes_arm_round (aes_arm_round (aes_arm_round
                (aes_arm_round (aes_arm_round (aes_arm_round
                   b0 rk0) rk1) rk2) rk3) rk4) rk5) rk6) rk7) rk8 /\
          read Q1 s =
            aes_arm_round (aes_arm_round (aes_arm_round
              (aes_arm_round (aes_arm_round (aes_arm_round
                (aes_arm_round (aes_arm_round (aes_arm_round
                   b1 rk0) rk1) rk2) rk3) rk4) rk5) rk6) rk7) rk8 /\
          read Q2 s =
            aes_arm_round (aes_arm_round (aes_arm_round
              (aes_arm_round (aes_arm_round (aes_arm_round
                (aes_arm_round (aes_arm_round (aes_arm_round
                   b2 rk0) rk1) rk2) rk3) rk4) rk5) rk6) rk7) rk8 /\
          read Q3 s =
            aes_arm_round (aes_arm_round (aes_arm_round
              (aes_arm_round (aes_arm_round (aes_arm_round
                (aes_arm_round (aes_arm_round (aes_arm_round
                   (word_insert (word_zx sx10:int128) (64,64) sx9 :int128)
                rk0) rk1) rk2) rk3) rk4) rk5) rk6) rk7) rk8 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                 Q8; Q9; Q10; Q11] ,,
      MAYCHANGE [X0; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--137) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-PRELUDE cut: tracks the GHASH `rev64+ext+eor` chain         *)
(* on Q4 and Q11 across slice instr 1..21 (offsets 0..0x50).                 *)
(*                                                                           *)
(* The body's first 21 instructions interleave AES rounds 0..2 for blocks   *)
(* 0/1/2 with the GHASH PRE chain that prepares Q4 for the per-block        *)
(* Karatsuba.  The GHASH PRE chain is:                                       *)
(*                                                                           *)
(*   instr 3  (offset 0x008): arm_REV64_VEC Q4 Q4 8        ; rev64 v4       *)
(*   instr 9  (offset 0x020): arm_EXT       Q11 Q11 Q11 64 ; ext q11,q,#8  *)
(*   instr 21 (offset 0x050): arm_EOR_VEC   Q4 Q4 Q11 128  ; PRE 1          *)
(*                                                                           *)
(* For arbitrary input forms `q4_pre` and `q11_pre`, the cut establishes:   *)
(*                                                                           *)
(*   read Q11 s = byteswap128 q11_pre                                        *)
(*   read Q4  s = word_xor (aes_gcm_rev64_int128 q4_pre)                    *)
(*                         (byteswap128 q11_pre)                             *)
(*                                                                           *)
(* Two algebraic identities discovered in this proof (close via WORD_BLAST  *)
(* on REWRITE_TAC[byteswap128;aes_gcm_rev64_int128] expansion):              *)
(*                                                                           *)
(*   (a) word_subword (word_join q11 q11) (64,128) = byteswap128 q11        *)
(*       — i.e. the kernel's `ext q,q,q,#8` on a 128-bit register equals    *)
(*       byteswap128 (the 64-bit half-swap), without rev64 within halves.    *)
(*                                                                           *)
(*   (b) The 28-byte word_join/word_subword tree from `arm_REV64_VEC` of    *)
(*       esize=8 collapses to `aes_gcm_rev64_int128 q4_pre`, defined as     *)
(*       `word_join (word_bytereverse subword_hi)                            *)
(*                  (word_bytereverse subword_lo)`.                          *)
(*                                                                           *)
(* These identities, plus AESMC_AESE_AS_ARM_ROUND for the AES rounds, close *)
(* under a single CONV_TAC WORD_BLAST after expanding `byteswap128` and    *)
(* `aes_gcm_rev64_int128` definitions.                                       *)
(*                                                                           *)
(* This cut is the GHASH-PRELUDE building block for a future `Q4 =          *)
(* byteswap128 (running_tag XOR c4_prev)`-shaped cut: that interpretation   *)
(* requires the byteswap-distributes-over-XOR identity                      *)
(* `byteswap128 (a XOR b) = byteswap128 a XOR byteswap128 b` AND a          *)
(* relationship between `aes_gcm_rev64_int128` and `byteswap128` on the    *)
(* specific kernel-form ciphertext (which is determined by the prior        *)
(* iteration's exit Q4..Q7 shape — to be discovered when composing across  *)
(* iterations in Phase 8).                                                   *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_PRELUDE_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128)
        (sx9:int64) (sx10:int64) (sx13:int64)
        (q4_pre:int128) (q11_pre:int128)
        (q15:int128) (q17:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q4 s = q4_pre /\
          read Q11 s = q11_pre /\
          read Q15 s = q15 /\
          read Q17 s = q17 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read X9 s = sx9 /\
          read X10 s = sx10 /\
          read X13 s = sx13)
     (\s. read PC s = word (pc + 0x54) /\
          read Q0 s = aes_arm_round (aes_arm_round (aes_arm_round b0 rk0) rk1) rk2 /\
          read Q1 s = aes_arm_round (aes_arm_round b1 rk0) rk1 /\
          read Q2 s = aes_arm_round (aes_arm_round b2 rk0) rk1 /\
          read Q3 s = word_insert (word_zx sx10 :int128) (64,64) sx9 /\
          read Q4 s = word_xor (aes_gcm_rev64_int128 q4_pre)
                               (byteswap128 q11_pre) /\
          read Q11 s = byteswap128 q11_pre /\
          read Q15 s = q15 /\
          read Q17 s = q17 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read X13 s = sx13)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q11] ,,
      MAYCHANGE [X21; X22; X23; X24] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--21) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND;
                  aes_gcm_rev64_int128; byteswap128] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-0-HIGH-PMULL2 cut: tracks Q9 = pmull2(Q4, Q15)        *)
(* across slice instr 22..30 (offsets 0x054..0x078).                          *)
(*                                                                           *)
(* The window covers AES rounds 2 (block 1) / 3 (block 0) / 0 (block 3) and  *)
(* the first two GHASH ops for block 0:                                      *)
(*                                                                           *)
(*   instr 22 (offset 0x054): arm_AESE Q1 Q20      ; AES rd 2 blk 1          *)
(*   instr 23 (offset 0x058): arm_AESMC Q1 Q1                                *)
(*   instr 24 (offset 0x05c): arm_AESE Q3 Q18      ; AES rd 0 blk 3          *)
(*   instr 25 (offset 0x060): arm_AESMC Q3 Q3                                *)
(*   instr 26 (offset 0x064): arm_EOR X23 X23 X13  ; scalar plt+rk N         *)
(*   instr 27 (offset 0x068): arm_AESE Q0 Q21      ; AES rd 3 blk 0          *)
(*   instr 28 (offset 0x06c): arm_AESMC Q0 Q0                                *)
(*   instr 29 (offset 0x070): arm_DUP_GEN_FROM_ELEM Q10 Q17 64 64 1          *)
(*   instr 30 (offset 0x074): arm_PMULL2_VEC Q9 Q4 Q15 64                    *)
(*                                                                           *)
(* Postcondition asserts the high-half polynomial product:                  *)
(*                                                                           *)
(*   read Q9 s = word_pmul (word_subword q4 (64,64) :64 word)               *)
(*                         (word_subword q15 (64,64) :64 word)               *)
(*                                                                           *)
(* This is the first per-component value-tracking cut on the GHASH region.  *)
(* It is independent of the GHASH-PRELUDE cut (uses fresh `q4` / `q15`     *)
(* variables) but composes with it via brute-force re-execution per         *)
(* session 024's pattern: a future PRELUDE_AND_BLOCK0_PMULL2 composition    *)
(* cut over instr 1..30 just runs ARM_STEPS_TAC on the union range.         *)
(*                                                                           *)
(* The closing tactic is the standard 5-line spine:                          *)
(*   REPEAT GEN_TAC; ENSURES_INIT_TAC "s0";                                  *)
(*   ARM_STEPS_TAC ... (1--9); ENSURES_FINAL_STATE_TAC;                      *)
(*   ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND].                               *)
(*                                                                           *)
(* PMULL2 doesn't need a special bridge because the simulator emits its     *)
(* output `word_pmul (subword Rn (64,64)) (subword Rm (64,64))` directly    *)
(* — exactly matching the postcondition's algebraic form.  Q1 sits in     *)
(* MAYCHANGE without value-tracking (round-2 advance for block 1).  Q10    *)
(* is also clobbered (the DUP_GEN); its value `word_zx (subword q17        *)
(* (64,64))` is left for a future cut to track.                              *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK0_HIGH_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b3:int128)
        (q4:int128) (q15:int128) (q17:int128)
        (rk0:int128) (rk2:int128) (rk3:int128) (sx13:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x54) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q3 s = b3 /\
          read Q4 s = q4 /\
          read Q15 s = q15 /\
          read Q17 s = q17 /\
          read Q18 s = rk0 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read X13 s = sx13)
     (\s. read PC s = word (pc + 0x78) /\
          read Q0 s = aes_arm_round b0 rk3 /\
          read Q1 s = aes_arm_round b1 rk2 /\
          read Q3 s = aes_arm_round b3 rk0 /\
          read Q4 s = q4 /\
          read Q9 s = (word_pmul (word_subword q4 (64,64) :64 word)
                                 (word_subword q15 (64,64) :64 word)
                       :int128) /\
          read Q10 s = (word_zx (word_subword q17 (64,64) :64 word) :int128) /\
          read Q15 s = q15 /\
          read Q17 s = q17 /\
          read Q18 s = rk0 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q3; Q9; Q10] ,,
      MAYCHANGE [X23])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-0-LOW cut: tracks Q11 = pmull(Q4, Q15) AND the        *)
(* block-1 PRE rev64 (Q5 = aes_gcm_rev64_int128 q5_pre) across slice          *)
(* instr 31..38 (offsets 0x078..0x098).                                       *)
(*                                                                           *)
(* Window:                                                                   *)
(*   instr 31 (offset 0x078): arm_EOR X22 X22 X14   ; AES blk 6 rd N hi      *)
(*   instr 32 (offset 0x07c): arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1            *)
(*   instr 33 (offset 0x080): arm_AESE Q3 Q19       ; AES rd 1 blk 3         *)
(*   instr 34 (offset 0x084): arm_AESMC Q3 Q3                                *)
(*   instr 35 (offset 0x088): arm_REV64_VEC Q5 Q5 8 ; GHASH PRE block 1     *)
(*   instr 36 (offset 0x08c): arm_AESE Q0 Q22       ; AES rd 4 blk 0         *)
(*   instr 37 (offset 0x090): arm_AESMC Q0 Q0                                *)
(*   instr 38 (offset 0x094): arm_PMULL_VEC Q11 Q4 Q15 64                    *)
(*                                                                           *)
(* Postcondition asserts:                                                    *)
(*                                                                           *)
(*   read Q11 s = word_pmul (word_subword q4 (0,64) :64 word)                *)
(*                          (word_subword q15 (0,64) :64 word)               *)
(*   read Q5  s = aes_gcm_rev64_int128 q5_pre                                *)
(*                                                                           *)
(* Plus AES round advances: Q0 advances rk3→rk4, Q3 advances rk0→rk1.       *)
(*                                                                           *)
(* The Q11 product is the BLOCK 0 LOW Karatsuba component (overwriting the  *)
(* prelude's `byteswap128 q11_pre` carry).  The Q5 byteswap kicks off       *)
(* block-1's GHASH PRE chain.  Q8 (DUP_GEN of Q4 high half) sits in         *)
(* MAYCHANGE without value-tracking — its specific value will be used in   *)
(* the block-0 mid-pmull-prep cut at instr 39 (EOR Q8 Q8 Q4) and the       *)
(* block-0 mid-pmull at instr 47.                                            *)
(*                                                                           *)
(* The closing tactic adds `aes_gcm_rev64_int128` to the rewrite set and   *)
(* uses CONV_TAC WORD_BLAST to discharge the Q5 byteswap form (the         *)
(* rev64+rev64+rev64 word_join/word_subword tree from arm_REV64_VEC esize  *)
(* =8 collapses to aes_gcm_rev64_int128's two-bytereverse-and-swap form).  *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK0_LOW_CORRECT = prove
 (`!pc (b0:int128) (b3:int128) (q4:int128) (q15:int128) (q5_pre:int128)
        (rk1:int128) (rk4:int128) (sx14:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x78) /\
          read Q0 s = b0 /\
          read Q3 s = b3 /\
          read Q4 s = q4 /\
          read Q5 s = q5_pre /\
          read Q15 s = q15 /\
          read Q19 s = rk1 /\
          read Q22 s = rk4 /\
          read X14 s = sx14)
     (\s. read PC s = word (pc + 0x98) /\
          read Q0 s = aes_arm_round b0 rk4 /\
          read Q3 s = aes_arm_round b3 rk1 /\
          read Q4 s = q4 /\
          read Q5 s = aes_gcm_rev64_int128 q5_pre /\
          read Q8 s = (word_zx (word_subword q4 (64,64) :64 word) :int128) /\
          read Q11 s = (word_pmul (word_subword q4 (0,64) :64 word)
                                  (word_subword q15 (0,64) :64 word)
                        :int128) /\
          read Q15 s = q15 /\
          read Q19 s = rk1 /\
          read Q22 s = rk4)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q3; Q5; Q8; Q11] ,,
      MAYCHANGE [X22])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND; aes_gcm_rev64_int128] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-1-HIGH cut: tracks Q4 = pmull2(Q5, Q14) AND the       *)
(* block-3 PRE rev64 (Q7 = aes_gcm_rev64_int128 q7_pre) across slice         *)
(* instr 39..46 (offsets 0x098..0x0b8).                                       *)
(*                                                                           *)
(* Window:                                                                   *)
(*   instr 39 (offset 0x098): arm_EOR_VEC Q8 Q8 Q4 64    ; blk-0 mid prep   *)
(*   instr 40 (offset 0x09c): arm_AESE Q2 Q20            ; AES rd 2 blk 2   *)
(*   instr 41 (offset 0x0a0): arm_AESMC Q2 Q2                                *)
(*   instr 42 (offset 0x0a4): arm_AESE Q0 Q23            ; AES rd 5 blk 0   *)
(*   instr 43 (offset 0x0a8): arm_AESMC Q0 Q0                                *)
(*   instr 44 (offset 0x0ac): arm_REV64_VEC Q7 Q7 8      ; GHASH PRE blk 3  *)
(*   instr 45 (offset 0x0b0): arm_PMULL2_VEC Q4 Q5 Q14 64 ; blk-1 HIGH      *)
(*   instr 46 (offset 0x0b4): arm_PMULL_VEC Q10 Q8 Q10 64 ; blk-0 MID       *)
(*                                                                           *)
(* Postcondition asserts:                                                    *)
(*                                                                           *)
(*   read Q4 s = word_pmul (word_subword q5 (64,64)) (word_subword q14 (64,64))*)
(*   read Q7 s = aes_gcm_rev64_int128 q7_pre                                 *)
(*                                                                           *)
(* The block-1 HIGH pmull product **OVERWRITES Q4** (the cut consumes Q4   *)
(* via the EOR at instr 39 then puts a new value there at instr 45).  The  *)
(* block-0 MID pmull at instr 46 writes Q10; its value depends on the       *)
(* prior Q8 (post-EOR) and Q10 (post-DUP_GEN); for now Q10 stays in        *)
(* MAYCHANGE.  Closes via the standard ASM_REWRITE_TAC + CONV_TAC          *)
(* WORD_BLAST pattern.                                                       *)
(*                                                                           *)
(* This cut completes the per-component decomposition for the FIRST half  *)
(* of the per-block Karatsuba sequence (block-0 HIGH+LOW from prior cuts;  *)
(* block-1 HIGH here).  Future cuts handle block-0 MID, block-1 LOW/MID,   *)
(* block-2 HIGH/LOW/MID, block-3 HIGH/LOW/MID, plus the EOR accumulators.  *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK1_HIGH_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128)
        (q5:int128) (q14:int128)
        (q7_pre:int128) (q8_pre:int128) (q10_pre:int128) (q4_in:int128)
        (rk2:int128) (rk5:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x98) /\
          read Q0 s = b0 /\
          read Q2 s = b2 /\
          read Q4 s = q4_in /\
          read Q5 s = q5 /\
          read Q7 s = q7_pre /\
          read Q8 s = q8_pre /\
          read Q10 s = q10_pre /\
          read Q14 s = q14 /\
          read Q20 s = rk2 /\
          read Q23 s = rk5)
     (\s. read PC s = word (pc + 0xb8) /\
          read Q0 s = aes_arm_round b0 rk5 /\
          read Q2 s = aes_arm_round b2 rk2 /\
          read Q4 s = (word_pmul (word_subword q5 (64,64) :64 word)
                                 (word_subword q14 (64,64) :64 word)
                       :int128) /\
          read Q5 s = q5 /\
          read Q7 s = aes_gcm_rev64_int128 q7_pre /\
          read Q14 s = q14 /\
          read Q20 s = rk2 /\
          read Q23 s = rk5)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q2; Q4; Q7; Q8; Q10] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND; aes_gcm_rev64_int128] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-0-MID + block-1-HIGH cut: tracks both Q10 (block-0    *)
(* MID Karatsuba) AND Q4 (block-1 HIGH Karatsuba) AND Q7 (block-3 PRE) over *)
(* slice instr 39..46 (offsets 0x098..0x0b8), the same window as            *)
(* AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK1_HIGH_CORRECT but with the additional *)
(* Q10 conjunct.  This subsumes BLOCK1_HIGH for compositions that need the  *)
(* block-0 MID product.                                                       *)
(*                                                                           *)
(* Window (same as BLOCK1_HIGH):                                             *)
(*   instr 39 (offset 0x098): arm_EOR_VEC Q8 Q8 Q4 64    ; blk-0 mid prep   *)
(*   instr 40 (offset 0x09c): arm_AESE Q2 Q20            ; AES rd 2 blk 2   *)
(*   instr 41 (offset 0x0a0): arm_AESMC Q2 Q2                                *)
(*   instr 42 (offset 0x0a4): arm_AESE Q0 Q23            ; AES rd 5 blk 0   *)
(*   instr 43 (offset 0x0a8): arm_AESMC Q0 Q0                                *)
(*   instr 44 (offset 0x0ac): arm_REV64_VEC Q7 Q7 8      ; GHASH PRE blk 3  *)
(*   instr 45 (offset 0x0b0): arm_PMULL2_VEC Q4 Q5 Q14 64 ; blk-1 HIGH      *)
(*   instr 46 (offset 0x0b4): arm_PMULL_VEC Q10 Q8 Q10 64 ; blk-0 MID       *)
(*                                                                           *)
(* New postcondition vs BLOCK1_HIGH:                                         *)
(*                                                                           *)
(*   read Q10 s = word_pmul (subword (xor q4_in q8_pre) (0,64))             *)
(*                          (subword q10_pre (0,64))                         *)
(*                                                                           *)
(* Note Q4-first XOR order: instr 39 `EOR_VEC Q8 Q8 Q4` reads Rm=Q4 first   *)
(* (m), Rn=Q8 second (n), so the simulator emits `word_xor q4_in q8_pre`    *)
(* in that order.                                                            *)
(*                                                                           *)
(* The closing tactic uses REPEAT CONJ_TAC to split the 9 postcondition     *)
(* conjuncts so each can be discharged with a targeted closer:              *)
(* - PC, Q0/Q2 (AES round advance), Q5/Q14/Q20/Q23 (preserved): ASM_REWRITE *)
(* - Q4 (block-1 HIGH pmull2): ASM_REWRITE_TAC matches simulator output    *)
(* - Q7 (block-3 PRE rev64): unfold aes_gcm_rev64_int128 + WORD_BLAST       *)
(* - Q10 (block-0 MID pmull): AP_THM_TAC + AP_TERM_TAC reduces to the       *)
(*   single subword/zx identity, closed by WORD_BLAST                        *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK0_MID_BLOCK1_HIGH_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128)
        (q5:int128) (q14:int128)
        (q7_pre:int128) (q8_pre:int128) (q10_pre:int128) (q4_in:int128)
        (rk2:int128) (rk5:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x98) /\
          read Q0 s = b0 /\
          read Q2 s = b2 /\
          read Q4 s = q4_in /\
          read Q5 s = q5 /\
          read Q7 s = q7_pre /\
          read Q8 s = q8_pre /\
          read Q10 s = q10_pre /\
          read Q14 s = q14 /\
          read Q20 s = rk2 /\
          read Q23 s = rk5)
     (\s. read PC s = word (pc + 0xb8) /\
          read Q0 s = aes_arm_round b0 rk5 /\
          read Q2 s = aes_arm_round b2 rk2 /\
          read Q4 s = (word_pmul (word_subword q5 (64,64) :64 word)
                                 (word_subword q14 (64,64) :64 word)
                       :int128) /\
          read Q5 s = q5 /\
          read Q7 s = aes_gcm_rev64_int128 q7_pre /\
          read Q10 s = (word_pmul (word_subword (word_xor q4_in q8_pre:int128)
                                                (0,64) :64 word)
                                  (word_subword q10_pre (0,64) :64 word)
                        :int128) /\
          read Q14 s = q14 /\
          read Q20 s = rk2 /\
          read Q23 s = rk5)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q2; Q4; Q7; Q8; Q10] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (REWRITE_TAC[aes_gcm_rev64_int128] THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST) THEN
  TRY (ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-1-LOW cut: tracks block-1 LOW Karatsuba product       *)
(* Q8 = pmull(Q5, Q14), block-1 HIGH accumulation Q9 := Q9 ^ Q4, block-2    *)
(* PRE rev64 of Q6, and block-1 MID DUP_GEN Q4 = high(Q5).  Window: slice   *)
(* instr 47..54 (offsets 0x0b8..0x0d8).                                      *)
(*                                                                           *)
(* Window:                                                                   *)
(*   instr 47 (offset 0x0b8): arm_REV64_VEC Q6 Q6 8        ; blk-2 PRE      *)
(*   instr 48 (offset 0x0bc): arm_PMULL_VEC  Q8 Q5 Q14 64  ; blk-1 LOW     *)
(*   instr 49 (offset 0x0c0): arm_EOR_VEC    Q9 Q9 Q4 128  ; blk-1 HIGH acc*)
(*   instr 50 (offset 0x0c4): arm_DUP_GEN_FROM_ELEM Q4 Q5 64 64 1 ; blk-1 mid*)
(*   instr 51 (offset 0x0c8): arm_AESE       Q1 Q21       ; AES rd 3 blk 1 *)
(*   instr 52 (offset 0x0cc): arm_AESMC      Q1 Q1                          *)
(*   instr 53 (offset 0x0d0): arm_AESE       Q3 Q20       ; AES rd 2 blk 3 *)
(*   instr 54 (offset 0x0d4): arm_AESMC      Q3 Q3                          *)
(*                                                                           *)
(* Postcondition tracks:                                                     *)
(*   Q4 = word_zx (subword q5 (64,64)) — block-1 MID DUP_GEN (Q4 OVERWRITTEN) *)
(*   Q6 = aes_gcm_rev64_int128 q6_pre — block-2 PRE rev64                  *)
(*   Q8 = word_pmul (subword q5 (0,64)) (subword q14 (0,64)) — blk-1 LOW   *)
(*   Q9 = word_xor q9_pre q4_in — block-1 HIGH XOR accumulator              *)
(*                                                                           *)
(* AES round advances: Q1 → rk3 (was at rk2 after R5R3R2_3BLOCK), Q3 → rk2  *)
(* (was at rk1 from prior cuts).                                             *)
(*                                                                           *)
(* The closing tactic uses the same TRY chain as BLOCK0_MID_BLOCK1_HIGH:    *)
(* most conjuncts close via plain ASM_REWRITE_TAC; Q6 needs unfold +        *)
(* WORD_BLAST; Q9 (XOR commutativity simulator-side q4_in q9_pre vs.        *)
(* postcondition q9_pre q4_in) closes via WORD_BLAST after plain            *)
(* ASM_REWRITE_TAC peels everything else.                                    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK1_LOW_CORRECT = prove
 (`!pc (b1:int128) (b3:int128) (q5:int128) (q14:int128) (q6_pre:int128)
        (q9_pre:int128) (q4_in:int128) (rk2:int128) (rk3:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0xb8) /\
          read Q1 s = b1 /\
          read Q3 s = b3 /\
          read Q4 s = q4_in /\
          read Q5 s = q5 /\
          read Q6 s = q6_pre /\
          read Q9 s = q9_pre /\
          read Q14 s = q14 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3)
     (\s. read PC s = word (pc + 0xd8) /\
          read Q1 s = aes_arm_round b1 rk3 /\
          read Q3 s = aes_arm_round b3 rk2 /\
          read Q4 s = (word_zx (word_subword q5 (64,64) :64 word) :int128) /\
          read Q5 s = q5 /\
          read Q6 s = aes_gcm_rev64_int128 q6_pre /\
          read Q8 s = (word_pmul (word_subword q5 (0,64) :64 word)
                                 (word_subword q14 (0,64) :64 word)
                       :int128) /\
          read Q9 s = word_xor q9_pre q4_in /\
          read Q14 s = q14 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q1; Q3; Q4; Q6; Q8; Q9])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (REWRITE_TAC[aes_gcm_rev64_int128] THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH TAIL with Q11 value-tracking — instr 167..175.             *)
(*                                                                           *)
(* Window: slice instr 167..175 (offsets 0x298..0x2bc, 9 instructions) —    *)
(* same as the existing AES_GCM_MAIN_LOOP_BODY_TAIL_CORRECT cut but with    *)
(* full GHASH value tracking on Q11.                                        *)
(*                                                                           *)
(* Notable instruction in this window:                                      *)
(*   instr 172 (offset 0x2ac): arm_EOR_VEC Q11 Q11 Q10 128                  *)
(*                             ^ Q11 := q11_in XOR q10_in                   *)
(*                                    = v11_a XOR v10_swap                  *)
(*                                    = kernel_modulo h l m                 *)
(*                              (THE FINAL kernel_modulo result.)            *)
(*                                                                           *)
(* Postcondition tracks 1 GHASH write:                                       *)
(*   Q11 = q11_in XOR q10_in — final kernel_modulo result                   *)
(*                                                                           *)
(* Together with the prior MODULO chain cuts (BLOCK3_MID_AND_ACCUMS,        *)
(* MODULO_KARATSUBA, R9_FINAL_B0_B1_GHASH, FINAL_XOR_AND_CTR_GHASH,         *)
(* R9_FINAL_B2_B3_GHASH), composition of these 6 cuts produces              *)
(* `Q11 = kernel_modulo (q9_pre XOR blk3_high) (q11_pre XOR blk3_low)       *)
(*                       (q10_pre XOR blk3_mid)`.                           *)
(*                                                                           *)
(* Plus the two final ciphertext stores (Q6, Q7 after EOR with Q2, Q3)     *)
(* and Q2/Q3 CTR setup writes and X2 advancement.                           *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain.  Q11 closes via plain WORD_BLAST   *)
(* (XOR commutativity); other conjuncts close via plain ASM_REWRITE_TAC.    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_TAIL_GHASH_CORRECT = prove
 (`!pc (cptr:int64) (q2:int128) (q3:int128) (q10_in:int128) (q11_in:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x298) /\
              read X2 s = cptr /\
              read Q2 s = q2 /\
              read Q3 s = q3 /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 32) /\
              read Q10 s = q10_in /\
              read Q11 s = word_xor q11_in q10_in)
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q2; Q6; Q7; Q11] ,,
          MAYCHANGE [X2; X9; X12] ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16))] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH R9_FINAL_B2_B3 with Q10 and Q11 value-tracking — instr     *)
(* 157..166.                                                                 *)
(*                                                                           *)
(* Window: slice instr 157..166 (offsets 0x270..0x298, 10 instructions) —   *)
(* same as the existing AES_GCM_MAIN_LOOP_BODY_R9_FINAL_B2_B3_CORRECT cut   *)
(* but with full GHASH value tracking on Q10 and Q11.                       *)
(*                                                                           *)
(* Notable instructions in this window:                                      *)
(*   instr 161 (offset 0x280): arm_EOR_VEC Q11 Q11 Q9 128                   *)
(*                             ^ Q11 := q11_in XOR q9_in                    *)
(*                                    = v11_a in kernel_modulo notation     *)
(*                                    = l XOR v9_new                        *)
(*   instr 163 (offset 0x288): arm_EXT Q10 Q10 Q10 64                       *)
(*                             ^ Q10 := byteswap128 q10_in = v10_swap       *)
(*                                    (kernel_modulo's `byteswap128 v10_b`) *)
(*                                                                           *)
(* Postcondition tracks 2 GHASH writes:                                      *)
(*   Q10 = byteswap128 q10_in — kernel_modulo's `v10_swap`                  *)
(*   Q11 = q11_in XOR q9_in — kernel_modulo's `v11_a`                       *)
(*                                                                           *)
(* Plus AES round-9-final advances on Q2/Q3 and the two ciphertext stores   *)
(* (Q4, Q5 written to memory at cptr/cptr+16, X2 advances by 32).            *)
(*                                                                           *)
(* nonoverlapping precondition required for the simulator to discharge      *)
(* "stores will not modify the program code".                                *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain.  Q11 closes via plain WORD_BLAST   *)
(* (XOR commutativity); Q10 needs `REWRITE_TAC[byteswap128]` then            *)
(* WORD_BLAST.  AES conjuncts close via ASM_REWRITE after                   *)
(* AESE_AS_ARM_FINAL_ROUND.                                                  *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R9_FINAL_B2_B3_GHASH_CORRECT = prove
 (`!pc (cptr:int64) (b2:int128) (b3:int128) (q9_in:int128) (q10_in:int128)
        (q11_in:int128) (rk9:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x270) /\
              read X2 s = cptr /\
              read Q2 s = b2 /\
              read Q3 s = b3 /\
              read Q9 s = q9_in /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in /\
              read Q31 s = rk9)
         (\s. read PC s = word (pc + 0x298) /\
              read X2 s = word_add cptr (word 32) /\
              read Q2 s = aes_arm_final_round b2 rk9 /\
              read Q3 s = aes_arm_final_round b3 rk9 /\
              read Q9 s = q9_in /\
              read Q10 s = byteswap128 q10_in /\
              read Q11 s = word_xor q11_in q9_in /\
              read Q31 s = rk9)
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q2; Q3; Q7; Q10; Q11] ,,
          MAYCHANGE [X2; X9; X12] ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16))] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESE_AS_ARM_FINAL_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (REWRITE_TAC[byteswap128] THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC WORD_BLAST) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH FINAL_XOR_AND_CTR with Q9 value-tracking — instr 143..156. *)
(*                                                                           *)
(* Window: slice instr 143..156 (offsets 0x238..0x270, 14 instructions) —   *)
(* same as the existing AES_GCM_MAIN_LOOP_BODY_FINAL_XOR_AND_CTR_CORRECT cut*)
(* but with full GHASH value tracking on Q9 (the v9_new pmull result).      *)
(*                                                                           *)
(* Notable instruction in this window:                                      *)
(*   instr 147 (offset 0x248): arm_PMULL_VEC Q9 Q10 Q8 64                   *)
(*                             ^ Q9 := pmull(q10_in_lo, q8_in_lo)           *)
(*                                    = v9_new in kernel_modulo notation    *)
(*                              (Q10 holds v10_b from R9_FINAL_B0_B1; Q8    *)
(*                              still holds c64 = 0xc200000000000000 from   *)
(*                              MOVI/SHL in BLOCK3_MID_AND_ACCUMS.)          *)
(*                                                                           *)
(* Postcondition tracks 1 GHASH write:                                       *)
(*   Q9 = pmull(subword q10_in (0,64)) (subword q8_in (0,64))               *)
(*           — kernel_modulo's `v9_new = pmull(v10_b_lo, c64)`              *)
(*                                                                           *)
(* Other tracked registers: Q2, Q3, Q8, Q10, Q11 unchanged.                  *)
(*                                                                           *)
(* MAYCHANGE includes SOME_FLAGS for the SUBS ZR X0 X5 at instr 145.        *)
(* REWRITE_TAC[SOME_FLAGS] is applied before ENSURES_INIT_TAC per feedback   *)
(* memory `some_flags_no_canon.md`.                                          *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain.  All conjuncts close via plain     *)
(* ASM_REWRITE_TAC or WORD_BLAST.                                            *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_FINAL_XOR_AND_CTR_GHASH_CORRECT = prove
 (`!pc (q2:int128) (q3:int128) (q8_in:int128) (q10_in:int128) (q11_in:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x238) /\
          read Q2 s = q2 /\
          read Q3 s = q3 /\
          read Q8 s = q8_in /\
          read Q10 s = q10_in /\
          read Q11 s = q11_in)
     (\s. read PC s = word (pc + 0x270) /\
          read Q2 s = q2 /\
          read Q3 s = q3 /\
          read Q8 s = q8_in /\
          read Q9 s = (word_pmul (word_subword q10_in (0,64) :64 word)
                                 (word_subword q8_in (0,64) :64 word)
                       :int128) /\
          read Q10 s = q10_in /\
          read Q11 s = q11_in)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q4; Q5; Q6; Q9] ,,
      MAYCHANGE [X9; X12] ,,
      MAYCHANGE SOME_FLAGS)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH R9_FINAL_B0_B1 with Q10 value-tracking — instr 138..142.   *)
(*                                                                           *)
(* Window: slice instr 138..142 (offsets 0x224..0x238, 5 instructions) —    *)
(* same as the existing AES_GCM_MAIN_LOOP_BODY_R9_FINAL_B0_B1_CORRECT cut   *)
(* but with full GHASH value tracking on Q10.                                *)
(*                                                                           *)
(*   instr 138 (offset 0x224): arm_AESE Q0 Q31         ; round 9 final b0  *)
(*   instr 139 (offset 0x228): arm_FMOV_ItoF Q4 X7 1  (Q4 clobbered)        *)
(*   instr 140 (offset 0x22c): arm_EOR_VEC Q10 Q10 Q7 128                   *)
(*                             ^ Q10 := q10_in XOR q7_in                    *)
(*                                    = v10_a XOR v7_a = v10_b              *)
(*                               (in kernel_modulo's notation)               *)
(*   instr 141 (offset 0x230): arm_FMOV_ItoF Q7 X23 0 (Q7 clobbered)        *)
(*   instr 142 (offset 0x234): arm_AESE Q1 Q31         ; round 9 final b1  *)
(*                                                                           *)
(* Postcondition tracks 1 GHASH write:                                       *)
(*   Q10 = q10_in XOR q7_in — kernel_modulo's `v10_b = v10_a XOR v7_a`     *)
(*                                                                           *)
(* Plus AES round-9-final advances on Q0/Q1.                                 *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain.  Q10 closes via plain WORD_BLAST   *)
(* (XOR commutativity); AES conjuncts close via ASM_REWRITE_TAC after       *)
(* AESE_AS_ARM_FINAL_ROUND folding.                                         *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_R9_FINAL_B0_B1_GHASH_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (q7_in:int128) (q10_in:int128) (rk9:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x224) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q7 s = q7_in /\
          read Q10 s = q10_in /\
          read Q31 s = rk9)
     (\s. read PC s = word (pc + 0x238) /\
          read Q0 s = aes_arm_final_round b0 rk9 /\
          read Q1 s = aes_arm_final_round b1 rk9 /\
          read Q10 s = word_xor q10_in q7_in /\
          read Q31 s = rk9)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q4; Q7; Q10])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESE_AS_ARM_FINAL_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-MODULO-Karatsuba-tidy + h/c64-pmull + h byteswap.           *)
(*                                                                           *)
(* Window: slice instr 124..137 (offsets 0x1ec..0x224, 14 instructions) — a *)
(* MIDDLE portion of the existing GHASH_MODULO_CORRECT cut, with full       *)
(* value tracking on Q7/Q9/Q10.  This is the kernel_modulo's "v4 = l ^ h"  *)
(* / "v7 = pmull(h, c64)" / "h_swap = byteswap128 h" / "v10_a = m ^ v4"    *)
(* / "v7_a = h_swap ^ v7" sub-chain — naming the intermediate values       *)
(* exactly as `kernel_modulo` does in `aes_gcm_bridge.ml:344`.              *)
(*                                                                           *)
(*   instr 124 (offset 0x1ec): arm_EOR_VEC Q4 Q11 Q9 128                    *)
(*                             ^ Q4 := q11_in XOR q9_in (= v4 = l ^ h)      *)
(*   instr 125 (offset 0x1f0): arm_ADD X0 X0 #64                            *)
(*   instr 126 (offset 0x1f4): arm_PMULL_VEC Q7 Q9 Q8 64                    *)
(*                             ^ Q7 := pmull(q9_in_lo, q8_in_lo) (= v7)     *)
(*   instr 127 (offset 0x1f8): arm_REV W9 W12                               *)
(*   instr 128 (offset 0x1fc): arm_EXT Q9 Q9 Q9 64                          *)
(*                             ^ Q9 := byteswap128 q9_in (= h_swap)         *)
(*                               (note: ext v.16b, v.16b, v.16b, #8 on the *)
(*                               same operand swaps the two 64-bit halves, *)
(*                               which is exactly byteswap128 for a value)  *)
(*   instr 129 (offset 0x200): arm_EOR X6 X6 X13                            *)
(*   instr 130 (offset 0x204): arm_EOR_VEC Q10 Q10 Q4 128                   *)
(*                             ^ Q10 := q10_in XOR (q11_in XOR q9_in)       *)
(*                                    = v10_a (kernel_modulo)               *)
(*   instr 131 (offset 0x208): arm_EOR X7 X7 X14                            *)
(*   instr 132 (offset 0x20c): arm_FMOV_ItoF Q4 X6 0  (Q4 clobbered)        *)
(*   instr 133 (offset 0x210): arm_ORR X9 X11 (X9 LSL 32)                   *)
(*   instr 134 (offset 0x214): arm_EOR_VEC Q7 Q9 Q7 128                     *)
(*                             ^ Q7 := byteswap128(q9_in) XOR pmull(...)   *)
(*                                    = v7_a (kernel_modulo)                *)
(*   instr 135 (offset 0x218): arm_EOR X20 X20 X14                          *)
(*   instr 136 (offset 0x21c): arm_EOR X24 X24 X14                          *)
(*   instr 137 (offset 0x220): arm_ADD W12 W12 #1                           *)
(*                                                                           *)
(* Postcondition tracks 5 GHASH writes:                                      *)
(*   Q7  = byteswap128 q9_in XOR pmull(q9_in_lo, q8_in_lo)                 *)
(*           — kernel_modulo's `v7_a = h_swap XOR v7`                       *)
(*   Q8  = q8_in (unchanged)                                                 *)
(*   Q9  = byteswap128 q9_in — kernel_modulo's `h_swap`                     *)
(*   Q10 = q10_in XOR (q11_in XOR q9_in) — kernel_modulo's `v10_a`         *)
(*   Q11 = q11_in (unchanged after blk-3 LOW accum at instr 121)            *)
(*                                                                           *)
(* MAYCHANGE includes [events] (no memory event in this window — instr      *)
(* 119's LDP is OUTSIDE this window — but kept for safety on the X0 ADD    *)
(* and other scalar ops).  Note also no MAYCHANGE on [events] is needed    *)
(* since this window has no memory events — but the existing               *)
(* GHASH_MODULO_CORRECT lists [events] in its MAYCHANGE; aligning here      *)
(* avoids subsumption gymnastics in composition.                             *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain.  Q9 is `byteswap128 q9_in` —      *)
(* needs `REWRITE_TAC[byteswap128]` to unfold, then ASM_REWRITE +           *)
(* WORD_BLAST closes (the kernel's `ext` on a single-operand v.16b is       *)
(* exactly the byteswap128 = swap-halves operation modulo word_subword     *)
(* algebra).  Other XOR-commutativity conjuncts close via plain WORD_BLAST. *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_MODULO_KARATSUBA_CORRECT = prove
 (`!pc (q8_in:int128) (q9_in:int128) (q10_in:int128) (q11_in:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x1ec) /\
          read Q8 s = q8_in /\
          read Q9 s = q9_in /\
          read Q10 s = q10_in /\
          read Q11 s = q11_in)
     (\s. read PC s = word (pc + 0x224) /\
          read Q7 s = word_xor (byteswap128 q9_in)
                          (word_pmul (word_subword q9_in (0,64) :64 word)
                                     (word_subword q8_in (0,64) :64 word)
                            :int128) /\
          read Q8 s = q8_in /\
          read Q9 s = byteswap128 q9_in /\
          read Q10 s = word_xor q10_in (word_xor q11_in q9_in) /\
          read Q11 s = q11_in)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q4; Q7; Q9; Q10] ,,
      MAYCHANGE [X0; X6; X7; X9; X12; X20; X24] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REWRITE_TAC[byteswap128] THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC WORD_BLAST) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-3-MID pmull + block-3 HIGH/LOW/MID XOR accumulators  *)
(* + Q8 movi/shl + Q5 fmov-CTR-clobber.                                      *)
(*                                                                           *)
(* Window: slice instr 115..122 (offsets 0x1c8..0x1e8, 8 instructions) — a  *)
(* PREFIX of the existing AES_GCM_MAIN_LOOP_BODY_GHASH_MODULO_CORRECT cut,  *)
(* with FULL value tracking on Q4/Q9/Q10/Q11.  This is the "pre-Karatsuba- *)
(* tidy" portion of the MODULO chain: after this window, the kernel has    *)
(* finished accumulating the per-block contributions into Q9/Q10/Q11 but   *)
(* has not yet started the c64-pmull reduction (`v4 := l XOR h`).           *)
(*                                                                           *)
(*   instr 115 (offset 0x1c8): arm_MOVI Q8 (...0xc2 in low 8 bits...)        *)
(*   instr 116 (offset 0x1cc): arm_PMULL_VEC Q4 Q4 Q16 64                   *)
(*                             ^ Q4 := pmull(q4_in_lo, q16_lo) — blk-3 MID *)
(*   instr 117 (offset 0x1d0): arm_EOR_VEC Q9 Q9 Q5 128                     *)
(*                             ^ Q9 := q9_in XOR q5 — blk-3 HIGH accum     *)
(*   instr 118 (offset 0x1d4): arm_FMOV_ItoF Q5 X19 0  (Q5 clobbered)       *)
(*   instr 119 (offset 0x1d8): arm_LDP X6 X7 X0 #0     (memory event)       *)
(*   instr 120 (offset 0x1dc): arm_SHL_VEC Q8 Q8 56 64 64                   *)
(*   instr 121 (offset 0x1e0): arm_EOR_VEC Q11 Q11 Q6 128                   *)
(*                             ^ Q11 := q11_in XOR q6 — blk-3 LOW accum    *)
(*   instr 122 (offset 0x1e4): arm_EOR_VEC Q10 Q10 Q4 128                   *)
(*                             ^ Q10 := q10_in XOR Q4_just_set              *)
(*                                    = q10_in XOR pmull(q4_in_lo, q16_lo)  *)
(*                             — blk-3 MID accum (using Q4 = blk-3 MID)    *)
(*                                                                           *)
(* Postcondition tracks 4 GHASH writes:                                      *)
(*   Q4 = pmull(subword q4_in (0,64)) (subword q16 (0,64)) — blk-3 MID    *)
(*   Q9 = q9_in XOR q5 — block-3 HIGH XOR accumulator                       *)
(*   Q10 = q10_in XOR pmull(q4_in_lo, q16_lo) — block-3 MID accumulator    *)
(*         (using NEW Q4 from instr 116)                                    *)
(*   Q11 = q11_in XOR q6 — block-3 LOW XOR accumulator                      *)
(*                                                                           *)
(* MAYCHANGE includes [events] to absorb the LDP X6 X7 X0 memory event;    *)
(* X6/X7 also clobbered by the LDP.  Q5 and Q8 land in MAYCHANGE without    *)
(* value tracking (Q5 := word_zx X19 from FMOV; Q8 := shifted MOVI const).  *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + plain WORD_BLAST.  All 4 conjuncts are        *)
(* opaque-pmull-friendly XOR-commutativity; no AP_THM_TAC needed.            *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK3_MID_AND_ACCUMS_CORRECT = prove
 (`!pc (q4_in:int128) (q5:int128) (q6:int128) (q9_in:int128)
        (q10_in:int128) (q11_in:int128) (q16:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x1c8) /\
          read Q4 s = q4_in /\
          read Q5 s = q5 /\
          read Q6 s = q6 /\
          read Q9 s = q9_in /\
          read Q10 s = q10_in /\
          read Q11 s = q11_in /\
          read Q16 s = q16)
     (\s. read PC s = word (pc + 0x1e8) /\
          read Q4 s = (word_pmul (word_subword q4_in (0,64) :64 word)
                                 (word_subword q16 (0,64) :64 word)
                       :int128) /\
          read Q9 s = word_xor q9_in q5 /\
          read Q10 s = word_xor q10_in
                          (word_pmul (word_subword q4_in (0,64) :64 word)
                                     (word_subword q16 (0,64) :64 word)
                            :int128) /\
          read Q11 s = word_xor q11_in q6 /\
          read Q16 s = q16)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q4; Q5; Q8; Q9; Q10; Q11] ,,
      MAYCHANGE [X6; X7] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-2-MID accumulator (Q10 ^= Q8) cut.                    *)
(*                                                                           *)
(* Window: slice instr 106..114 (offsets 0x1a4..0x1c8, 9 instructions) —    *)
(* same as the existing AES_GCM_MAIN_LOOP_BODY_R8_B2_R7R8_B3_CORRECT cut    *)
(* but with full GHASH value tracking on Q10.                                *)
(*                                                                           *)
(*   instr 106 (offset 0x1a4): arm_EOR X19 X19 X13   ; AES blk 4k+5 round N  *)
(*   instr 107 (offset 0x1a8): arm_AESE Q2 Q26       ; AES rd 8 b2          *)
(*   instr 108 (offset 0x1ac): arm_AESMC Q2 Q2                               *)
(*   instr 109 (offset 0x1b0): arm_EOR_VEC Q10 Q10 Q8 128 ; blk-2 MID accum *)
(*                             ^ Q10 ^= Q8 (using Q8 from BLOCK1_MID exit:  *)
(*                               Q8 = word_zx (xor q6_lo q6_hi))             *)
(*   instr 110 (offset 0x1b4): arm_AESE Q3 Q25       ; AES rd 7 b3          *)
(*   instr 111 (offset 0x1b8): arm_AESMC Q3 Q3                               *)
(*   instr 112 (offset 0x1bc): arm_EOR X21 X21 X13   ; AES blk 4k+6 round N  *)
(*   instr 113 (offset 0x1c0): arm_AESE Q3 Q26       ; AES rd 8 b3          *)
(*   instr 114 (offset 0x1c4): arm_AESMC Q3 Q3                               *)
(*                                                                           *)
(* Postcondition: Q10 = q10_in XOR q8_in (block-2 MID XOR accumulator).      *)
(* AES round advances: Q2 → rk8 (one round), Q3 → rk7 → rk8 (two rounds).    *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain; the only non-trivial conjunct is    *)
(* Q10 (XOR-commutativity simulator-side q8_in q10_in vs. postcondition      *)
(* q10_in q8_in) which closes via plain CONV_TAC WORD_BLAST.                 *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK2_MID_ACCUM_CORRECT = prove
 (`!pc (b2:int128) (b3:int128) (q8_in:int128) (q10_in:int128)
        (rk6:int128) (rk7:int128) (rk8:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x1a4) /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q8 s = q8_in /\
          read Q10 s = q10_in /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (\s. read PC s = word (pc + 0x1c8) /\
          read Q2 s = aes_arm_round b2 rk8 /\
          read Q3 s = aes_arm_round (aes_arm_round b3 rk7) rk8 /\
          read Q8 s = q8_in /\
          read Q10 s = word_xor q10_in q8_in /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q2; Q3; Q10] ,,
      MAYCHANGE [X19; X21])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-1-MID pmull cut + block-2-MID DUP_GEN/prep + Q11      *)
(* block-1-LOW XOR accumulator.                                              *)
(*                                                                           *)
(* Window: slice instr 55..71 (offsets 0x0d8..0x11c, 17 instructions).      *)
(* Picks up where BLOCK1_LOW ended (Q4 had been overwritten with             *)
(* `word_zx (subword q5 (64,64))` by the DUP_GEN at slice instr 50, but     *)
(* this cut takes Q4 as uninterpreted `q4_in` — caller threading binds      *)
(* it to the BLOCK1_LOW exit value).                                         *)
(*                                                                           *)
(*   instr 55 (offset 0x0d8): arm_EOR_VEC      Q11 Q11 Q8 128 ; blk-1 LOW   *)
(*                            ^ Q11 ^= Q8 (using OLD Q8 = blk-1 LOW pmull)  *)
(*   instr 56 (offset 0x0dc): arm_AESE         Q2 Q21        ; AES rd 3 b2  *)
(*   instr 57 (offset 0x0e0): arm_AESMC        Q2 Q2                         *)
(*   instr 58 (offset 0x0e4): arm_AESE         Q1 Q22        ; AES rd 4 b1  *)
(*   instr 59 (offset 0x0e8): arm_AESMC        Q1 Q1                         *)
(*   instr 60 (offset 0x0ec): arm_DUP_GEN_FROM_ELEM Q8 Q6 64 64 1            *)
(*                            ^ Q8 := word_zx (subword q6 (64,64))           *)
(*   instr 61 (offset 0x0f0): arm_AESE         Q3 Q21        ; AES rd 3 b3  *)
(*   instr 62 (offset 0x0f4): arm_AESMC        Q3 Q3                         *)
(*   instr 63 (offset 0x0f8): arm_EOR_VEC      Q4 Q4 Q5 64                   *)
(*                            ^ Q4 := word_zx (subword (xor Q4 Q5) (0,64))  *)
(*                              (Q4 = OLD q4_in here)                        *)
(*   instr 64 (offset 0x0fc): arm_AESE         Q2 Q22        ; AES rd 4 b2  *)
(*   instr 65 (offset 0x100): arm_AESMC        Q2 Q2                         *)
(*   instr 66 (offset 0x104): arm_AESE         Q0 Q24        ; AES rd 6 b0  *)
(*   instr 67 (offset 0x108): arm_AESMC        Q0 Q0                         *)
(*   instr 68 (offset 0x10c): arm_EOR_VEC      Q8 Q8 Q6 64                   *)
(*                            ^ Q8 := word_zx (subword (xor Q8 Q6) (0,64))  *)
(*                                  = word_zx (xor q6_lo q6_hi)              *)
(*   instr 69 (offset 0x110): arm_AESE         Q3 Q22        ; AES rd 4 b3  *)
(*   instr 70 (offset 0x114): arm_AESMC        Q3 Q3                         *)
(*   instr 71 (offset 0x118): arm_PMULL_VEC    Q4 Q4 Q17 64  ; blk-1 MID    *)
(*                            ^ Q4 := pmull(Q4_lo, Q17_lo)                  *)
(*                              with Q4 = (OLD q4_in XOR q5) low half       *)
(*                                                                           *)
(* Postcondition tracks 3 GHASH writes:                                      *)
(*   Q4  = pmull(subword (xor q4_in q5) (0,64))                              *)
(*               (subword q17 (0,64)) — blk-1 MID Karatsuba product         *)
(*   Q8  = word_zx (xor (subword q6 (0,64)) (subword q6 (64,64)))            *)
(*               — blk-2 MID prep (low XOR high of q6)                       *)
(*   Q11 = q11_in XOR q8_in — blk-1 LOW XOR accumulator (using OLD Q8)      *)
(*                                                                           *)
(* AES round advances: Q0 → rk6 (one round), Q1 → rk4 (one round),          *)
(* Q2 → rk3 → rk4 (two rounds), Q3 → rk3 → rk4 (two rounds).                 *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain.  Q4 needs                          *)
(* `AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BLAST` to peel the        *)
(* opaque `word_pmul` operator and let WORD_BLAST attack the subword/        *)
(* word_zx folding.  Q8 closes via plain CONV_TAC WORD_BLAST.  Q11           *)
(* (XOR commutativity simulator-side q8_in q11_in vs. postcondition          *)
(* q11_in q8_in) closes via plain CONV_TAC WORD_BLAST.                       *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK1_MID_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128)
        (q4_in:int128) (q5:int128) (q6:int128) (q8_in:int128)
        (q11_in:int128) (q17:int128)
        (rk3:int128) (rk4:int128) (rk6:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0xd8) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q4 s = q4_in /\
          read Q5 s = q5 /\
          read Q6 s = q6 /\
          read Q8 s = q8_in /\
          read Q11 s = q11_in /\
          read Q17 s = q17 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q24 s = rk6)
     (\s. read PC s = word (pc + 0x11c) /\
          read Q0 s = aes_arm_round b0 rk6 /\
          read Q1 s = aes_arm_round b1 rk4 /\
          read Q2 s = aes_arm_round (aes_arm_round b2 rk3) rk4 /\
          read Q3 s = aes_arm_round (aes_arm_round b3 rk3) rk4 /\
          read Q4 s = (word_pmul (word_subword (word_xor q4_in q5:int128)
                                               (0,64) :64 word)
                                 (word_subword q17 (0,64) :64 word)
                       :int128) /\
          read Q5 s = q5 /\
          read Q6 s = q6 /\
          read Q8 s = (word_zx (word_xor (word_subword q6 (0,64) :64 word)
                                         (word_subword q6 (64,64) :64 word)
                                :64 word)
                       :int128) /\
          read Q11 s = word_xor q11_in q8_in /\
          read Q17 s = q17 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q24 s = rk6)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q8; Q11])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BLAST) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-AES-only gap cut covering offsets 0x11c..0x150              *)
(* (slice instr 72..84, 13 instructions).                                    *)
(*                                                                           *)
(* Bridges between BLOCK1_MID (which exits at 0x11c) and                     *)
(* BLOCK2_HL_BLOCK3_L (which enters at 0x150).  This window is mostly       *)
(* AES rounds for blocks 0..3 plus a single `ins v8.d[1], v8.d[0]` at        *)
(* offset 0x434 (instr 76, slice offset 0x134) — pure AES + Q8 internal     *)
(* rearrangement.                                                            *)
(*                                                                           *)
(* No GHASH value tracking is needed in this gap — Q4/Q11 are preserved     *)
(* (their values from BLOCK1_MID's exit propagate unchanged), Q8 is in       *)
(* MAYCHANGE (the INS instruction overwrites it with a derived form).        *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_GAP_AES_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128) (b3:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128)
        (q4_in:int128) (q8_in:int128) (q11_in:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x11c) /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q3 s = b3 /\
          read Q4 s = q4_in /\
          read Q8 s = q8_in /\
          read Q11 s = q11_in /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (\s. read PC s = word (pc + 0x150) /\
          read Q0 s = aes_arm_round (aes_arm_round b0 rk7) rk8 /\
          read Q1 s = aes_arm_round (aes_arm_round b1 rk5) rk6 /\
          read Q2 s = aes_arm_round b2 rk5 /\
          read Q3 s = aes_arm_round b3 rk5 /\
          read Q4 s = q4_in /\
          read Q8 s = (word_insert q8_in (64,64)
                        (word_subword (word_subword q8_in (0,64) :64 word)
                                      (0,64) :64 word) :int128) /\
          read Q11 s = q11_in /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q8])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--13) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-2-HIGH+LOW + block-3-LOW + EOR-accumulators cut.     *)
(*                                                                           *)
(* Window: slice instr 85..93 (offsets 0x150..0x174, 9 instructions) — same *)
(* as the existing AES_GCM_MAIN_LOOP_BODY_R7R6_BLOCK1_BLOCK3_CORRECT cut    *)
(* but with full GHASH value tracking on Q4/Q5/Q6/Q9/Q10.                   *)
(*                                                                           *)
(*   instr 85 (offset 0x150): arm_EOR_VEC      Q10 Q10 Q4 128                *)
(*   instr 86 (offset 0x154): arm_PMULL2_VEC   Q4 Q6 Q13 64    ; blk-2 HIGH *)
(*   instr 87 (offset 0x158): arm_PMULL_VEC    Q5 Q6 Q13 64    ; blk-2 LOW  *)
(*   instr 88 (offset 0x15c): arm_AESE         Q1 Q25          ; AES rd 7 b1*)
(*   instr 89 (offset 0x160): arm_AESMC        Q1 Q1                         *)
(*   instr 90 (offset 0x164): arm_PMULL_VEC    Q6 Q7 Q12 64    ; blk-3 LOW  *)
(*   instr 91 (offset 0x168): arm_EOR_VEC      Q9 Q9 Q4 128                  *)
(*   instr 92 (offset 0x16c): arm_AESE         Q3 Q24          ; AES rd 6 b3*)
(*   instr 93 (offset 0x170): arm_AESMC        Q3 Q3                         *)
(*                                                                           *)
(* IMPORTANT — Q4 chain across this window:                                  *)
(*   - Enters as `q4_in` (block-1 MID pmull product from earlier cut)        *)
(*   - Consumed by EOR Q10 ^= Q4 at instr 85 (using OLD q4_in)               *)
(*   - Overwritten by PMULL2 Q4 = Q6_HI * Q13_HI at instr 86 (block-2 HIGH) *)
(*   - Consumed by EOR Q9 ^= Q4 at instr 91 (using NEW Q4 = block-2 HIGH)   *)
(*                                                                           *)
(* Postcondition tracks 5 GHASH writes:                                      *)
(*   Q4 = pmull (subword q6 (64,64)) (subword q13 (64,64)) — blk-2 HIGH    *)
(*   Q5 = pmull (subword q6 (0,64))  (subword q13 (0,64))  — blk-2 LOW     *)
(*   Q6 = pmull (subword q7 (0,64))  (subword q12 (0,64))  — blk-3 LOW     *)
(*   Q9 = q9_pre ^ Q4_new (blk-2 HIGH accumulator using NEW Q4)             *)
(*  Q10 = q10_pre ^ q4_in (blk-1 MID accumulator using OLD Q4)              *)
(*                                                                           *)
(* Plus AES round advances: Q1 → rk7, Q3 → rk6.                              *)
(*                                                                           *)
(* Closing: REPEAT CONJ_TAC + TRY chain.  Most conjuncts close via plain    *)
(* ASM_REWRITE_TAC; the two XOR-commutativity conjuncts (Q9 simulator       *)
(* emits xor pmull q9_pre, postcondition has xor q9_pre pmull; Q10          *)
(* simulator emits xor q4_in q10_pre, postcondition has xor q10_pre q4_in)  *)
(* close via plain CONV_TAC WORD_BLAST.                                      *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK2_HL_BLOCK3_L_CORRECT = prove
 (`!pc (b1:int128) (b3:int128) (q6:int128) (q7:int128)
        (q12:int128) (q13:int128) (q9_pre:int128) (q10_pre:int128)
        (q4_in:int128) (rk6:int128) (rk7:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x150) /\
          read Q1 s = b1 /\
          read Q3 s = b3 /\
          read Q4 s = q4_in /\
          read Q6 s = q6 /\
          read Q7 s = q7 /\
          read Q9 s = q9_pre /\
          read Q10 s = q10_pre /\
          read Q12 s = q12 /\
          read Q13 s = q13 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7)
     (\s. read PC s = word (pc + 0x174) /\
          read Q1 s = aes_arm_round b1 rk7 /\
          read Q3 s = aes_arm_round b3 rk6 /\
          read Q4 s = (word_pmul (word_subword q6 (64,64) :64 word)
                                 (word_subword q13 (64,64) :64 word)
                       :int128) /\
          read Q5 s = (word_pmul (word_subword q6 (0,64) :64 word)
                                 (word_subword q13 (0,64) :64 word)
                       :int128) /\
          read Q6 s = (word_pmul (word_subword q7 (0,64) :64 word)
                                 (word_subword q12 (0,64) :64 word)
                       :int128) /\
          read Q9 s = word_xor q9_pre
                       (word_pmul (word_subword q6 (64,64) :64 word)
                                  (word_subword q13 (64,64) :64 word)
                        :int128) /\
          read Q10 s = word_xor q10_pre q4_in /\
          read Q12 s = q12 /\
          read Q13 s = q13 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q1; Q3; Q4; Q5; Q6; Q9; Q10])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH-block-2-MID + block-3-HIGH + block-1-LOW-accum cut.        *)
(*                                                                           *)
(* Window: slice instr 94..105 (offsets 0x174..0x1a4, 12 instructions),    *)
(* same as the existing AES_GCM_MAIN_LOOP_BODY_R8R7_LDP_CORRECT but with   *)
(* full GHASH value tracking on Q5/Q8/Q11.                                  *)
(*                                                                           *)
(*   instr 94  (offset 0x174): arm_LDP X19 X20 X0 #16   ; AES blk 4k+5 plt  *)
(*   instr 95  (offset 0x178): arm_AESE Q1 Q26          ; AES rd 8 blk 1   *)
(*   instr 96  (offset 0x17c): arm_AESMC Q1 Q1                              *)
(*   instr 97  (offset 0x180): arm_DUP_GEN_FROM_ELEM Q4 Q7 64 64 1 ; blk-3 mid prep*)
(*   instr 98  (offset 0x184): arm_AESE Q2 Q24          ; AES rd 6 blk 2   *)
(*   instr 99  (offset 0x188): arm_AESMC Q2 Q2                              *)
(*   instr 100 (offset 0x18c): arm_EOR_VEC Q11 Q11 Q5 128 ; blk-2 LOW accum *)
(*   instr 101 (offset 0x190): arm_PMULL2_VEC Q8 Q8 Q16 ; blk-2 MID         *)
(*   instr 102 (offset 0x194): arm_PMULL2_VEC Q5 Q7 Q12 ; blk-3 HIGH        *)
(*   instr 103 (offset 0x198): arm_EOR_VEC Q4 Q4 Q7 64  ; blk-3 mid prep   *)
(*   instr 104 (offset 0x19c): arm_AESE Q2 Q25          ; AES rd 7 blk 2   *)
(*   instr 105 (offset 0x1a0): arm_AESMC Q2 Q2                              *)
(*                                                                           *)
(* IMPORTANT — Q5 chain:                                                     *)
(*   - Enters as `q5_in` (from prior cut: blk-2 LOW pmull product)          *)
(*   - Consumed by EOR Q11 ^= Q5 at instr 100 (using OLD q5_in)             *)
(*   - Overwritten by PMULL2 Q5 = Q7_HI * Q12_HI at instr 102 (blk-3 HIGH) *)
(*                                                                           *)
(* Postcondition tracks 3 GHASH writes:                                      *)
(*   Q5 = pmull (subword q7 (64,64)) (subword q12 (64,64)) — blk-3 HIGH    *)
(*   Q8 = pmull (subword q8_in (64,64)) (subword q16 (64,64)) — blk-2 MID  *)
(*  Q11 = q11_in XOR q5_in (blk-2 LOW XOR accumulator, OLD Q5)              *)
(*                                                                           *)
(* Plus AES round advances: Q1 → rk8, Q2 → rk6 → rk7 (2-round advance),    *)
(* and the LDP X19, X20.  Q4 (DUP_GEN + EOR) sits in MAYCHANGE without     *)
(* value tracking — its block-3 mid value depends on q7 only and can be    *)
(* tracked in the next cut.                                                  *)
(*                                                                           *)
(* Closes via the standard TRY chain.                                        *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK2_MID_BLOCK3_HIGH_CORRECT = prove
 (`!pc (b1:int128) (b2:int128) (q5_in:int128) (q7:int128) (q8_in:int128)
        (q11_in:int128) (q12:int128) (q16:int128)
        (rk6:int128) (rk7:int128) (rk8:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word (pc + 0x174) /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q5 s = q5_in /\
          read Q7 s = q7 /\
          read Q8 s = q8_in /\
          read Q11 s = q11_in /\
          read Q12 s = q12 /\
          read Q16 s = q16 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (\s. read PC s = word (pc + 0x1a4) /\
          read Q1 s = aes_arm_round b1 rk8 /\
          read Q2 s = aes_arm_round (aes_arm_round b2 rk6) rk7 /\
          read Q4 s = (word_zx (word_subword
                         (word_xor q7
                            (word_zx (word_subword q7 (64,64) :64 word)
                             :int128))
                         (0,64) :64 word) :int128) /\
          read Q5 s = (word_pmul (word_subword q7 (64,64) :64 word)
                                 (word_subword q12 (64,64) :64 word)
                       :int128) /\
          read Q7 s = q7 /\
          read Q8 s = (word_pmul (word_subword q8_in (64,64) :64 word)
                                 (word_subword q16 (64,64) :64 word)
                       :int128) /\
          read Q11 s = word_xor q11_in q5_in /\
          read Q12 s = q12 /\
          read Q16 s = q16 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q1; Q2; Q4; Q5; Q8; Q11] ,,
      MAYCHANGE [X19; X20] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  TRY (CONV_TAC WORD_BLAST));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 FULL BODY composition cut: all 175 instructions.                  *)
(*                                                                           *)
(* Composes the full 17-cut chain (R0_BLOCKS012 through TAIL) into a single *)
(* `ensures arm` over the entire body slice (offsets 0..0x2bc).             *)
(*                                                                           *)
(* This cut intentionally has a *minimal* postcondition: only the           *)
(* preserved round keys (Q18..Q26, Q31), plus the advanced PC and cptr.    *)
(* The Q0..Q3 (cipher state), Q4..Q11 (GHASH state) and X registers all    *)
(* sit in MAYCHANGE without value-tracking.  This is the right shape for    *)
(* compositions that *don't* need to express the AES outputs algebraically *)
(* — e.g. when the loop wrapper only needs to know the round keys are     *)
(* preserved across the iteration and ciphertext memory got written.        *)
(*                                                                           *)
(* For a value-tracking composition that asserts each block's final         *)
(* ciphertext = `aes_arm_final_round (aes_arm_round^9 b_i [rk0..rk8]) rk9   *)
(* XOR plaintext_i`, see AES_GCM_MAIN_LOOP_BODY_AES_8ROUNDS_CORRECT for     *)
(* the partial form (ends at round 8, no XOR-with-plaintext or stores).    *)
(*                                                                           *)
(* The closing tactic combines AESMC_AESE_AS_ARM_ROUND (rounds 0..8) and   *)
(* AESE_AS_ARM_FINAL_ROUND (round 9) in one ASM_REWRITE_TAC pass.           *)
(* SOME_FLAGS is unfolded before STRIP_TAC for the SUBS instruction at     *)
(* offset 0x240.  cptr nonoverlap ensures the four STR Q4..Q7 stores at   *)
(* offsets 0x278/0x28c/0x2a0/0x2b8 don't smash the program text.            *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_FULL_AES_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128) (b11:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word pc /\
              read X2 s = cptr /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q11 s = b11 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 64) /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9)
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                     Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12;
                     X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--175) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AESMC_AESE_AS_ARM_ROUND; AESE_AS_ARM_FINAL_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH composition cut: full kernel_modulo over offsets             *)
(* 0x1c8..0x2bc (61 instructions, slice instr 115..175).  Composes the         *)
(* 6 sequential per-component cuts BLOCK3_MID_AND_ACCUMS through TAIL_GHASH   *)
(* into a single ensures whose Q11 postcondition is in spec form              *)
(* `kernel_modulo` (`aes_gcm_bridge.ml:344`).                                 *)
(*                                                                            *)
(* The cut starts at slice offset 0x1c8 (kernel pc + 0x308 + 0x1c8 = pc +    *)
(* 0x4d0) which is BEFORE the kernel's `MOVI Q8 #0xc2 / SHL D8, D8, #56`     *)
(* that builds Q8 := word 0xC200000000000000 (kernel_modulo's c64 const).   *)
(* This means the cut window absorbs the c64 constant construction so the    *)
(* postcondition can refer to `kernel_modulo` directly without exposing Q8   *)
(* as an explicit precondition.                                              *)
(*                                                                            *)
(* Postcondition Q11 = `kernel_modulo (q9_in XOR q5) (q11_in XOR q6)         *)
(*                                    (q10_in XOR pmull(q4_in_lo,q16_lo))`.  *)
(* The kernel_modulo's three arguments are the per-block-3-accumulated       *)
(* HIGH/LOW/MID Karatsuba accumulators:                                       *)
(*   - h_in = q9_in XOR q5  (kernel's Q9 ^= Q5 at instr 117 = blk-3 HIGH)   *)
(*   - l_in = q11_in XOR q6 (kernel's Q11 ^= Q6 at instr 121 = blk-3 LOW)   *)
(*   - m_in = q10_in XOR pmull(q4_in_lo,q16_lo)                             *)
(*           (kernel's Q10 ^= NEW Q4 at instr 122 where NEW Q4 = block-3   *)
(*           MID Karatsuba product from PMULL Q4 Q4 Q16 at instr 116)      *)
(*                                                                            *)
(* Discharge strategy (exhibits brute-force composition + ABBREV-driven     *)
(* WORD_RULE close):                                                         *)
(*   1. Brute-force ARM_STEPS_TAC (1--61) over the union range — wall-clock *)
(*      ~3 seconds.  Per memory `brute_force_composition.md`.                *)
(*   2. ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC produces a pure word-     *)
(*      level equation between simulator's Q11 form and kernel_modulo.       *)
(*   3. REWRITE_TAC[kernel_modulo; byteswap128; LET_DEF; LET_END_DEF] to    *)
(*      unfold both sides.                                                  *)
(*   4. Discharge a one-step lemma `subword(join h h, (64,128)) =           *)
(*      join(subword(h,0,64), subword(h,64,64))` and use ASM_REWRITE_TAC    *)
(*      to align the LHS's `subword(join h h)` form with the RHS's          *)
(*      `join(subword,subword)` form.                                       *)
(*   5. ABBREV_TAC the c64-pmul atom Pinner, the kernel's per-block-3       *)
(*      Pmid atom, the input XOR sums Hxor/Lxor, the byteswapped form       *)
(*      Bswapped, and the inner XOR sum Inner — reducing both sides to       *)
(*      a goal of <300 chars in pure XOR/word_join/word_subword/word_pmul   *)
(*      atoms.                                                               *)
(*   6. SUBGOAL_THEN normalises the RHS's inner XOR sum's association to    *)
(*      match Inner via WORD_RULE.                                          *)
(*   7. CONV_TAC WORD_RULE closes the ~300-char XOR-rearrangement goal in   *)
(*      sub-second.                                                         *)
(*                                                                            *)
(* This cut is the spec-form companion to the per-component cuts of session *)
(* 029 — its postcondition is what Phase 8's loop invariant will track for   *)
(* the running tag.                                                          *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_COMPOSED_CORRECT = prove
 (`!pc (cptr:int64) (q2:int128) (q3:int128) (q4_in:int128) (q5:int128)
        (q6:int128) (q9_in:int128) (q10_in:int128) (q11_in:int128)
        (q16:int128) (rk9:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x1c8) /\
              read X2 s = cptr /\
              read Q2 s = q2 /\
              read Q3 s = q3 /\
              read Q4 s = q4_in /\
              read Q5 s = q5 /\
              read Q6 s = q6 /\
              read Q9 s = q9_in /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in /\
              read Q16 s = q16 /\
              read Q31 s = rk9)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 64) /\
              read Q11 s = kernel_modulo
                              (word_xor q9_in q5)
                              (word_xor q11_in q6)
                              (word_xor q10_in
                                 (word_pmul (word_subword q4_in (0,64) :64 word)
                                            (word_subword q16 (0,64) :64 word)
                                  :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--61) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[kernel_modulo; byteswap128; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `!h:int128.
       word_subword (word_join h h:256 word) (64,128):int128 =
       word_join (word_subword h (0,64) :64 word)
                 (word_subword h (64,64) :64 word)`
   ASSUME_TAC THENL [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Pinner:int128 =
      word_pmul (word_subword (word_xor (q5:int128) (q9_in:int128)) (0,64)
                 :64 word)
                (word 13979173243358019584:64 word)` THEN
  SUBGOAL_THEN
   `word_xor (q9_in:int128) (q5:int128) = word_xor q5 q9_in /\
    word_xor (q11_in:int128) (q6:int128) = word_xor q6 q11_in /\
    word_xor (q10_in:int128)
             (word_pmul (word_subword (q4_in:int128) (0,64) :64 word)
                        (word_subword (q16:int128) (0,64) :64 word)
              :int128) =
    word_xor (word_pmul (word_subword q4_in (0,64) :64 word)
                        (word_subword q16 (0,64) :64 word) :int128)
             q10_in`
   STRIP_ASSUME_TAC THENL [REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Hxor:int128 = word_xor (q5:int128) (q9_in:int128)` THEN
  ABBREV_TAC `Lxor:int128 = word_xor (q6:int128) (q11_in:int128)` THEN
  ABBREV_TAC
   `Pmid:int128 =
      word_pmul (word_subword (q4_in:int128) (0,64) :64 word)
                (word_subword (q16:int128) (0,64) :64 word)` THEN
  ABBREV_TAC
   `Bswapped:int128 =
      word_join (word_subword (Hxor:int128) (0,64) :64 word)
                (word_subword Hxor (64,64) :64 word)` THEN
  ABBREV_TAC
   `Inner:int128 =
      word_xor (word_xor (Pinner:int128) (Bswapped:int128))
               (word_xor (word_xor (Hxor:int128) (Lxor:int128))
                         (word_xor (Pmid:int128) (q10_in:int128)))` THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor (Pmid:int128) (q10_in:int128))
                       (word_xor (Lxor:int128) (Hxor:int128)))
             (word_xor (Bswapped:int128) (Pinner:int128)) = Inner`
    SUBST1_TAC THENL
   [EXPAND_TAC "Inner" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 prep — extended kernel-modulo body cut with Q5/Q6/Q7 emit-form    *)
(* post-conjuncts.                                                            *)
(*                                                                           *)
(* Same body slice as KERNEL_MODULO_COMPOSED_CORRECT (offsets 0x1c8..0x2bc, *)
(* 61 instructions) but with:                                                *)
(*   * augmented preconditions: Q0/Q1 added (Q2/Q3 already there); plus the *)
(*     X-register inputs X19..X24, X14 that the simulator reads in this    *)
(*     window;                                                              *)
(*   * augmented postconditions: Q5/Q6/Q7 in raw simulator-emit form        *)
(*     (function of Q1/Q2/Q3 AES outputs XOR'd with X19..X24/X14 plaintext-  *)
(*     XOR'd values).                                                       *)
(*                                                                           *)
(* These Q5/Q6/Q7 emit forms are precisely the values that get stored to   *)
(* memory via st1 [x2] at offsets 0x594/0x5a8/0x5c0 in the same slice — they*)
(* are this iteration's ciphertext blocks 1, 2, 3 (block 0 = Q4 is loaded  *)
(* from [X0] mid-slice and so doesn't have a clean emit form without a    *)
(* memory precondition; deferred to a follow-on cut).                      *)
(*                                                                           *)
(* The Q11 = kernel_modulo conjunct closure carries unchanged from the    *)
(* original KERNEL_MODULO_COMPOSED proof; the Q5/Q6/Q7 conjuncts are       *)
(* discharged automatically by ASM_REWRITE_TAC[] since the simulator's    *)
(* emit shape matches them syntactically.                                   *)
(*                                                                           *)
(* Phase 8 use: this cut feeds the loop wrapper.  At iteration i+1's loop *)
(* entry, the body precondition's `aes_gcm_rev64_int128 q5_pre =          *)
(* byteswap128 ct1` etc. is established by combining iteration i's       *)
(* Q5/Q6/Q7 emit-form post (this cut) with a separate spec-level           *)
(* identification `aes_gcm_rev64_int128 (word_xor (aese q1 rk9)           *)
(* (word_insert ...)) = byteswap128 ct'` (deferred algebraic work).        *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_PLUS_Q567_CORRECT = prove
 (`!pc (cptr:int64) (q0:int128) (q1:int128) (q2:int128) (q3:int128)
        (q4_in:int128) (q5:int128) (q6:int128) (q9_in:int128) (q10_in:int128)
        (q11_in:int128) (q16:int128) (rk9:int128)
        (x19:int64) (x20:int64) (x21:int64) (x22:int64) (x23:int64)
        (x24:int64) (sx14:int64).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x1c8) /\
              read X2 s = cptr /\
              read Q0 s = q0 /\
              read Q1 s = q1 /\
              read Q2 s = q2 /\
              read Q3 s = q3 /\
              read Q4 s = q4_in /\
              read Q5 s = q5 /\
              read Q6 s = q6 /\
              read Q9 s = q9_in /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in /\
              read Q16 s = q16 /\
              read Q31 s = rk9 /\
              read X19 s = x19 /\
              read X20 s = x20 /\
              read X21 s = x21 /\
              read X22 s = x22 /\
              read X23 s = x23 /\
              read X24 s = x24 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 64) /\
              read Q5 s = (word_xor (aese q1 rk9)
                           (word_insert
                             (word_zx x19 :int128)
                             (64,64)
                             (word_xor x20 sx14)) :int128) /\
              read Q6 s = (word_xor (aese q2 rk9)
                           (word_insert
                             (word_zx x21 :int128)
                             (64,64)
                             x22) :int128) /\
              read Q7 s = (word_xor (aese q3 rk9)
                           (word_insert
                             (word_zx x23 :int128)
                             (64,64)
                             (word_xor x24 sx14)) :int128) /\
              read Q11 s = kernel_modulo
                              (word_xor q9_in q5)
                              (word_xor q11_in q6)
                              (word_xor q10_in
                                 (word_pmul (word_subword q4_in (0,64) :64 word)
                                            (word_subword q16 (0,64) :64 word)
                                  :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--61) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[kernel_modulo; byteswap128; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `!h:int128.
       word_subword (word_join h h:256 word) (64,128):int128 =
       word_join (word_subword h (0,64) :64 word)
                 (word_subword h (64,64) :64 word)`
   ASSUME_TAC THENL [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Pinner:int128 =
      word_pmul (word_subword (word_xor (q5:int128) (q9_in:int128)) (0,64)
                 :64 word)
                (word 13979173243358019584:64 word)` THEN
  SUBGOAL_THEN
   `word_xor (q9_in:int128) (q5:int128) = word_xor q5 q9_in /\
    word_xor (q11_in:int128) (q6:int128) = word_xor q6 q11_in /\
    word_xor (q10_in:int128)
             (word_pmul (word_subword (q4_in:int128) (0,64) :64 word)
                        (word_subword (q16:int128) (0,64) :64 word)
              :int128) =
    word_xor (word_pmul (word_subword q4_in (0,64) :64 word)
                        (word_subword q16 (0,64) :64 word) :int128)
             q10_in`
   STRIP_ASSUME_TAC THENL [REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Hxor:int128 = word_xor (q5:int128) (q9_in:int128)` THEN
  ABBREV_TAC `Lxor:int128 = word_xor (q6:int128) (q11_in:int128)` THEN
  ABBREV_TAC
   `Pmid:int128 =
      word_pmul (word_subword (q4_in:int128) (0,64) :64 word)
                (word_subword (q16:int128) (0,64) :64 word)` THEN
  ABBREV_TAC
   `Bswapped:int128 =
      word_join (word_subword (Hxor:int128) (0,64) :64 word)
                (word_subword Hxor (64,64) :64 word)` THEN
  ABBREV_TAC
   `Inner:int128 =
      word_xor (word_xor (Pinner:int128) (Bswapped:int128))
               (word_xor (word_xor (Hxor:int128) (Lxor:int128))
                         (word_xor (Pmid:int128) (q10_in:int128)))` THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor (Pmid:int128) (q10_in:int128))
                       (word_xor (Lxor:int128) (Hxor:int128)))
             (word_xor (Bswapped:int128) (Pinner:int128)) = Inner`
    SUBST1_TAC THENL
   [EXPAND_TAC "Inner" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 GHASH SPEC-FORM cut over offsets 0x1c8..0x2bc.                    *)
(*                                                                           *)
(* Wraps AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_COMPOSED_CORRECT with    *)
(* KERNEL_4BLOCK_NIST_BRIDGE_LASSOC to express Q11's exit value in spec form*)
(* `nist_ghash h prev_tag [ct0;ct1;ct2;ct3]` rather than the kernel's       *)
(* `kernel_modulo` form.                                                     *)
(*                                                                           *)
(* The spec-form precondition is the bridge's input-binding antecedent: the *)
(* composition cut's q9_in/q10_in/q11_in/q4_in must satisfy the 4-block     *)
(* left-associated XOR-sum of Karatsuba components against H-power table   *)
(* entries.  In Phase 8, this antecedent will be discharged by composing    *)
(* with the per-block 0/1/2 cuts (BLOCK0_HIGH/LOW, BLOCK0_MID_BLOCK1_HIGH,  *)
(* BLOCK1_LOW/MID, BLOCK2_HL_BLOCK3_L, BLOCK2_MID_BLOCK3_HIGH) which        *)
(* together establish that q9_in/q10_in/q11_in are the per-block-0/1/2     *)
(* Karatsuba accumulators and q5/q6 are the block-3 HIGH/LOW products.      *)
(*                                                                           *)
(* Discharge: trivially follows from the composition cut + bridge:          *)
(*   1. MP_TAC the composition cut, ASM_REWRITE_TAC for nonoverlap.        *)
(*   2. MP_TAC the bridge, ASM_REWRITE_TAC for the input-binding antecedent.*)
(*   3. The bridge yields a `kernel_modulo (...) = nist_ghash` equality.   *)
(*      GSYM-rewrite to fold nist_ghash → kernel_modulo in the goal,       *)
(*      matching the composition cut's postcondition exactly.               *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_CORRECT = prove
 (`!pc (cptr:int64) (q2:int128) (q3:int128) (q4_in:int128) (q5:int128)
        (q6:int128) (q9_in:int128) (q10_in:int128) (q11_in:int128)
        (q16:int128) (rk9:int128) (h:int128) (prev_tag:int128)
        (ct0:int128) (ct1:int128) (ct2:int128) (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64) /\
    (let h0,l0,m0 =
       karatsuba_components (byteswap128 (word_xor prev_tag ct0))
                            (byteswap128 (h_power (ghash_twist h) 3)) in
     let h1,l1,m1 =
       karatsuba_components (byteswap128 ct1)
                            (byteswap128 (h_power (ghash_twist h) 2)) in
     let h2,l2,m2 =
       karatsuba_components (byteswap128 ct2)
                            (byteswap128 (h_power (ghash_twist h) 1)) in
     let h3,l3,m3 =
       karatsuba_components (byteswap128 ct3)
                            (byteswap128 (h_power (ghash_twist h) 0)) in
     word_xor q9_in q5 = word_xor (word_xor (word_xor h0 h1) h2) h3 /\
     word_xor q11_in q6 = word_xor (word_xor (word_xor l0 l1) l2) l3 /\
     word_xor q10_in
              (word_pmul (word_subword q4_in (0,64) :64 word)
                         (word_subword q16 (0,64) :64 word) :int128) =
     word_xor (word_xor (word_xor m0 m1) m2) m3)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x1c8) /\
              read X2 s = cptr /\
              read Q2 s = q2 /\
              read Q3 s = q3 /\
              read Q4 s = q4_in /\
              read Q5 s = q5 /\
              read Q6 s = q6 /\
              read Q9 s = q9_in /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in /\
              read Q16 s = q16 /\
              read Q31 s = rk9)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 64) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3])
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cptr:int64`; `q2:int128`; `q3:int128`;
                `q4_in:int128`; `q5:int128`; `q6:int128`; `q9_in:int128`;
                `q10_in:int128`; `q11_in:int128`; `q16:int128`; `rk9:int128`]
               AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_COMPOSED_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:int128`; `prev_tag:int128`; `ct0:int128`;
                `ct1:int128`; `ct2:int128`; `ct3:int128`;
                `q5:int128`; `q6:int128`; `q9_in:int128`;
                `q10_in:int128`; `q11_in:int128`; `q4_in:int128`;
                `q16:int128`]
               KERNEL_4BLOCK_NIST_BRIDGE_LASSOC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* ------------------------------------------------------------------------- *)
(* Phase 7/8 GHASH SPEC-FORM cut over offsets 0x1c8..0x2bc, augmented with    *)
(* Q5/Q6/Q7 emit-form post-conjuncts (and the precondition registers needed   *)
(* by KERNEL_MODULO_PLUS_Q567).                                               *)
(*                                                                           *)
(* Wraps AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_PLUS_Q567_CORRECT with    *)
(* KERNEL_4BLOCK_NIST_BRIDGE_LASSOC, exactly mirroring NIST_SPEC_FORM_CORRECT *)
(* but threading Q0/Q1 + X19..X24/X14 through and surfacing the Q5/Q6/Q7     *)
(* emit forms (`word_xor (aese qi rk9) (word_insert ...)`).                  *)
(*                                                                           *)
(* Phase 8 use: this is the "spec-form" cut at the slice boundary that the   *)
(* loop wrapper needs in order to (a) carry running tag Q11 = nist_ghash and *)
(* (b) re-establish the next iteration's q5/q6/q7 byteswap identifications  *)
(* via AES_GCM_REV64_OF_EMIT_FORM applied to the emit-form Q5/Q6/Q7.         *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_PLUS_Q567_CORRECT = prove
 (`!pc (cptr:int64) (q0:int128) (q1:int128) (q2:int128) (q3:int128)
        (q4_in:int128) (q5:int128) (q6:int128) (q9_in:int128) (q10_in:int128)
        (q11_in:int128) (q16:int128) (rk9:int128)
        (x19:int64) (x20:int64) (x21:int64) (x22:int64) (x23:int64)
        (x24:int64) (sx14:int64)
        (h:int128) (prev_tag:int128)
        (ct0:int128) (ct1:int128) (ct2:int128) (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64) /\
    (let h0,l0,m0 =
       karatsuba_components (byteswap128 (word_xor prev_tag ct0))
                            (byteswap128 (h_power (ghash_twist h) 3)) in
     let h1,l1,m1 =
       karatsuba_components (byteswap128 ct1)
                            (byteswap128 (h_power (ghash_twist h) 2)) in
     let h2,l2,m2 =
       karatsuba_components (byteswap128 ct2)
                            (byteswap128 (h_power (ghash_twist h) 1)) in
     let h3,l3,m3 =
       karatsuba_components (byteswap128 ct3)
                            (byteswap128 (h_power (ghash_twist h) 0)) in
     word_xor q9_in q5 = word_xor (word_xor (word_xor h0 h1) h2) h3 /\
     word_xor q11_in q6 = word_xor (word_xor (word_xor l0 l1) l2) l3 /\
     word_xor q10_in
              (word_pmul (word_subword q4_in (0,64) :64 word)
                         (word_subword q16 (0,64) :64 word) :int128) =
     word_xor (word_xor (word_xor m0 m1) m2) m3)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x1c8) /\
              read X2 s = cptr /\
              read Q0 s = q0 /\
              read Q1 s = q1 /\
              read Q2 s = q2 /\
              read Q3 s = q3 /\
              read Q4 s = q4_in /\
              read Q5 s = q5 /\
              read Q6 s = q6 /\
              read Q9 s = q9_in /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in /\
              read Q16 s = q16 /\
              read Q31 s = rk9 /\
              read X19 s = x19 /\
              read X20 s = x20 /\
              read X21 s = x21 /\
              read X22 s = x22 /\
              read X23 s = x23 /\
              read X24 s = x24 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 64) /\
              read Q5 s = (word_xor (aese q1 rk9)
                           (word_insert
                             (word_zx x19 :int128)
                             (64,64)
                             (word_xor x20 sx14)) :int128) /\
              read Q6 s = (word_xor (aese q2 rk9)
                           (word_insert
                             (word_zx x21 :int128)
                             (64,64)
                             x22) :int128) /\
              read Q7 s = (word_xor (aese q3 rk9)
                           (word_insert
                             (word_zx x23 :int128)
                             (64,64)
                             (word_xor x24 sx14)) :int128) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3])
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cptr:int64`; `q0:int128`; `q1:int128`;
                `q2:int128`; `q3:int128`;
                `q4_in:int128`; `q5:int128`; `q6:int128`;
                `q9_in:int128`; `q10_in:int128`; `q11_in:int128`;
                `q16:int128`; `rk9:int128`;
                `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`;
                `x23:int64`; `x24:int64`; `sx14:int64`]
               AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_PLUS_Q567_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:int128`; `prev_tag:int128`; `ct0:int128`;
                `ct1:int128`; `ct2:int128`; `ct3:int128`;
                `q5:int128`; `q6:int128`; `q9_in:int128`;
                `q10_in:int128`; `q11_in:int128`; `q4_in:int128`;
                `q16:int128`]
               KERNEL_4BLOCK_NIST_BRIDGE_LASSOC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* ------------------------------------------------------------------------- *)
(* Phase 8 plan — discharging the bridge antecedent.                          *)
(*                                                                            *)
(* AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_CORRECT takes the bridge       *)
(* antecedent (q9_in/q10_in/q11_in/q5/q6/q4_in/q16 = 4-block left-           *)
(* associated Karatsuba-sum of byteswapped ct_i × H-power) as a              *)
(* precondition.  Phase 8 will discharge it by composing the per-component   *)
(* GHASH cuts for offsets 0..0x1c8 (instr 1..114) into a wider ensures       *)
(* whose postcondition establishes:                                           *)
(*                                                                            *)
(*   At offset 0x1c8 (composition cut entry):                                 *)
(*     read Q9  s = h0 ^ h1 ^ h2     (sum of per-block-0/1/2 HIGH Karatsuba) *)
(*     read Q10 s = m0 ^ m1 ^ m2     (sum of per-block-0/1/2 MID Karatsuba)  *)
(*     read Q11 s = l0 ^ l1 ^ l2     (sum of per-block-0/1/2 LOW Karatsuba)  *)
(*     read Q5  s = h3                (block-3 HIGH Karatsuba)               *)
(*     read Q6  s = l3                (block-3 LOW Karatsuba)                *)
(*     read Q4  s = byteswap128 ct3 ^ byteswap128 (h_power (ghash_twist h) 0) *)
(*                                    -- but only its low half is used in    *)
(*                                       pmull(q4_lo, q16_lo) = m3            *)
(*     read Q16 s = byteswap128 (h_power (ghash_twist h) 0)                  *)
(*                                                                            *)
(*   where (h_i, l_i, m_i) =                                                 *)
(*     karatsuba_components (byteswap128 c_i) (byteswap128 H_{3-i})           *)
(*     and c_0 = word_xor prev_tag ct0, c_1 = ct1, c_2 = ct2, c_3 = ct3       *)
(*     and H_k = h_power (ghash_twist h) k.                                   *)
(*                                                                            *)
(*   With these bindings, the bridge antecedent simplifies via XOR-          *)
(*   commutativity to                                                         *)
(*     word_xor q9_in q5 = (h0 ^ h1 ^ h2) ^ h3 = h0 ^ h1 ^ h2 ^ h3   ✓        *)
(*   etc., closing it via WORD_RULE.                                          *)
(*                                                                            *)
(* Composing the per-component cuts for 0..0x1c8 is the bulk of Phase 8       *)
(* preparatory work.  Per session-031 strategy, brute-force ARM_STEPS_TAC    *)
(* over instr 1..114 (~3s wall-clock) + ABBREV-driven WORD_RULE close per   *)
(* `brute_force_composition` and `abbrev_word_rule_kernel_modulo` memories.  *)
(*                                                                            *)
(* The Q4/Q5 OLD/NEW chain across instr 39, 45, 50, 71, 102 must be threaded *)
(* explicitly: each PMULL/PMULL2 that overwrites Q4/Q5 produces a *new*      *)
(* Karatsuba product, while the EOR_VEC accumulators consume the *old* Q4/Q5*)
(* values.  Per-component cuts already capture this chain (e.g.             *)
(* BLOCK1_HIGH overwrites Q4 with block-1 HIGH product); composition needs   *)
(* to symbolically execute through the chain in one ARM_STEPS_TAC pass.      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Phase 7/8 H-power + round-key preservation cut: instructions 1..114      *)
(* (offsets 0..0x1c8) preserve Q12..Q17 (H-power table) AND Q18..Q26 (AES  *)
(* round keys 0..8) across the loop body's per-block-0/1/2/3-mid Karatsuba *)
(* portion.                                                                   *)
(*                                                                            *)
(* This is the "minimal" composition cut for offsets 0..0x1c8: brute-force  *)
(* ARM_STEPS_TAC with a postcondition that asserts only register             *)
(* preservation (no GHASH value tracking — that's the substantial Phase 8   *)
(* discharge work; see Phase 8 plan comment block above).                    *)
(*                                                                            *)
(* The cut establishes that:                                                  *)
(*   - H-power table registers Q12..Q17 are NOT clobbered during the per-   *)
(*     block 0/1/2/3-mid Karatsuba portion (needed for iteration invariance *)
(*     in Phase 8 loop wrapper);                                              *)
(*   - AES round-key registers Q18..Q26 (rk0..rk8) are also preserved       *)
(*     (the body slice has no LDR Q18..Q26 in this prefix; round keys are   *)
(*     loaded once in the kernel prologue and read-only thereafter).         *)
(*                                                                            *)
(* Q31 (rk9) is NOT included in the precondition or postcondition — it is   *)
(* first used at slice offset 0x224 (instr 138, AES round-9 final), AFTER   *)
(* this cut's window.  The compose-with-rest cut at Phase 8 will add Q31    *)
(* preservation across the full body.                                        *)
(*                                                                            *)
(* Closes via brute-force ARM_STEPS_TAC + ENSURES_FINAL_STATE_TAC +          *)
(* ASM_REWRITE_TAC.  ~3 seconds wall-clock per                               *)
(* `brute_force_composition` memory.  Round-key preservation is automatic   *)
(* since Q18..Q26 are not in MAYCHANGE — adding them to the postcondition  *)
(* requires no extra closing tactic work.                                    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_HPOWER_PRESERVED_CORRECT = prove
 (`!pc (cptr:int64) (b0_pre:int128) (b1_pre:int128) (b2_pre:int128)
        (b3_pre:int128) (q4_pre:int128) (q11_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128)
        (q16:int128) (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word pc /\
              read X2 s = cptr /\
              read Q0 s = b0_pre /\
              read Q1 s = b1_pre /\
              read Q2 s = b2_pre /\
              read Q4 s = q4_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x1c8) /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8)
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--114) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* DISCHARGE_CORRECT: 10-cut chain composition over offsets 0..0x1c8.
 * Postcondition asserts the kernel-form Q4..Q11 values that
 * AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_COMPOSED_CORRECT consumes,
 * plus preserved Q12..Q26 round-key/H-power table.
 *)
let AES_GCM_MAIN_LOOP_BODY_GHASH_DISCHARGE_CORRECT = prove
 (`!pc (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
          read PC s = word pc /\
          read Q0 s = b0 /\
          read Q1 s = b1 /\
          read Q2 s = b2 /\
          read Q4 s = q4_pre /\
          read Q5 s = q5_pre /\
          read Q6 s = q6_pre /\
          read Q7 s = q7_pre /\
          read Q11 s = q11_pre /\
          read Q12 s = q12 /\
          read Q13 s = q13 /\
          read Q14 s = q14 /\
          read Q15 s = q15 /\
          read Q16 s = q16 /\
          read Q17 s = q17 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8 /\
          read X9 s = sx9 /\
          read X10 s = sx10 /\
          read X13 s = sx13 /\
          read X14 s = sx14)
     (\s. read PC s = word (pc + 0x1c8) /\
          read Q4 s =
            (word_zx (word_subword
              (word_xor (aes_gcm_rev64_int128 q7_pre)
                        (word_zx (word_subword (aes_gcm_rev64_int128 q7_pre)
                                               (64,64) :64 word) :int128))
              (0,64) :64 word) :int128) /\
          read Q5 s =
            (word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64)
                                     :64 word)
                       (word_subword q12 (64,64) :64 word) :int128) /\
          read Q6 s =
            (word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (0,64)
                                     :64 word)
                       (word_subword q12 (0,64) :64 word) :int128) /\
          read Q9 s =
            word_xor
             (word_xor
              (word_pmul
                (word_subword
                  (word_xor (aes_gcm_rev64_int128 q4_pre)
                            (byteswap128 q11_pre)) (64,64) :64 word)
                (word_subword q15 (64,64) :64 word) :int128)
              (word_pmul
                (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word)
                (word_subword q14 (64,64) :64 word) :int128))
             (word_pmul
               (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word)
               (word_subword q13 (64,64) :64 word) :int128) /\
          read Q10 s =
            word_xor
             (word_xor
              (word_pmul
                (word_subword
                  (word_xor
                    (word_xor (aes_gcm_rev64_int128 q4_pre)
                              (byteswap128 q11_pre))
                    (word_zx
                      (word_subword
                        (word_xor (aes_gcm_rev64_int128 q4_pre)
                                  (byteswap128 q11_pre))
                        (64,64) :64 word) :int128))
                  (0,64) :64 word)
                (word_subword
                  (word_zx (word_subword q17 (64,64) :64 word) :int128)
                  (0,64) :64 word) :int128)
              (word_pmul
                (word_subword
                  (word_xor
                    (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre)
                                           (64,64) :64 word) :int128)
                    (aes_gcm_rev64_int128 q5_pre)) (0,64) :64 word)
                (word_subword q17 (0,64) :64 word) :int128))
             (word_pmul
               (word_subword
                 (word_insert
                   (word_zx
                     (word_xor
                       (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                                     :64 word)
                       (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                                     :64 word) :64 word) :int128)
                   (64,64)
                   (word_subword
                     (word_subword
                       (word_zx
                         (word_xor
                           (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                                         :64 word)
                           (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                                         :64 word) :64 word) :int128)
                       (0,64) :64 word) (0,64) :64 word) :int128) (64,64)
                 :64 word)
               (word_subword q16 (64,64) :64 word) :int128) /\
          read Q11 s =
            word_xor
             (word_xor
              (word_pmul
                (word_subword
                  (word_xor (aes_gcm_rev64_int128 q4_pre)
                            (byteswap128 q11_pre)) (0,64) :64 word)
                (word_subword q15 (0,64) :64 word) :int128)
              (word_pmul
                (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word)
                (word_subword q14 (0,64) :64 word) :int128))
             (word_pmul
               (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word)
               (word_subword q13 (0,64) :64 word) :int128) /\
          read Q12 s = q12 /\
          read Q13 s = q13 /\
          read Q14 s = q14 /\
          read Q15 s = q15 /\
          read Q16 s = q16 /\
          read Q17 s = q17 /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q22 s = rk4 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7 /\
          read Q26 s = rk8)
     (MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL[`pc:num`; `b0:int128`; `b1:int128`; `b2:int128`;
               `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
               `sx9:int64`; `sx10:int64`; `sx13:int64`;
               `q4_pre:int128`; `q11_pre:int128`;
               `q15:int128`; `q17:int128`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_PRELUDE_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s21" THEN
  MP_TAC(SPECL[`pc:num`;
               `(aes_arm_round (aes_arm_round (aes_arm_round b0 rk0) rk1) rk2):int128`;
               `(aes_arm_round (aes_arm_round b1 rk0) rk1):int128`;
               `(word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)):int128`;
               `(word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre)):int128`;
               `(q15:int128)`;
               `(q17:int128)`;
               `(rk0:int128)`;
               `(rk2:int128)`;
               `(rk3:int128)`;
               `(sx13:int64)`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK0_HIGH_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s30" THEN
  MP_TAC(SPECL[`pc:num`;
               `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b0 rk0) rk1) rk2) rk3):int128`;
               `(aes_arm_round (word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)) rk0):int128`;
               `(word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre)):int128`;
               `(q15:int128)`;
               `(q5_pre:int128)`;
               `(rk1:int128)`;
               `(rk4:int128)`;
               `(sx14:int64)`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK0_LOW_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s38" THEN
  MP_TAC(SPECL[`pc:num`;
               `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b0 rk0) rk1) rk2) rk3) rk4):int128`;
               `(aes_arm_round (aes_arm_round b1 rk0) rk1):int128`;
               `(aes_arm_round (aes_arm_round b2 rk0) rk1):int128`;
               `(aes_arm_round (aes_arm_round (word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)) rk0) rk1):int128`;
               `(aes_gcm_rev64_int128 q5_pre):int128`;
               `(q14:int128)`;
               `(q7_pre:int128)`;
               `(word_zx (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (64,64) :64 word) :int128):int128`;
               `(word_zx (word_subword (q17:int128) (64,64) :64 word) :int128):int128`;
               `(word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre)):int128`;
               `(rk2:int128)`;
               `(rk5:int128)`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK0_MID_BLOCK1_HIGH_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s46" THEN
  MP_TAC(SPECL[`pc:num`;
               `(aes_arm_round (aes_arm_round (aes_arm_round b1 rk0) rk1) rk2):int128`;
               `(aes_arm_round (aes_arm_round (word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)) rk0) rk1):int128`;
               `(aes_gcm_rev64_int128 q5_pre):int128`;
               `(q14:int128)`;
               `(q6_pre:int128)`;
               `(word_pmul (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (64,64) :64 word) (word_subword (q15:int128) (64,64) :64 word) :int128):int128`;
               `(word_pmul (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word) (word_subword (q14:int128) (64,64) :64 word) :int128):int128`;
               `(rk2:int128)`;
               `(rk3:int128)`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK1_LOW_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s54" THEN
  MP_TAC(SPECL[`pc:num`;
               `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b0 rk0) rk1) rk2) rk3) rk4) rk5):int128`;
               `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b1 rk0) rk1) rk2) rk3):int128`;
               `(aes_arm_round (aes_arm_round (aes_arm_round b2 rk0) rk1) rk2):int128`;
               `(aes_arm_round (aes_arm_round (aes_arm_round (word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)) rk0) rk1) rk2):int128`;
               `(word_zx (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word) :int128):int128`;
               `(aes_gcm_rev64_int128 q5_pre):int128`;
               `(aes_gcm_rev64_int128 q6_pre):int128`;
               `(word_pmul (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word) (word_subword (q14:int128) (0,64) :64 word) :int128):int128`;
               `(word_pmul (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (0,64) :64 word) (word_subword (q15:int128) (0,64) :64 word) :int128):int128`;
               `(q17:int128)`;
               `(rk3:int128)`;
               `(rk4:int128)`;
               `(rk6:int128)`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK1_MID_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s71" THEN
  MP_TAC(SPECL[
    `pc:num`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b0 rk0) rk1) rk2) rk3) rk4) rk5) rk6):int128`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b1 rk0) rk1) rk2) rk3) rk4):int128`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b2 rk0) rk1) rk2) rk3) rk4):int128`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)) rk0) rk1) rk2) rk3) rk4):int128`;
    `(rk5:int128)`;
    `(rk6:int128)`;
    `(rk7:int128)`;
    `(rk8:int128)`;
    `(word_pmul (word_subword (word_xor (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word) :int128) (aes_gcm_rev64_int128 q5_pre):int128) (0,64) :64 word) (word_subword (q17:int128) (0,64) :64 word) :int128):int128`;
    `(word_zx (word_xor (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word) (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word) :64 word) :int128):int128`;
    `(word_xor (word_pmul (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (0,64) :64 word) (word_subword (q15:int128) (0,64) :64 word) :int128) (word_pmul (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word) (word_subword (q14:int128) (0,64) :64 word) :int128) :int128):int128`
  ] AES_GCM_MAIN_LOOP_BODY_GHASH_GAP_AES_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s84" THEN
  MP_TAC(SPECL[
    `pc:num`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b1 rk0) rk1) rk2) rk3) rk4) rk5) rk6):int128`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)) rk0) rk1) rk2) rk3) rk4) rk5):int128`;
    `(aes_gcm_rev64_int128 q6_pre):int128`;
    `(aes_gcm_rev64_int128 q7_pre):int128`;
    `(q12:int128)`;
    `(q13:int128)`;
    `(word_xor (word_pmul (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (64,64) :64 word) (word_subword (q15:int128) (64,64) :64 word) :int128) (word_pmul (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word) (word_subword (q14:int128) (64,64) :64 word) :int128) :int128):int128`;
    `(word_pmul (word_subword (word_xor (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (word_zx (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (64,64) :64 word) :int128):int128) (0,64) :64 word) (word_subword (word_zx (word_subword (q17:int128) (64,64) :64 word) :int128) (0,64) :64 word) :int128):int128`;
    `(word_pmul (word_subword (word_xor (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word) :int128) (aes_gcm_rev64_int128 q5_pre):int128) (0,64) :64 word) (word_subword (q17:int128) (0,64) :64 word) :int128):int128`;
    `(rk6:int128)`;
    `(rk7:int128)`
  ] AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK2_HL_BLOCK3_L_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s93" THEN
  MP_TAC(SPECL[
    `pc:num`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b1 rk0) rk1) rk2) rk3) rk4) rk5) rk6) rk7):int128`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b2 rk0) rk1) rk2) rk3) rk4) rk5):int128`;
    `(word_pmul (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word) (word_subword (q13:int128) (0,64) :64 word) :int128):int128`;
    `(aes_gcm_rev64_int128 q7_pre):int128`;
    `(word_insert (word_zx (word_xor (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word) (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word) :64 word) :int128) (64,64) (word_subword (word_subword (word_zx (word_xor (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word) (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word) :64 word) :int128) (0,64) :64 word) (0,64) :64 word) :int128):int128`;
    `(word_xor (word_pmul (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (0,64) :64 word) (word_subword (q15:int128) (0,64) :64 word) :int128) (word_pmul (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word) (word_subword (q14:int128) (0,64) :64 word) :int128) :int128):int128`;
    `(q12:int128)`;
    `(q16:int128)`;
    `(rk6:int128)`;
    `(rk7:int128)`;
    `(rk8:int128)`
  ] AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK2_MID_BLOCK3_HIGH_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s105" THEN
  MP_TAC(SPECL[
    `pc:num`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round b2 rk0) rk1) rk2) rk3) rk4) rk5) rk6) rk7):int128`;
    `(aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (aes_arm_round (word_insert (word_zx (sx10:int64) :int128) (64,64) (sx9:int64)) rk0) rk1) rk2) rk3) rk4) rk5) rk6):int128`;
    `(word_pmul (word_subword (word_insert (word_zx (word_xor (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word) (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word) :64 word) :int128) (64,64) (word_subword (word_subword (word_zx (word_xor (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word) (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word) :64 word) :int128) (0,64) :64 word) (0,64) :64 word) :int128) (64,64) :64 word) (word_subword (q16:int128) (64,64) :64 word) :int128):int128`;
    `(word_xor (word_pmul (word_subword (word_xor (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (word_zx (word_subword (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre):int128) (64,64) :64 word) :int128):int128) (0,64) :64 word) (word_subword (word_zx (word_subword (q17:int128) (64,64) :64 word) :int128) (0,64) :64 word) :int128) (word_pmul (word_subword (word_xor (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word) :int128) (aes_gcm_rev64_int128 q5_pre):int128) (0,64) :64 word) (word_subword (q17:int128) (0,64) :64 word) :int128) :int128):int128`;
    `(rk6:int128)`;
    `(rk7:int128)`;
    `(rk8:int128)`
  ] AES_GCM_MAIN_LOOP_BODY_GHASH_BLOCK2_MID_ACCUM_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s114" THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
              read PC s = word pc /\
              read X2 s = cptr /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 64) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3])
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL[`pc:num`; `b0:int128`; `b1:int128`; `b2:int128`;
               `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
               `q7_pre:int128`; `q6_pre:int128`;
               `q12:int128`; `q13:int128`; `q14:int128`; `q15:int128`;
               `q16:int128`; `q17:int128`;
               `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
               `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
               `rk8:int128`;
               `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_DISCHARGE_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s114" THEN
  ABBREV_TAC `q2_kmc:int128 = read Q2 s114` THEN
  ABBREV_TAC `q3_kmc:int128 = read Q3 s114` THEN
  MP_TAC(SPECL[`pc:num`; `cptr:int64`; `q2_kmc:int128`; `q3_kmc:int128`;
   `(word_zx (word_subword
      (word_xor (aes_gcm_rev64_int128 q7_pre)
      (word_zx (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
       :int128))
     (0,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
               (word_subword (q12:int128) (64,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (0,64) :64 word)
               (word_subword (q12:int128) (0,64) :64 word) :int128):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (64,64) :64 word)
          (word_subword (q15:int128) (64,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word)
          (word_subword (q14:int128) (64,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word)
        (word_subword (q13:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor
              (word_xor (aes_gcm_rev64_int128 q4_pre)
                        (byteswap128 q11_pre))
              (word_zx
                (word_subword
                  (word_xor (aes_gcm_rev64_int128 q4_pre)
                            (byteswap128 q11_pre))
                  (64,64) :64 word) :int128))
            (0,64) :64 word)
          (word_subword
            (word_zx (word_subword (q17:int128) (64,64) :64 word) :int128)
            (0,64) :64 word) :int128)
        (word_pmul
          (word_subword
            (word_xor
              (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre)
                                     (64,64) :64 word) :int128)
              (aes_gcm_rev64_int128 q5_pre)) (0,64) :64 word)
          (word_subword (q17:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword
          (word_insert
            (word_zx
              (word_xor
                (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                              :64 word)
                (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                              :64 word) :64 word) :int128)
            (64,64)
            (word_subword
              (word_subword
                (word_zx
                  (word_xor
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                                  :64 word)
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                                  :64 word) :64 word) :int128)
                (0,64) :64 word) (0,64) :64 word) :int128) (64,64)
          :64 word)
        (word_subword (q16:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (0,64) :64 word)
          (word_subword (q15:int128) (0,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word)
          (word_subword (q14:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word)
        (word_subword (q13:int128) (0,64) :64 word) :int128)):int128`;
   `q16:int128`; `rk9:int128`;
   `h:int128`; `prev_tag:int128`;
   `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_CORRECT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[karatsuba_components; karatsuba_mid; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128] THEN
    SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
             DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH;
             WORD_SUBWORD_TRIVIAL] THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ABBREV_TAC `c0_lo:64 word = word_subword ((word_xor prev_tag ct0):int128) (0,64)` THEN
    ABBREV_TAC `c0_hi:64 word = word_subword ((word_xor prev_tag ct0):int128) (64,64)` THEN
    ABBREV_TAC `c1_lo:64 word = word_subword (ct1:int128) (0,64)` THEN
    ABBREV_TAC `c1_hi:64 word = word_subword (ct1:int128) (64,64)` THEN
    ABBREV_TAC `c2_lo:64 word = word_subword (ct2:int128) (0,64)` THEN
    ABBREV_TAC `c2_hi:64 word = word_subword (ct2:int128) (64,64)` THEN
    ABBREV_TAC `c3_lo:64 word = word_subword (ct3:int128) (0,64)` THEN
    ABBREV_TAC `c3_hi:64 word = word_subword (ct3:int128) (64,64)` THEN
    ABBREV_TAC `H0_LO:64 word = word_subword (h_power (ghash_twist h) 0) (0,64)` THEN
    ABBREV_TAC `H0_HI:64 word = word_subword (h_power (ghash_twist h) 0) (64,64)` THEN
    ABBREV_TAC `H1_LO:64 word = word_subword (h_power (ghash_twist h) 1) (0,64)` THEN
    ABBREV_TAC `H1_HI:64 word = word_subword (h_power (ghash_twist h) 1) (64,64)` THEN
    ABBREV_TAC `H2_LO:64 word = word_subword (h_power (ghash_twist h) 2) (0,64)` THEN
    ABBREV_TAC `H2_HI:64 word = word_subword (h_power (ghash_twist h) 2) (64,64)` THEN
    ABBREV_TAC `H3_LO:64 word = word_subword (h_power (ghash_twist h) 3) (0,64)` THEN
    ABBREV_TAC `H3_HI:64 word = word_subword (h_power (ghash_twist h) 3) (64,64)` THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_join (c0_lo:64 word) (c0_hi:64 word):int128)
                              (word_zx (c0_lo:64 word):int128)) (0,64) :64 word) =
      word_xor c0_hi c0_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_zx (c1_lo:64 word):int128)
                              (word_join (c1_lo:64 word) (c1_hi:64 word):int128))
                    (0,64) :64 word) =
      word_xor c1_hi c1_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_subword (word_xor (word_join (c3_lo:64 word) (c3_hi:64 word):int128)
                                                     (word_zx (c3_lo:64 word):int128))
                                           (0,64) :64 word):int128) (0,64) :64 word) =
      word_xor c3_hi c3_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_insert (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                 (64,64)
                                 (word_subword (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                               (0,64) :64 word):int128) (64,64) :64 word) =
      word_xor c2_hi c2_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_xor (H3_LO:64 word) (H3_HI:64 word):64 word)
                    :int128) (0,64) :64 word) = word_xor H3_LO H3_HI` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `Mp_h0:int128 = word_pmul (word_xor (c0_lo:64 word) (c0_hi:64 word))
                                         (word_xor (H3_LO:64 word) (H3_HI:64 word))` THEN
    ABBREV_TAC `Mp_h1:int128 = word_pmul (word_xor (c1_lo:64 word) (c1_hi:64 word))
                                         (word_xor (H2_LO:64 word) (H2_HI:64 word))` THEN
    ABBREV_TAC `Mp_h2:int128 = word_pmul (word_xor (c2_lo:64 word) (c2_hi:64 word))
                                         (word_xor (H1_LO:64 word) (H1_HI:64 word))` THEN
    ABBREV_TAC `Mp_h3:int128 = word_pmul (word_xor (c3_lo:64 word) (c3_hi:64 word))
                                         (word_xor (H0_LO:64 word) (H0_HI:64 word))` THEN
    SUBGOAL_THEN
     `word_xor (c0_hi:64 word) c0_lo = word_xor c0_lo c0_hi /\
      word_xor (c1_hi:64 word) c1_lo = word_xor c1_lo c1_hi /\
      word_xor (c2_hi:64 word) c2_lo = word_xor c2_lo c2_hi /\
      word_xor (c3_hi:64 word) c3_lo = word_xor c3_lo c3_hi` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s175" THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7/8 GHASH NIST_FULL with Q5/Q6/Q7 emit-form post-conjuncts.          *)
(*                                                                           *)
(* Wraps DISCHARGE_CORRECT (offsets 0..0x1c8) and NIST_SPEC_FORM_PLUS_Q567   *)
(* (offsets 0x1c8..0x2bc) into a single ensures over the full body slice,    *)
(* mirroring NIST_FULL_CORRECT but threading Q5/Q6/Q7 emit-form post-        *)
(* conjuncts.                                                                *)
(*                                                                           *)
(* The emit forms are existentially quantified over the s114 boundary values *)
(* of Q1/Q2/Q3 and X19..X24 — the simulator computes specific symbolic       *)
(* expressions for these registers across DISCHARGE's 114-instruction chain, *)
(* but they are not asserted in DISCHARGE's postcondition; they are abbreviated*)
(* via ABBREV_TAC after the BIGSTEP s114 and surfaced as existential witnesses*)
(* in the post.                                                              *)
(*                                                                           *)
(* Phase 8 use: this is the body cut for the loop wrapper.  At iteration     *)
(* i+1's loop top the `?q1k...x24k.` existential lets the loop invariant     *)
(* introduce abstract ciphertext-block carry without forcing the cut to      *)
(* spell out the AES round-9 chain.                                          *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_PLUS_Q567_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
              read PC s = word pc /\
              read X2 s = cptr /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X2 s = word_add cptr (word 64) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3] /\
              (?(q1k:int128) (q2k:int128) (q3k:int128)
                (x19k:int64) (x20k:int64) (x21k:int64)
                (x22k:int64) (x23k:int64) (x24k:int64).
                 read Q5 s = (word_xor (aese q1k rk9)
                               (word_insert
                                 (word_zx x19k :int128)
                                 (64,64)
                                 (word_xor x20k sx14)) :int128) /\
                 read Q6 s = (word_xor (aese q2k rk9)
                               (word_insert
                                 (word_zx x21k :int128)
                                 (64,64)
                                 x22k) :int128) /\
                 read Q7 s = (word_xor (aese q3k rk9)
                               (word_insert
                                 (word_zx x23k :int128)
                                 (64,64)
                                 (word_xor x24k sx14)) :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL[`pc:num`; `b0:int128`; `b1:int128`; `b2:int128`;
               `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
               `q7_pre:int128`; `q6_pre:int128`;
               `q12:int128`; `q13:int128`; `q14:int128`; `q15:int128`;
               `q16:int128`; `q17:int128`;
               `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
               `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
               `rk8:int128`;
               `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_DISCHARGE_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s114" THEN
  ABBREV_TAC `q0_kmc:int128 = read Q0 s114` THEN
  ABBREV_TAC `q1_kmc:int128 = read Q1 s114` THEN
  ABBREV_TAC `q2_kmc:int128 = read Q2 s114` THEN
  ABBREV_TAC `q3_kmc:int128 = read Q3 s114` THEN
  ABBREV_TAC `x19_kmc:int64 = read X19 s114` THEN
  ABBREV_TAC `x20_kmc:int64 = read X20 s114` THEN
  ABBREV_TAC `x21_kmc:int64 = read X21 s114` THEN
  ABBREV_TAC `x22_kmc:int64 = read X22 s114` THEN
  ABBREV_TAC `x23_kmc:int64 = read X23 s114` THEN
  ABBREV_TAC `x24_kmc:int64 = read X24 s114` THEN
  MP_TAC(SPECL[`pc:num`; `cptr:int64`;
   `q0_kmc:int128`; `q1_kmc:int128`; `q2_kmc:int128`; `q3_kmc:int128`;
   `(word_zx (word_subword
      (word_xor (aes_gcm_rev64_int128 q7_pre)
      (word_zx (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
       :int128))
     (0,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
               (word_subword (q12:int128) (64,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (0,64) :64 word)
               (word_subword (q12:int128) (0,64) :64 word) :int128):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (64,64) :64 word)
          (word_subword (q15:int128) (64,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word)
          (word_subword (q14:int128) (64,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word)
        (word_subword (q13:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor
              (word_xor (aes_gcm_rev64_int128 q4_pre)
                        (byteswap128 q11_pre))
              (word_zx
                (word_subword
                  (word_xor (aes_gcm_rev64_int128 q4_pre)
                            (byteswap128 q11_pre))
                  (64,64) :64 word) :int128))
            (0,64) :64 word)
          (word_subword
            (word_zx (word_subword (q17:int128) (64,64) :64 word) :int128)
            (0,64) :64 word) :int128)
        (word_pmul
          (word_subword
            (word_xor
              (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre)
                                     (64,64) :64 word) :int128)
              (aes_gcm_rev64_int128 q5_pre)) (0,64) :64 word)
          (word_subword (q17:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword
          (word_insert
            (word_zx
              (word_xor
                (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                              :64 word)
                (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                              :64 word) :64 word) :int128)
            (64,64)
            (word_subword
              (word_subword
                (word_zx
                  (word_xor
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                                  :64 word)
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                                  :64 word) :64 word) :int128)
                (0,64) :64 word) (0,64) :64 word) :int128) (64,64)
          :64 word)
        (word_subword (q16:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (0,64) :64 word)
          (word_subword (q15:int128) (0,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word)
          (word_subword (q14:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word)
        (word_subword (q13:int128) (0,64) :64 word) :int128)):int128`;
   `q16:int128`; `rk9:int128`;
   `x19_kmc:int64`; `x20_kmc:int64`; `x21_kmc:int64`;
   `x22_kmc:int64`; `x23_kmc:int64`; `x24_kmc:int64`; `sx14:int64`;
   `h:int128`; `prev_tag:int128`;
   `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_PLUS_Q567_CORRECT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[karatsuba_components; karatsuba_mid; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128] THEN
    SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
             DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH;
             WORD_SUBWORD_TRIVIAL] THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ABBREV_TAC `c0_lo:64 word = word_subword ((word_xor prev_tag ct0):int128) (0,64)` THEN
    ABBREV_TAC `c0_hi:64 word = word_subword ((word_xor prev_tag ct0):int128) (64,64)` THEN
    ABBREV_TAC `c1_lo:64 word = word_subword (ct1:int128) (0,64)` THEN
    ABBREV_TAC `c1_hi:64 word = word_subword (ct1:int128) (64,64)` THEN
    ABBREV_TAC `c2_lo:64 word = word_subword (ct2:int128) (0,64)` THEN
    ABBREV_TAC `c2_hi:64 word = word_subword (ct2:int128) (64,64)` THEN
    ABBREV_TAC `c3_lo:64 word = word_subword (ct3:int128) (0,64)` THEN
    ABBREV_TAC `c3_hi:64 word = word_subword (ct3:int128) (64,64)` THEN
    ABBREV_TAC `H0_LO:64 word = word_subword (h_power (ghash_twist h) 0) (0,64)` THEN
    ABBREV_TAC `H0_HI:64 word = word_subword (h_power (ghash_twist h) 0) (64,64)` THEN
    ABBREV_TAC `H1_LO:64 word = word_subword (h_power (ghash_twist h) 1) (0,64)` THEN
    ABBREV_TAC `H1_HI:64 word = word_subword (h_power (ghash_twist h) 1) (64,64)` THEN
    ABBREV_TAC `H2_LO:64 word = word_subword (h_power (ghash_twist h) 2) (0,64)` THEN
    ABBREV_TAC `H2_HI:64 word = word_subword (h_power (ghash_twist h) 2) (64,64)` THEN
    ABBREV_TAC `H3_LO:64 word = word_subword (h_power (ghash_twist h) 3) (0,64)` THEN
    ABBREV_TAC `H3_HI:64 word = word_subword (h_power (ghash_twist h) 3) (64,64)` THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_join (c0_lo:64 word) (c0_hi:64 word):int128)
                              (word_zx (c0_lo:64 word):int128)) (0,64) :64 word) =
      word_xor c0_hi c0_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_zx (c1_lo:64 word):int128)
                              (word_join (c1_lo:64 word) (c1_hi:64 word):int128))
                    (0,64) :64 word) =
      word_xor c1_hi c1_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_subword (word_xor (word_join (c3_lo:64 word) (c3_hi:64 word):int128)
                                                     (word_zx (c3_lo:64 word):int128))
                                           (0,64) :64 word):int128) (0,64) :64 word) =
      word_xor c3_hi c3_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_insert (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                 (64,64)
                                 (word_subword (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                               (0,64) :64 word):int128) (64,64) :64 word) =
      word_xor c2_hi c2_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_xor (H3_LO:64 word) (H3_HI:64 word):64 word)
                    :int128) (0,64) :64 word) = word_xor H3_LO H3_HI` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `Mp_h0:int128 = word_pmul (word_xor (c0_lo:64 word) (c0_hi:64 word))
                                         (word_xor (H3_LO:64 word) (H3_HI:64 word))` THEN
    ABBREV_TAC `Mp_h1:int128 = word_pmul (word_xor (c1_lo:64 word) (c1_hi:64 word))
                                         (word_xor (H2_LO:64 word) (H2_HI:64 word))` THEN
    ABBREV_TAC `Mp_h2:int128 = word_pmul (word_xor (c2_lo:64 word) (c2_hi:64 word))
                                         (word_xor (H1_LO:64 word) (H1_HI:64 word))` THEN
    ABBREV_TAC `Mp_h3:int128 = word_pmul (word_xor (c3_lo:64 word) (c3_hi:64 word))
                                         (word_xor (H0_LO:64 word) (H0_HI:64 word))` THEN
    SUBGOAL_THEN
     `word_xor (c0_hi:64 word) c0_lo = word_xor c0_lo c0_hi /\
      word_xor (c1_hi:64 word) c1_lo = word_xor c1_lo c1_hi /\
      word_xor (c2_hi:64 word) c2_lo = word_xor c2_lo c2_hi /\
      word_xor (c3_hi:64 word) c3_lo = word_xor c3_lo c3_hi` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s175" THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  MAP_EVERY EXISTS_TAC
   [`q1_kmc:int128`; `q2_kmc:int128`; `q3_kmc:int128`;
    `x19_kmc:int64`; `x20_kmc:int64`; `x21_kmc:int64`;
    `x22_kmc:int64`; `x23_kmc:int64`; `x24_kmc:int64`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 prep — promote NIST_FULL_CORRECT (over the body slice mc) to the  *)
(* full kernel mc context.  The slice is `SUB_LIST(0x308, 0x2bc)             *)
(* aes_gcm_enc_kernel_mc`, so any                                            *)
(*   `aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc`                *)
(* implies                                                                   *)
(*   `aligned_bytes_loaded s (word(pc + 0x308)) slice_mc`                    *)
(* and the slice ensures from PC=pc+0x308 to PC=pc+0x308+0x2bc=pc+0x5c4      *)
(* lifts unchanged into the kernel context.                                  *)
(*                                                                           *)
(* The promoted theorem is the body cut for Phase 8's                        *)
(* `ENSURES_WHILE_UP_TAC`: the loop body subgoal arrives with PC=pc+0x308    *)
(* (loop top) and must reach PC=pc+0x5c4 (back-edge instruction) under the   *)
(* same 11-conjunct precondition (H-power table + Q16/Q17 km layout +        *)
(* q4..q7 byteswap identifications).                                         *)
(* ------------------------------------------------------------------------- *)

let SLICE_TO_KERNEL_BODY_LOAD =
  ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
    aes_gcm_enc_kernel_mc aes_gcm_main_loop_body_slice_mc 0x308;;

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x308) /\
              read X2 s = cptr /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x5c4) /\
              read X2 s = word_add cptr (word 64) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3])
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`pc + 0x308:num`; `cptr:int64`; `b0:int128`; `b1:int128`;
                 `b2:int128`; `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
                 `q7_pre:int128`; `q6_pre:int128`; `q12:int128`; `q13:int128`;
                 `q14:int128`; `q15:int128`; `q16:int128`; `q17:int128`;
                 `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
                 `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
                 `rk8:int128`; `rk9:int128`;
                 `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`;
                 `h:int128`; `prev_tag:int128`;
                 `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
                AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_CORRECT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
    REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC;
                fst AES_GCM_ENC_KERNEL_EXEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[fst AES_GCM_ENC_KERNEL_EXEC;
                                NONOVERLAPPING_CLAUSES]) THEN
    NONOVERLAPPING_TAC;
    REWRITE_TAC[ARITH_RULE `(pc + 0x308) + 0x2bc = pc + 0x5c4`] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    GEN_TAC THEN STRIP_TAC THEN
    POP_ASSUM(STRIP_ASSUME_TAC o BETA_RULE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SLICE_TO_KERNEL_BODY_LOAD]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 prep — promote NIST_FULL_PLUS_Q567_CORRECT (with Q5/Q6/Q7 emit-    *)
(* form post-conjuncts) to the full kernel mc context.  Mechanical slice→     *)
(* kernel promotion analogous to NIST_FULL_KERNEL_CORRECT — the proof is the *)
(* same shape (MP_TAC NIST_FULL_PLUS_Q567 + ENSURES_PRECONDITION_THM via     *)
(* SLICE_TO_KERNEL_BODY_LOAD).                                               *)
(*                                                                           *)
(* This is the kernel-level body cut for Phase 8's loop wrapper: the loop    *)
(* body subgoal arrives with PC=pc+0x308 (loop top) and must reach           *)
(* PC=pc+0x5c4 (back-edge) under the same 11-conjunct precondition; the      *)
(* `?q1k...x24k.` existential surfaces the ciphertext-block emit forms from  *)
(* iteration i for use in identifying iteration i+1's pre-conditions.        *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_PLUS_Q567_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x308) /\
              read X2 s = cptr /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x5c4) /\
              read X2 s = word_add cptr (word 64) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3] /\
              (?(q1k:int128) (q2k:int128) (q3k:int128)
                (x19k:int64) (x20k:int64) (x21k:int64)
                (x22k:int64) (x23k:int64) (x24k:int64).
                 read Q5 s = (word_xor (aese q1k rk9)
                               (word_insert
                                 (word_zx x19k :int128)
                                 (64,64)
                                 (word_xor x20k sx14)) :int128) /\
                 read Q6 s = (word_xor (aese q2k rk9)
                               (word_insert
                                 (word_zx x21k :int128)
                                 (64,64)
                                 x22k) :int128) /\
                 read Q7 s = (word_xor (aese q3k rk9)
                               (word_insert
                                 (word_zx x23k :int128)
                                 (64,64)
                                 (word_xor x24k sx14)) :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`pc + 0x308:num`; `cptr:int64`; `b0:int128`; `b1:int128`;
                 `b2:int128`; `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
                 `q7_pre:int128`; `q6_pre:int128`; `q12:int128`; `q13:int128`;
                 `q14:int128`; `q15:int128`; `q16:int128`; `q17:int128`;
                 `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
                 `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
                 `rk8:int128`; `rk9:int128`;
                 `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`;
                 `h:int128`; `prev_tag:int128`;
                 `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
                AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_PLUS_Q567_CORRECT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
    REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC;
                fst AES_GCM_ENC_KERNEL_EXEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[fst AES_GCM_ENC_KERNEL_EXEC;
                                NONOVERLAPPING_CLAUSES]) THEN
    NONOVERLAPPING_TAC;
    REWRITE_TAC[ARITH_RULE `(pc + 0x308) + 0x2bc = pc + 0x5c4`] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    GEN_TAC THEN STRIP_TAC THEN
    POP_ASSUM(STRIP_ASSUME_TAC o BETA_RULE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SLICE_TO_KERNEL_BODY_LOAD]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — main-loop wrapper design notes (for next session).              *)
(*                                                                           *)
(* The Lenc_main_loop body slice covers kernel offsets 0x308..0x5c4 (175     *)
(* instructions, including the back-edge `b.lt .Lenc_main_loop` excluded).   *)
(* `NIST_FULL_KERNEL_CORRECT` (above) discharges this body slice in the     *)
(* kernel mc context.                                                        *)
(*                                                                           *)
(* Loop control (from disasm of `aes_gcm_enc_kernel_aes128.o`):             *)
(*                                                                           *)
(*   Prelude (offsets 0x00..0x244):                                          *)
(*     0x3c: add  x4, x0, x1, lsr #3   ; x4 = end_input_ptr = x0 + byte_len *)
(*     0x40: lsr  x5, x1, #3            ; x5 = byte_len                      *)
(*     0x50: sub  x5, x5, #1            ; x5 = byte_len - 1                  *)
(*     0x58: and  x5, x5, #~0x3f        ; x5 = floor((byte_len-1)/64) * 64   *)
(*     0x60: add  x5, x5, x0            ; x5 = x0_init + (byte_len-1) AND ~63*)
(*           ; ===> loop bound; x0 advances by 0x40 per main_loop iter.      *)
(*     0x244: cmp  x0, x5                                                    *)
(*     0x248: b.ge .Lenc_prepretail     ; skip main_loop if no iters left   *)
(*     0x308: .Lenc_main_loop:          ; loop top                           *)
(*       ...                                                                 *)
(*     0x4f8: add  x0, x0, #0x40        ; advance plaintext ptr              *)
(*     0x504: cmp  x0, x5                                                    *)
(*     0x5c4: b.lt .Lenc_main_loop      ; backedge                           *)
(*     0x5c8: ...                       ; fallthrough to prepretail          *)
(*                                                                           *)
(* The main loop runs `N = (byte_len - 1) DIV 64` times after the prelude   *)
(* has handled the first 4-block iteration.  When `byte_len < 64` (fewer    *)
(* than one full 4-block iteration), the prelude's b.ge at 0x244 skips the *)
(* main loop entirely (this is the `Lenc_finish_first_blocks` path).        *)
(*                                                                           *)
(* Loop tactic choice (per agent-guide.md "Loops" section):                  *)
(*   - Backedge is `cmp x0, x5; b.lt`, a flag-conditional backedge: the     *)
(*     loop continues while X0 < X5.  This is post-form (q i s captures a   *)
(*     flag fact at the `b.lt`).                                             *)
(*   - Two natural counter conventions are available:                        *)
(*     (a) PUP:  index i = 0..N where N is the total number of main-loop   *)
(*         iterations.  The loop top is at i, the back-edge proves          *)
(*         `i+1 <= N`.  At Init, i=0 (after-prelude state).                  *)
(*     (b) PAUP: index i = a..b where the index IS the X0 value (or some    *)
(*         linear function of it).  Used when the counter is "naturally"    *)
(*         arbitrary-start.                                                  *)
(*   - **Decision: PUP** (post-form, 0..N counter).                          *)
(*       Justification:                                                      *)
(*       * Reviewer 039 flagged AES-XTS at `arm_xts_encrypt.ml:3521` as    *)
(*         using PAUP for an analogous cmp/b.lt back-edge.  We compared    *)
(*         the two precedents:                                              *)
(*         - AES-XTS uses PAUP with explicit `0..val(num_5blocks:int64)`   *)
(*           bounds; the counter `i` is the LOGICAL block index, with the  *)
(*           pointer `X0 = ptxt_p + 0x50*i`.  PAUP's `a..b` bounds let    *)
(*           the proof express the loop bound `b = val num_5blocks` as a   *)
(*           free `int64` value (not a `num`).                              *)
(*         - Our case is structurally identical EXCEPT that:                *)
(*           (1) Phase 7's body cut already takes `cptr:int64` as an        *)
(*               abstract pointer free of the X0 mapping (the cut treats   *)
(*               X2, the ciphertext output ptr).  X0 is just one of           *)
(*               many MAYCHANGE registers.                                   *)
(*           (2) The kernel's loop bound N can be expressed as the `num`   *)
(*               quantity `(byte_len - 1) DIV 64` since `byte_len` is a    *)
(*               concrete arithmetic value derived from X1.                 *)
(*       * Both PUP and PAUP work; PUP is simpler when the counter type    *)
(*         is uniformly `num` (which is our case: index i ranges over     *)
(*         `0..N`).  PAUP would force the counter to be `int64` to match    *)
(*         X0's type, which is unnecessarily complicating.                  *)
(*       * Counter goes from 0 to N (i = number of fully-completed         *)
(*         iterations; X0 advances by 64 per iteration; X0_at_top_of_iter  *)
(*         = X0_post_prelude + 64*i).                                        *)
(*                                                                           *)
(* Loop invariant (sketch — to be authored next session):                    *)
(*                                                                           *)
(*   `\i s. ... /\ (read ZF s <=> i = N)` where the body invariant carries: *)
(*     - `read X0 s = word_add x0_init (word (0x40 * i + 0x40))`             *)
(*       (advanced by 64*(i+1) after the prelude consumes block 0)           *)
(*     - `read X2 s = word_add x2_init (word (0x40 * i + 0x40))`             *)
(*     - `read X5 s = x5_loop_bound`                                         *)
(*     - `read X12 s = word (counter32_init + 4*(i+1))`  (BE32 counter)      *)
(*     - `read Q11 s = byteswap128 (ghash_polyval_acc h prev_tag             *)
(*           (TAKE (4*(i+1)) ciphertext_blocks))`  (running tag)              *)
(*     - `read Q12 s = byteswap128 (h_power (ghash_twist h) 0) /\ ...`       *)
(*       (H-power table, iteration-invariant)                                *)
(*     - `read Q16 s = word_join (km h^1) (km h^0) /\                       *)
(*       read Q17 s = word_join (km h^3) (km h^2)`                          *)
(*       (km layout, iteration-invariant)                                    *)
(*     - `read Q18 s = rk0 /\ ... /\ read Q26 s = rk8 /\                    *)
(*       read Q31 s = rk9` (round keys, iteration-invariant)                 *)
(*     - `read Q4 s = aes_gcm_rev64_int128_inv (...prev_iter ct0...)` etc.  *)
(*       (4 byteswap identifications matching NIST_FULL_KERNEL_CORRECT's    *)
(*       precondition shape)                                                 *)
(*     - quantified memory: plaintext bytes preserved + ciphertext-written  *)
(*       so far (use FIRST_ASSUM, not FIRST_X_ASSUM, per SHA-256 retro).    *)
(*                                                                           *)
(* Phase 8 subgoals (per ENSURES_WHILE_PUP_TAC):                              *)
(*   1. Init  (PC 0x308 invariant at i=0)  — from prelude exit state         *)
(*   2. Body  (one iteration via NIST_FULL_KERNEL_CORRECT + memory write +   *)
(*             counter/ptr advance bookkeeping)                              *)
(*   3. Backedge (the `b.lt` instruction at 0x5c4 → 0x308 if i < N)         *)
(*   4. Exit  (the `b.lt` fallthrough at 0x5c8, no further work in loop)    *)
(*                                                                           *)
(* The Init subgoal is the largest unknown — the prelude's first 4-block    *)
(* iteration must produce all the loop-invariant facts.  May need to land   *)
(* a separate "prelude correctness" theorem before the loop wrapper itself  *)
(* can be proved.                                                            *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)
(* Phase 8 BLOCKER status (RESOLVED Sessions 041 + 042):                     *)
(*                                                                           *)
(* Original problem: `NIST_FULL_KERNEL_CORRECT`'s post does NOT assert       *)
(* Q5/Q6/Q7 at loop-body exit, so the loop invariant cannot carry the       *)
(* `aes_gcm_rev64_int128 q5_pre = byteswap128 ct1` byteswap identifications *)
(* needed by the body precondition at iteration i+1.                        *)
(*                                                                           *)
(* Resolution chain (per Path 1 endorsed by reviewer 041 — parallel cuts    *)
(* alongside originals, non-destructive):                                    *)
(*                                                                           *)
(*   * KERNEL_MODULO_PLUS_Q567_CORRECT (s041, line ~4481): same body slice  *)
(*     as KERNEL_MODULO_COMPOSED but with Q5/Q6/Q7 in raw simulator emit    *)
(*     form `word_xor (aese qi rk9) (word_insert (word_zx xj) (64,64) xk)`. *)
(*                                                                           *)
(*   * AES_GCM_REV64_OF_EMIT_FORM (s041, aes_gcm_bridge.ml line ~203):      *)
(*     algebraic identity decomposing aes_gcm_rev64_int128 of the emit     *)
(*     form into word_join'd byte-reversed XORs of half-AES output with    *)
(*     half-plaintext-derived value.                                        *)
(*                                                                           *)
(*   * NIST_SPEC_FORM_PLUS_Q567_CORRECT (s042, line ~4707): wraps           *)
(*     KERNEL_MODULO_PLUS_Q567 with KERNEL_4BLOCK_NIST_BRIDGE_LASSOC,       *)
(*     surfacing both `Q11 = nist_ghash` and Q5/Q6/Q7 emit forms.            *)
(*                                                                           *)
(*   * NIST_FULL_PLUS_Q567_CORRECT (s042, line ~5471): composes DISCHARGE  *)
(*     (0..0x1c8) with NIST_SPEC_FORM_PLUS_Q567 (0x1c8..0x2bc) over the    *)
(*     full body slice.  Post existentially quantifies the s114-boundary   *)
(*     values of Q1/Q2/Q3 and X19..X24:                                     *)
(*       `?q1k q2k q3k x19k x20k x21k x22k x23k x24k.                       *)
(*           read Q5 s = word_xor (aese q1k rk9) (word_insert ...) /\ ...`  *)
(*                                                                           *)
(*   * NIST_FULL_KERNEL_PLUS_Q567_CORRECT (s042, line ~5887): mechanical   *)
(*     slice→kernel promotion of NIST_FULL_PLUS_Q567 via                    *)
(*     ENSURES_PRECONDITION_THM + SLICE_TO_KERNEL_BODY_LOAD.                *)
(*                                                                           *)
(* Q4 deferral (per reviewer 041 endorsement): Q4 is overwritten by         *)
(* `ldp x6,x7,[x0]; fmov d4, x6; fmov v4.d[1], x7` at the very top of the  *)
(* next iteration, so its iteration-to-iteration value never needs byteswap*)
(* relation to a previous ciphertext.  The loop invariant uses an          *)
(* existential `?q4. read Q4 s = q4` to defer Q4 entirely.                 *)
(*                                                                           *)
(* Loop wrapper status: now unblocked.  Use NIST_FULL_KERNEL_PLUS_Q567_CORRECT*)
(* as the Body subgoal cut.  The loop invariant's q5/q6/q7 byteswap        *)
(* identifications are re-established at iteration i+1's loop top by       *)
(* applying AES_GCM_REV64_OF_EMIT_FORM to iteration i's exit Q5/Q6/Q7      *)
(* emit forms (witnessed by the existential q1k..x24k from the Body cut).  *)
(* The remaining algebraic gap (kernel emit form ↔ AES-GCM-CTR ciphertext  *)
(* spec) is independent of the loop machinery and can land any time.       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Phase 8 — X0/X5/flag tracking for ENSURES_WHILE_PUP_TAC (s043 finding).  *)
(*                                                                           *)
(* PROBLEM: ENSURES_WHILE_PUP_TAC (the committed loop-tactic per design     *)
(* notes above) needs the body subgoal to reach pc2 = pc+0x5c4 with a       *)
(* "q (i+1) s" conjunct — typically a flag fact like                        *)
(*                                                                           *)
(*   condition_semantics Condition_LT s <=> i + 1 < N                       *)
(*                                                                           *)
(* (b.lt at 0x5c4 takes the back-edge iff signed less-than holds).          *)
(* But NIST_FULL_KERNEL_PLUS_Q567_CORRECT's MAYCHANGE includes SOME_FLAGS    *)
(* AND X0 — both are "lost" at the body-cut post.  The cut's pre also       *)
(* doesn't bind X0 or X5 (only X2 = cptr is bound).  So the body cut alone  *)
(* cannot supply q (i+1).                                                   *)
(*                                                                           *)
(* SOLUTION SHAPE (validated empirically in s027, see "STATUS" below):     *)
(*                                                                           *)
(* Author a new strengthened body cut                                       *)
(* `AES_GCM_MAIN_LOOP_BODY_X0_X5_FLAG_KERNEL_CORRECT` that adds X0/X5 to    *)
(* pre and X0 advance + raw NF/VF flag facts to post:                      *)
(*                                                                           *)
(*   !pc cptr x0_init x5_init.                                             *)
(*     nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64)   *)
(*     ==> ensures arm                                                      *)
(*          (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\ *)
(*               read PC s = word (pc + 0x308) /\                          *)
(*               read X0 s = x0_init /\                                    *)
(*               read X2 s = cptr /\                                        *)
(*               read X5 s = x5_init)                                       *)
(*          (\s. read PC s = word (pc + 0x5c4) /\                          *)
(*               read X0 s = word_add x0_init (word 64) /\                 *)
(*               read X2 s = word_add cptr (word 64) /\                    *)
(*               read X5 s = x5_init /\                                     *)
(*               (read NF s <=>                                              *)
(*                ival (word_sub (word_add x0_init (word 64)) x5_init)     *)
(*                  < &0) /\                                                 *)
(*               (read VF s <=>                                              *)
(*                ~(ival (word_add x0_init (word 64)) - ival x5_init       *)
(*                  = ival (word_sub (word_add x0_init (word 64))          *)
(*                                   x5_init))))                            *)
(*          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,                  *)
(*           MAYCHANGE [memory :> bytes(cptr, 64)] ,,                       *)
(*           MAYCHANGE [events])                                              *)
(*                                                                           *)
(* PROOF STRATEGY (validated in s027): straightforward ARM_STEPS_TAC over  *)
(* the entire 175-instr body, since X0/X5/flags fall out naturally from    *)
(* the simulator's per-instruction state-update facts:                      *)
(*                                                                           *)
(*   REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN         *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;                   *)
(*                               fst AES_GCM_ENC_KERNEL_EXEC]) THEN        *)
(*   ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC (1--175) THEN                  *)
(*   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN                  *)
(*   <MAYCHANGE close>                                                      *)
(*                                                                           *)
(* RUNTIME: 175 ARM_STEPS over the kernel mc takes ~9s wall-clock in s027 *)
(* (well within budget; the ASES/PMULL/AESMC instructions are the bulk).   *)
(* ASM_REWRITE_TAC closes PC, X0, X2, X5, NF, VF post-conjuncts; only the *)
(* MAYCHANGE goal remains.                                                  *)
(*                                                                           *)
(* MAYCHANGE CLOSE (the open detail s043 ran out of time on):              *)
(*                                                                           *)
(* The simulator-produced MAYCHANGE has memory writes as 4 separate         *)
(* `bytes128` chunks (cptr+0/+16/+32/+48), but the goal's MAYCHANGE wants   *)
(* `bytes(cptr, 64)` (single 64-byte region).  Plain MONOTONE_MAYCHANGE_TAC *)
(* does NOT merge bytes128 chunks → bytes(.,64).  Two paths to investigate: *)
(*                                                                           *)
(*   (a) State the MAYCHANGE in the new cut's POST as 4 bytes128 chunks    *)
(*       (matching simulator output) instead of bytes(cptr,64).  Closes    *)
(*       cleanly.  Downstream consumers (the loop wrapper) then need to    *)
(*       merge.  But this propagates the 4-chunk form upward into the      *)
(*       loop invariant's quantified-memory predicate, which is awkward.   *)
(*                                                                           *)
(*   (b) Compose with NIST_FULL_KERNEL_PLUS_Q567_CORRECT via ARM_BIGSTEP   *)
(*       to inherit `bytes(cptr, 64)` MAYCHANGE.  The composed proof:      *)
(*                                                                           *)
(*         REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN  *)
(*         MP_TAC (SPECL [...] NIST_FULL_KERNEL_PLUS_Q567_CORRECT) THEN   *)
(*         ANTS_TAC THENL [...; ALL_TAC] THEN                              *)
(*         ARM_BIGSTEP_TAC AES_GCM_ENC_KERNEL_EXEC "s175" THEN            *)
(*         ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]                 *)
(*                                                                           *)
(*       However, ARM_BIGSTEP loses X0/flag info (they're in MAYCHANGE);   *)
(*       so we'd need an additional independent X0/flag-only cut to        *)
(*       establish them at s175.  Two cuts, double the symbolic exec cost. *)
(*                                                                           *)
(* RECOMMENDED PATH for s044+: pick (a) — author the cut with bytes128     *)
(* chunks in MAYCHANGE — this closes cleanly with one ARM_STEPS_TAC pass.  *)
(* The loop invariant downstream then has bytes128-chunked quantified      *)
(* memory predicate, which is fine for a 4-block iteration where the       *)
(* natural granularity is 16-byte ciphertext blocks.                       *)
(*                                                                           *)
(* LOOP WRAPPER STRUCTURE (per ENSURES_WHILE_PUP_TAC, s044+):              *)
(*                                                                           *)
(*   ENSURES_WHILE_PUP_TAC                                                  *)
(*     `N:num`           -- number of body iters; expressed via X5/X0_init  *)
(*     `pc + 0x308`      (* loop top *)                                     *)
(*     `pc + 0x5c4`      (* back-edge *)                                    *)
(*     `\i s. <state invariant — see PHASE 8 wrapper sketch above> /\      *)
(*            (read NF s <=> ...) /\ (read VF s <=> ...)`                  *)
(*     `\i s. condition_semantics Condition_LT s <=> i < N`                *)
(*                                                                           *)
(* Body subgoal: applies AES_GCM_MAIN_LOOP_BODY_X0_X5_FLAG_KERNEL_CORRECT  *)
(* AND NIST_FULL_KERNEL_PLUS_Q567_CORRECT (for the spec post).  Two-cut    *)
(* composition.                                                             *)
(*                                                                           *)
(* STATUS (s044 close): Path (a) LANDED.                                   *)
(*   - ARM_STEPS_TAC over all 175 instr in kernel mc context: WORKS (~9s). *)
(*   - X0/X5/X2/NF/VF post-conjuncts close via ASM_REWRITE_TAC: WORKS.    *)
(*   - MAYCHANGE close: REWRITE_TAC[SOME_FLAGS] THEN                       *)
(*     MONOTONE_MAYCHANGE_TAC closes when the goal MAYCHANGE lists Q0..Q11 *)
(*     explicitly (matching simulator output) instead of                   *)
(*     MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI (which tightens Q8..Q15  *)
(*     to tophalf-only, rejecting the simulator's full-Q8 update).         *)
(* ------------------------------------------------------------------------- *)

(* AES_GCM_MAIN_LOOP_BODY_X0_X5_FLAG_KERNEL_CORRECT — kernel-level body cut *)
(* asserting X0/X5/X2 advance + raw NF/VF flag facts at body exit          *)
(* (pc + 0x5c4).  Companion to NIST_FULL_KERNEL_PLUS_Q567_CORRECT for the  *)
(* ENSURES_WHILE_PUP_TAC body subgoal: PUP needs `q (i+1) s` in flag form, *)
(* which the spec-side body cut cannot supply (X0/X5 not in pre, SOME_FLAGS*)
(* in MAYCHANGE).  This cut takes X0/X5 as free preconditions and exposes  *)
(* the raw NF/VF post-cmp values at the back-edge.                         *)
let AES_GCM_MAIN_LOOP_BODY_X0_X5_FLAG_KERNEL_CORRECT = prove
 (`!pc cptr x0_init x5_init.
    nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x308) /\
              read X0 s = x0_init /\
              read X2 s = cptr /\
              read X5 s = x5_init)
         (\s. read PC s = word (pc + 0x5c4) /\
              read X0 s = word_add x0_init (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_init /\
              (read NF s <=>
               ival (word_sub (word_add x0_init (word 64)) x5_init) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_init (word 64)) - ival x5_init =
                 ival (word_sub (word_add x0_init (word 64)) x5_init))))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16));
                     memory :> bytes128 (word_add cptr (word 32));
                     memory :> bytes128 (word_add cptr (word 48))] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_ENC_KERNEL_EXEC]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC (1--175) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* X0_X5_FLAG_LOADED — same body cut but with aligned_bytes_loaded asserted *)
(* in the post.  ENSURES_WHILE_PUP_TAC's body subgoal post asserts          *)
(* aligned_bytes_loaded (it's part of the program_decodes conjunct);         *)
(* without it in the cut's post we can't bridge to the wrapper.  The proof  *)
(* spine is identical — ASM_REWRITE_TAC carries it from pre via the frame.  *)
(* (s047 finding: the kernel-level cut needs aligned_bytes_loaded in post.) *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_X0_X5_FLAG_LOADED_KERNEL_CORRECT = prove
 (`!pc cptr x0_init x5_init.
    nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x308) /\
              read X0 s = x0_init /\
              read X2 s = cptr /\
              read X5 s = x5_init)
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x5c4) /\
              read X0 s = word_add x0_init (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_init /\
              (read NF s <=>
               ival (word_sub (word_add x0_init (word 64)) x5_init) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_init (word 64)) - ival x5_init =
                 ival (word_sub (word_add x0_init (word 64)) x5_init))))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16));
                     memory :> bytes128 (word_add cptr (word 32));
                     memory :> bytes128 (word_add cptr (word 48))] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_ENC_KERNEL_EXEC]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC (1--175) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — back-edge cut for ENSURES_WHILE_PUP_TAC.                        *)
(*                                                                           *)
(* The b.lt at offset 0x5c4 is a 1-instruction back-edge that jumps to       *)
(* offset 0x308 when condition_semantics Condition_LT holds (i.e.            *)
(* `~(read NF s <=> read VF s)`).  In the PUP wrapper, the back-edge         *)
(* subgoal goes from `pc + 0x5c4` (with the loop invariant `p i s` and the  *)
(* flag fact `q i s`) to `pc + 0x308` (with `p i s` preserved).              *)
(*                                                                           *)
(* Because the b.lt only modifies PC and events, all other components of    *)
(* the loop invariant are preserved trivially via the MAYCHANGE frame        *)
(* `MAYCHANGE [PC] ,, MAYCHANGE [events]`.  So the wrapper's back-edge       *)
(* subgoal can be discharged by stepping the b.lt and applying the          *)
(* invariant preservation.  This minimal form, parameterised only on X0     *)
(* (an example of what the invariant carries), exhibits the proof spine.    *)
(*                                                                           *)
(* Validated in s027 (~26 ms wall-clock).                                    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BACKEDGE_KERNEL_CORRECT = prove
 (`!pc x0_init.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
           read PC s = word (pc + 0x5c4) /\
           read X0 s = x0_init /\
           condition_semantics Condition_LT s)
      (\s. read PC s = word (pc + 0x308) /\
           read X0 s = x0_init)
      (MAYCHANGE [PC] ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[condition_semantics]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — NF/VF emit-form to signed-LT translation lemma.                 *)
(*                                                                           *)
(* The X0/X5/flag body cut emits NF/VF as raw simulator forms:               *)
(*   read NF s <=> ival (word_sub a b) < &0                                  *)
(*   read VF s <=> ~(ival a - ival b = ival (word_sub a b))                  *)
(* Condition_LT semantics is `~(NF <=> VF)`, so combining yields:            *)
(*   condition_semantics Condition_LT s                                      *)
(*     <=> ~(ival(word_sub a b) < &0 <=>                                     *)
(*           ~(ival a - ival b = ival (word_sub a b)))                       *)
(*                                                                           *)
(* This lemma rewrites that combined form into the much simpler signed-LT    *)
(* `ival a < ival b`, which is what the loop invariant's `q i s` flag fact   *)
(* needs — i.e. `ival (word_add x0_init (word(0x40 * (i+1)))) < ival x5_init` *)
(* relating the iteration counter to the loop bound.                         *)
(*                                                                           *)
(* Proof spine: ICONG_WORD_SUB gives `ival(word_sub a b) ≡ ival a - ival b   *)
(* (mod 2^64)`, expanding the congruence to `… = 2^64 * d`. IVAL_BOUND       *)
(* bounds `ival` in `[-2^63, 2^63)`. Case-split on `d ∈ {-1, 0, 1}`; in each *)
(* case ASM_INT_ARITH_TAC closes; the residual contradicts via               *)
(* INT_ARITH_TAC.                                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* IVAL_WORD_ADD_BOUND — bridge from word-arithmetic precondition to         *)
(* num-arithmetic invariant.  Given val(x0) + 64*N < 2^63 (i.e. the loop    *)
(* range fits in signed-positive 64-bit) and word_add x0 (word(64*N)) = x5, *)
(* the signed-LT comparison `ival(word_add x0 (word(64*(i+1)))) < ival x5`  *)
(* is equivalent to the iteration counter inequality `i+1 < N`.             *)
(*                                                                           *)
(* Used by the PUP wrapper's body subgoal to convert the X0_X5_FLAG cut's   *)
(* signed-LT post (after IVAL_WORD_SUB_NFVF_TO_LT translation) into the     *)
(* `q (i+1) s = condition_semantics Condition_LT s <=> i+1 < N` flag fact   *)
(* the loop invariant carries.                                              *)
(* ------------------------------------------------------------------------- *)

let IVAL_WORD_ADD_BOUND = prove
 (`!(x0:int64) (x5:int64) (i:num) (N:num).
    val x0 + 64 * N < 2 EXP 63 /\
    i < N /\
    word_add x0 (word(64*N)) = x5
    ==> (ival (word_add x0 (word(64*(i+1)))) < ival x5 <=> i + 1 < N)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `val (x5:int64) = val (x0:int64) + 64 * N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    SUBGOAL_THEN `64 * N < 18446744073709551616` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (x0:int64) + 64 * N < 18446744073709551616` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val (word_add (x0:int64) (word(64*(i+1)):int64)) = val (x0:int64) + 64*(i+1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    SUBGOAL_THEN `64 * (i+1) < 18446744073709551616` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (x0:int64) + 64 * (i+1) < 18446744073709551616` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival (word_add (x0:int64) (word(64*(i+1)):int64)) = &(val (x0:int64) + 64 * (i+1))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ival; DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    COND_CASES_TAC THENL
     [REFL_TAC;
      POP_ASSUM MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival (x5:int64) = &(val (x5:int64))` ASSUME_TAC THENL
   [REWRITE_TAC[ival; DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    COND_CASES_TAC THENL
     [REFL_TAC;
      POP_ASSUM MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

let IVAL_WORD_SUB_NFVF_TO_LT = prove
 (`!a b:int64.
    ~(ival(word_sub a b) < &0 <=>
      ~(ival a - ival b = ival(word_sub a b))) <=>
    ival a < ival b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `b:int64`] ICONG_WORD_SUB) THEN
  REWRITE_TAC[DIMINDEX_64; int_congruent; int_divides] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `a:int64` IVAL_BOUND) THEN
  MP_TAC(ISPEC `b:int64` IVAL_BOUND) THEN
  MP_TAC(ISPEC `word_sub (a:int64) b` IVAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  CONV_TAC(DEPTH_CONV INT_POW_CONV) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  CONV_TAC(DEPTH_CONV INT_POW_CONV) THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `d:int = &0` THENL
  [POP_ASSUM SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC;
   ASM_CASES_TAC `d:int = &1` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC;
    ASM_CASES_TAC `d:int = -- &1` THENL
    [POP_ASSUM SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC;
     SUBGOAL_THEN `F` MP_TAC THENL
     [ASM_INT_ARITH_TAC; MESON_TAC[]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — kernel-level main-loop wrapper SKELETON                          *)
(*                                                                           *)
(* AES_GCM_MAIN_LOOP_WRAPPER_SKELETON_CORRECT — first wrapper landed for the *)
(* AES-GCM encryption kernel's main loop (offsets 0x308..0x5c4..0x5c8).      *)
(*                                                                           *)
(* SCOPE (s047): this is a SKELETON — the loop invariant carries only       *)
(* X0/X2/X5 advance facts and the Condition_LT flag.  It does NOT carry     *)
(* spec-level facts (Q11 = nist_ghash, byteswap identifications, H-power   *)
(* table, round-key table, plaintext/ciphertext memory layout).             *)
(* The skeleton's purpose is to validate the wrapper construction chain —   *)
(* especially the body-subgoal proof using two existing cuts via the        *)
(* ENSURES_FRAME_SUBSUMED + ENSURES_PREPOSTCONDITION_THM bridging pattern.   *)
(*                                                                           *)
(* PRECONDITIONS:                                                            *)
(*   ~(N = 0)                                                                *)
(*   nonoverlapping (word pc, kernel_mc) (cptr, 64*N)                       *)
(*   word_add x0_init (word(64*N)) = x5_init     (loop bound at end)        *)
(*   val x0_init + 64 * N < 2 EXP 63             (no signed overflow)       *)
(*                                                                           *)
(* The signed-overflow precondition is real: if val x0_init + 64*N ≥ 2^63,  *)
(* the b.lt at offset 0x5c4 would compare signed-negative addresses, and    *)
(* the iteration counter mapping breaks down.                               *)
(*                                                                           *)
(* SUBSEQUENT WORK: extend the loop invariant to carry spec-level facts.    *)
(* Each extension is a separate stronger wrapper that builds on this one    *)
(* via ENSURES_FRAME_SUBSUMED + a strengthened cut — same structural       *)
(* pattern.  Q-state spec facts come from NIST_FULL_KERNEL_PLUS_Q567_CORRECT *)
(* (already in tree); these can be threaded through by a parallel cut       *)
(* application in the body subgoal.                                          *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_WRAPPER_SKELETON_CORRECT = prove
 (`!pc (cptr:int64) (x0_init:int64) (x5_init:int64) (N:num).
   ~(N = 0) /\
   nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64*N) /\
   word_add x0_init (word(64*N)) = x5_init /\
   val x0_init + 64 * N < 2 EXP 63
   ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
             read PC s = word (pc + 0x308) /\
             read X0 s = x0_init /\
             read X2 s = cptr /\
             read X5 s = x5_init)
        (\s. read PC s = word (pc + 0x5c8) /\
             read X0 s = x5_init /\
             read X2 s = word_add cptr (word(64*N)) /\
             read X5 s = x5_init)
        (MAYCHANGE [PC] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
         MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
         MAYCHANGE SOME_FLAGS ,,
         MAYCHANGE [memory :> bytes(cptr, 64*N)] ,,
         MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `N:num` `pc + 0x308` `pc + 0x5c4`
    `\i s. (read X0 s = word_add x0_init (word(64*i)) /\
            read X2 s = word_add cptr (word(64*i)) /\
            read X5 s = x5_init) /\
           (condition_semantics Condition_LT s <=> i < N)` THEN
  (* Goal 1: ~(N = 0) *)
  ASM_REWRITE_TAC[] THEN
  (* Split (Init) /\ (Body) /\ (Backedge) /\ (Exit) *)
  CONJ_TAC THENL
   [(* Init subgoal *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; WORD_VAL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* Body subgoal *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC (SPECL [`pc:num`; `word_add cptr (word(64*i)):int64`;
                   `word_add x0_init (word(64*i)):int64`;
                   `x5_init:int64`]
            AES_GCM_MAIN_LOOP_BODY_X0_X5_FLAG_LOADED_KERNEL_CORRECT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst AES_GCM_ENC_KERNEL_EXEC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                                  fst AES_GCM_ENC_KERNEL_EXEC]) THEN
      NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
     `MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
      MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,,
      MAYCHANGE [memory :> bytes128 (word_add cptr (word (64 * i)));
                 memory :> bytes128 (word_add (word_add cptr (word (64 * i))) (word 16));
                 memory :> bytes128 (word_add (word_add cptr (word (64 * i))) (word 32));
                 memory :> bytes128 (word_add (word_add cptr (word (64 * i))) (word 48))] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                                  fst AES_GCM_ENC_KERNEL_EXEC]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    EXISTS_TAC
     `\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
          read PC s = word (pc + 0x308) /\
          read X0 s = word_add x0_init (word(64*i)) /\
          read X2 s = word_add cptr (word(64*i)) /\
          read X5 s = x5_init` THEN
    EXISTS_TAC
     `\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
          read PC s = word (pc + 0x5c4) /\
          read X0 s = word_add (word_add x0_init (word (64 * i))) (word 64) /\
          read X2 s = word_add (word_add cptr (word (64 * i))) (word 64) /\
          read X5 s = x5_init /\
          (read NF s <=>
           ival (word_sub (word_add (word_add x0_init (word (64 * i))) (word 64))
                          x5_init) < &0) /\
          (read VF s <=>
           ~(ival (word_add (word_add x0_init (word (64 * i))) (word 64)) -
             ival x5_init =
             ival (word_sub (word_add (word_add x0_init (word (64 * i))) (word 64))
                            x5_init)))` THEN
    REPEAT CONJ_TAC THEN BETA_TAC THENL
     [(* Pre' ==> Pre *)
      MESON_TAC[];
      (* Post (cut) ==> Post' (goal) *)
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE;
        CONV_TAC WORD_RULE;
        REWRITE_TAC[condition_semantics] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IVAL_WORD_SUB_NFVF_TO_LT] THEN
        SUBGOAL_THEN
         `word_add (word_add x0_init (word (64 * i))) (word 64) =
          word_add x0_init (word(64 * (i+1)):int64)` SUBST1_TAC THENL
         [CONV_TAC WORD_RULE; ALL_TAC] THEN
        MP_TAC (SPECL [`x0_init:int64`; `x5_init:int64`; `i:num`; `N:num`]
                IVAL_WORD_ADD_BOUND) THEN
        ASM_REWRITE_TAC[]];
      (* Original ensures *)
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* Backedge subgoal *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                                fst AES_GCM_ENC_KERNEL_EXEC]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[condition_semantics]) THEN
    ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Exit subgoal *)
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_ENC_KERNEL_EXEC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[condition_semantics; LT_REFL]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 (s048) — strengthened FLAG variants that thread X0/X5/NF/VF       *)
(* through the existing slice cut chain (KERNEL_MODULO → NIST_SPEC_FORM →    *)
(* NIST_FULL → NIST_FULL_KERNEL).  These are needed to extend the loop       *)
(* wrapper invariant to carry both Q11=spec AND X0/X5/flag in a single body  *)
(* cut (avoiding the s046 same-range-composition blocker).                   *)
(*                                                                           *)
(* Rationale (per s032 word_blast_karatsuba_sum_barrier memory): re-running  *)
(* ARM_STEPS_TAC (1--175) at the kernel level + applying the nist_ghash      *)
(* bridge inline would hit WORD_BLAST barrier (karatsuba-sum identity in     *)
(* post).  Instead, thread the X0/X5/NF/VF facts through the existing nested *)
(* slice cut structure — the algebraic identity stays inside the existing   *)
(* DISCHARGE/SPEC_FORM cut wrappers, never reintroduced fresh.               *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_PLUS_Q567_FLAG_CORRECT = prove
 (`!pc (cptr:int64) (q0:int128) (q1:int128) (q2:int128) (q3:int128)
        (q4_in:int128) (q5:int128) (q6:int128) (q9_in:int128) (q10_in:int128)
        (q11_in:int128) (q16:int128) (rk9:int128)
        (x19:int64) (x20:int64) (x21:int64) (x22:int64) (x23:int64)
        (x24:int64) (sx14:int64) (x0_in:int64) (x5_in:int64).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x1c8) /\
              read X2 s = cptr /\
              read Q0 s = q0 /\
              read Q1 s = q1 /\
              read Q2 s = q2 /\
              read Q3 s = q3 /\
              read Q4 s = q4_in /\
              read Q5 s = q5 /\
              read Q6 s = q6 /\
              read Q9 s = q9_in /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in /\
              read Q16 s = q16 /\
              read Q31 s = rk9 /\
              read X0 s = x0_in /\
              read X5 s = x5_in /\
              read X19 s = x19 /\
              read X20 s = x20 /\
              read X21 s = x21 /\
              read X22 s = x22 /\
              read X23 s = x23 /\
              read X24 s = x24 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X0 s = word_add x0_in (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_in /\
              (read NF s <=>
               ival (word_sub (word_add x0_in (word 64)) x5_in) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_in (word 64)) - ival x5_in =
                 ival (word_sub (word_add x0_in (word 64)) x5_in))) /\
              read Q5 s = (word_xor (aese q1 rk9)
                           (word_insert
                             (word_zx x19 :int128)
                             (64,64)
                             (word_xor x20 sx14)) :int128) /\
              read Q6 s = (word_xor (aese q2 rk9)
                           (word_insert
                             (word_zx x21 :int128)
                             (64,64)
                             x22) :int128) /\
              read Q7 s = (word_xor (aese q3 rk9)
                           (word_insert
                             (word_zx x23 :int128)
                             (64,64)
                             (word_xor x24 sx14)) :int128) /\
              read Q11 s = kernel_modulo
                              (word_xor q9_in q5)
                              (word_xor q11_in q6)
                              (word_xor q10_in
                                 (word_pmul (word_subword q4_in (0,64) :64 word)
                                            (word_subword q16 (0,64) :64 word)
                                  :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC (1--61) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[kernel_modulo; byteswap128; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `!h:int128.
       word_subword (word_join h h:256 word) (64,128):int128 =
       word_join (word_subword h (0,64) :64 word)
                 (word_subword h (64,64) :64 word)`
   ASSUME_TAC THENL [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Pinner:int128 =
      word_pmul (word_subword (word_xor (q5:int128) (q9_in:int128)) (0,64)
                 :64 word)
                (word 13979173243358019584:64 word)` THEN
  SUBGOAL_THEN
   `word_xor (q9_in:int128) (q5:int128) = word_xor q5 q9_in /\
    word_xor (q11_in:int128) (q6:int128) = word_xor q6 q11_in /\
    word_xor (q10_in:int128)
             (word_pmul (word_subword (q4_in:int128) (0,64) :64 word)
                        (word_subword (q16:int128) (0,64) :64 word)
              :int128) =
    word_xor (word_pmul (word_subword q4_in (0,64) :64 word)
                        (word_subword q16 (0,64) :64 word) :int128)
             q10_in`
   STRIP_ASSUME_TAC THENL [REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Hxor:int128 = word_xor (q5:int128) (q9_in:int128)` THEN
  ABBREV_TAC `Lxor:int128 = word_xor (q6:int128) (q11_in:int128)` THEN
  ABBREV_TAC
   `Pmid:int128 =
      word_pmul (word_subword (q4_in:int128) (0,64) :64 word)
                (word_subword (q16:int128) (0,64) :64 word)` THEN
  ABBREV_TAC
   `Bswapped:int128 =
      word_join (word_subword (Hxor:int128) (0,64) :64 word)
                (word_subword Hxor (64,64) :64 word)` THEN
  ABBREV_TAC
   `Inner:int128 =
      word_xor (word_xor (Pinner:int128) (Bswapped:int128))
               (word_xor (word_xor (Hxor:int128) (Lxor:int128))
                         (word_xor (Pmid:int128) (q10_in:int128)))` THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor (Pmid:int128) (q10_in:int128))
                       (word_xor (Lxor:int128) (Hxor:int128)))
             (word_xor (Bswapped:int128) (Pinner:int128)) = Inner`
    SUBST1_TAC THENL
   [EXPAND_TAC "Inner" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* NIST_SPEC_FORM_PLUS_Q567_FLAG_CORRECT: thread X0/X5/NF/VF through the    *)
(* SPEC_FORM bridge (offsets 0x1c8..0x2bc of slice mc).                      *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_PLUS_Q567_FLAG_CORRECT = prove
 (`!pc (cptr:int64) (q0:int128) (q1:int128) (q2:int128) (q3:int128)
        (q4_in:int128) (q5:int128) (q6:int128) (q9_in:int128) (q10_in:int128)
        (q11_in:int128) (q16:int128) (rk9:int128)
        (x19:int64) (x20:int64) (x21:int64) (x22:int64) (x23:int64)
        (x24:int64) (sx14:int64)
        (x0_in:int64) (x5_in:int64)
        (h:int128) (prev_tag:int128)
        (ct0:int128) (ct1:int128) (ct2:int128) (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64) /\
    (let h0,l0,m0 =
       karatsuba_components (byteswap128 (word_xor prev_tag ct0))
                            (byteswap128 (h_power (ghash_twist h) 3)) in
     let h1,l1,m1 =
       karatsuba_components (byteswap128 ct1)
                            (byteswap128 (h_power (ghash_twist h) 2)) in
     let h2,l2,m2 =
       karatsuba_components (byteswap128 ct2)
                            (byteswap128 (h_power (ghash_twist h) 1)) in
     let h3,l3,m3 =
       karatsuba_components (byteswap128 ct3)
                            (byteswap128 (h_power (ghash_twist h) 0)) in
     word_xor q9_in q5 = word_xor (word_xor (word_xor h0 h1) h2) h3 /\
     word_xor q11_in q6 = word_xor (word_xor (word_xor l0 l1) l2) l3 /\
     word_xor q10_in
              (word_pmul (word_subword q4_in (0,64) :64 word)
                         (word_subword q16 (0,64) :64 word) :int128) =
     word_xor (word_xor (word_xor m0 m1) m2) m3)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                  aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x1c8) /\
              read X2 s = cptr /\
              read Q0 s = q0 /\
              read Q1 s = q1 /\
              read Q2 s = q2 /\
              read Q3 s = q3 /\
              read Q4 s = q4_in /\
              read Q5 s = q5 /\
              read Q6 s = q6 /\
              read Q9 s = q9_in /\
              read Q10 s = q10_in /\
              read Q11 s = q11_in /\
              read Q16 s = q16 /\
              read Q31 s = rk9 /\
              read X0 s = x0_in /\
              read X5 s = x5_in /\
              read X19 s = x19 /\
              read X20 s = x20 /\
              read X21 s = x21 /\
              read X22 s = x22 /\
              read X23 s = x23 /\
              read X24 s = x24 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X0 s = word_add x0_in (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_in /\
              (read NF s <=>
               ival (word_sub (word_add x0_in (word 64)) x5_in) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_in (word 64)) - ival x5_in =
                 ival (word_sub (word_add x0_in (word 64)) x5_in))) /\
              read Q5 s = (word_xor (aese q1 rk9)
                           (word_insert
                             (word_zx x19 :int128)
                             (64,64)
                             (word_xor x20 sx14)) :int128) /\
              read Q6 s = (word_xor (aese q2 rk9)
                           (word_insert
                             (word_zx x21 :int128)
                             (64,64)
                             x22) :int128) /\
              read Q7 s = (word_xor (aese q3 rk9)
                           (word_insert
                             (word_zx x23 :int128)
                             (64,64)
                             (word_xor x24 sx14)) :int128) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3])
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cptr:int64`; `q0:int128`; `q1:int128`;
                `q2:int128`; `q3:int128`;
                `q4_in:int128`; `q5:int128`; `q6:int128`;
                `q9_in:int128`; `q10_in:int128`; `q11_in:int128`;
                `q16:int128`; `rk9:int128`;
                `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`;
                `x23:int64`; `x24:int64`; `sx14:int64`;
                `x0_in:int64`; `x5_in:int64`]
               AES_GCM_MAIN_LOOP_BODY_GHASH_KERNEL_MODULO_PLUS_Q567_FLAG_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:int128`; `prev_tag:int128`; `ct0:int128`;
                `ct1:int128`; `ct2:int128`; `ct3:int128`;
                `q5:int128`; `q6:int128`; `q9_in:int128`;
                `q10_in:int128`; `q11_in:int128`; `q4_in:int128`;
                `q16:int128`]
               KERNEL_4BLOCK_NIST_BRIDGE_LASSOC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* ------------------------------------------------------------------------- *)
(* NIST_FULL_PLUS_Q567_FLAG_LOADED_CORRECT: full slice cut over offsets     *)
(* 0..0x2bc combining DISCHARGE (114 instrs, X0/X5/flag preserved) +        *)
(* NIST_SPEC_FORM_PLUS_Q567_FLAG (61 instrs, where X0 advances).            *)
(* "_LOADED" suffix indicates aligned_bytes_loaded for slice_mc carried in  *)
(* the post (needed for downstream wrapper body subgoal which has           *)
(* program_decodes/aligned_bytes_loaded in its goal post per PUP machinery).*)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_PLUS_Q567_FLAG_LOADED_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (x0_in:int64) (x5_in:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
              read PC s = word pc /\
              read X2 s = cptr /\
              read X0 s = x0_in /\
              read X5 s = x5_in /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
              read PC s = word (pc + 0x2bc) /\
              read X0 s = word_add x0_in (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_in /\
              (read NF s <=>
               ival (word_sub (word_add x0_in (word 64)) x5_in) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_in (word 64)) - ival x5_in =
                 ival (word_sub (word_add x0_in (word 64)) x5_in))) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3] /\
              (?(q1k:int128) (q2k:int128) (q3k:int128)
                (x19k:int64) (x20k:int64) (x21k:int64)
                (x22k:int64) (x23k:int64) (x24k:int64).
                 read Q5 s = (word_xor (aese q1k rk9)
                               (word_insert
                                 (word_zx x19k :int128)
                                 (64,64)
                                 (word_xor x20k sx14)) :int128) /\
                 read Q6 s = (word_xor (aese q2k rk9)
                               (word_insert
                                 (word_zx x21k :int128)
                                 (64,64)
                                 x22k) :int128) /\
                 read Q7 s = (word_xor (aese q3k rk9)
                               (word_insert
                                 (word_zx x23k :int128)
                                 (64,64)
                                 (word_xor x24k sx14)) :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL[`pc:num`; `b0:int128`; `b1:int128`; `b2:int128`;
               `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
               `q7_pre:int128`; `q6_pre:int128`;
               `q12:int128`; `q13:int128`; `q14:int128`; `q15:int128`;
               `q16:int128`; `q17:int128`;
               `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
               `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
               `rk8:int128`;
               `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_DISCHARGE_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s114" THEN
  ABBREV_TAC `q0_kmc:int128 = read Q0 s114` THEN
  ABBREV_TAC `q1_kmc:int128 = read Q1 s114` THEN
  ABBREV_TAC `q2_kmc:int128 = read Q2 s114` THEN
  ABBREV_TAC `q3_kmc:int128 = read Q3 s114` THEN
  ABBREV_TAC `x19_kmc:int64 = read X19 s114` THEN
  ABBREV_TAC `x20_kmc:int64 = read X20 s114` THEN
  ABBREV_TAC `x21_kmc:int64 = read X21 s114` THEN
  ABBREV_TAC `x22_kmc:int64 = read X22 s114` THEN
  ABBREV_TAC `x23_kmc:int64 = read X23 s114` THEN
  ABBREV_TAC `x24_kmc:int64 = read X24 s114` THEN
  MP_TAC(SPECL[`pc:num`; `cptr:int64`;
   `q0_kmc:int128`; `q1_kmc:int128`; `q2_kmc:int128`; `q3_kmc:int128`;
   `(word_zx (word_subword
      (word_xor (aes_gcm_rev64_int128 q7_pre)
      (word_zx (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
       :int128))
     (0,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
               (word_subword (q12:int128) (64,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (0,64) :64 word)
               (word_subword (q12:int128) (0,64) :64 word) :int128):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (64,64) :64 word)
          (word_subword (q15:int128) (64,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word)
          (word_subword (q14:int128) (64,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word)
        (word_subword (q13:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor
              (word_xor (aes_gcm_rev64_int128 q4_pre)
                        (byteswap128 q11_pre))
              (word_zx
                (word_subword
                  (word_xor (aes_gcm_rev64_int128 q4_pre)
                            (byteswap128 q11_pre))
                  (64,64) :64 word) :int128))
            (0,64) :64 word)
          (word_subword
            (word_zx (word_subword (q17:int128) (64,64) :64 word) :int128)
            (0,64) :64 word) :int128)
        (word_pmul
          (word_subword
            (word_xor
              (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre)
                                     (64,64) :64 word) :int128)
              (aes_gcm_rev64_int128 q5_pre)) (0,64) :64 word)
          (word_subword (q17:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword
          (word_insert
            (word_zx
              (word_xor
                (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                              :64 word)
                (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                              :64 word) :64 word) :int128)
            (64,64)
            (word_subword
              (word_subword
                (word_zx
                  (word_xor
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                                  :64 word)
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                                  :64 word) :64 word) :int128)
                (0,64) :64 word) (0,64) :64 word) :int128) (64,64)
          :64 word)
        (word_subword (q16:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (0,64) :64 word)
          (word_subword (q15:int128) (0,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word)
          (word_subword (q14:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word)
        (word_subword (q13:int128) (0,64) :64 word) :int128)):int128`;
   `q16:int128`; `rk9:int128`;
   `x19_kmc:int64`; `x20_kmc:int64`; `x21_kmc:int64`;
   `x22_kmc:int64`; `x23_kmc:int64`; `x24_kmc:int64`; `sx14:int64`;
   `x0_in:int64`; `x5_in:int64`;
   `h:int128`; `prev_tag:int128`;
   `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_PLUS_Q567_FLAG_CORRECT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[karatsuba_components; karatsuba_mid; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128] THEN
    SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
             DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH;
             WORD_SUBWORD_TRIVIAL] THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ABBREV_TAC `c0_lo:64 word = word_subword ((word_xor prev_tag ct0):int128) (0,64)` THEN
    ABBREV_TAC `c0_hi:64 word = word_subword ((word_xor prev_tag ct0):int128) (64,64)` THEN
    ABBREV_TAC `c1_lo:64 word = word_subword (ct1:int128) (0,64)` THEN
    ABBREV_TAC `c1_hi:64 word = word_subword (ct1:int128) (64,64)` THEN
    ABBREV_TAC `c2_lo:64 word = word_subword (ct2:int128) (0,64)` THEN
    ABBREV_TAC `c2_hi:64 word = word_subword (ct2:int128) (64,64)` THEN
    ABBREV_TAC `c3_lo:64 word = word_subword (ct3:int128) (0,64)` THEN
    ABBREV_TAC `c3_hi:64 word = word_subword (ct3:int128) (64,64)` THEN
    ABBREV_TAC `H0_LO:64 word = word_subword (h_power (ghash_twist h) 0) (0,64)` THEN
    ABBREV_TAC `H0_HI:64 word = word_subword (h_power (ghash_twist h) 0) (64,64)` THEN
    ABBREV_TAC `H1_LO:64 word = word_subword (h_power (ghash_twist h) 1) (0,64)` THEN
    ABBREV_TAC `H1_HI:64 word = word_subword (h_power (ghash_twist h) 1) (64,64)` THEN
    ABBREV_TAC `H2_LO:64 word = word_subword (h_power (ghash_twist h) 2) (0,64)` THEN
    ABBREV_TAC `H2_HI:64 word = word_subword (h_power (ghash_twist h) 2) (64,64)` THEN
    ABBREV_TAC `H3_LO:64 word = word_subword (h_power (ghash_twist h) 3) (0,64)` THEN
    ABBREV_TAC `H3_HI:64 word = word_subword (h_power (ghash_twist h) 3) (64,64)` THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_join (c0_lo:64 word) (c0_hi:64 word):int128)
                              (word_zx (c0_lo:64 word):int128)) (0,64) :64 word) =
      word_xor c0_hi c0_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_zx (c1_lo:64 word):int128)
                              (word_join (c1_lo:64 word) (c1_hi:64 word):int128))
                    (0,64) :64 word) =
      word_xor c1_hi c1_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_subword (word_xor (word_join (c3_lo:64 word) (c3_hi:64 word):int128)
                                                     (word_zx (c3_lo:64 word):int128))
                                           (0,64) :64 word):int128) (0,64) :64 word) =
      word_xor c3_hi c3_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_insert (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                 (64,64)
                                 (word_subword (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                               (0,64) :64 word):int128) (64,64) :64 word) =
      word_xor c2_hi c2_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_xor (H3_LO:64 word) (H3_HI:64 word):64 word)
                    :int128) (0,64) :64 word) = word_xor H3_LO H3_HI` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `Mp_h0:int128 = word_pmul (word_xor (c0_lo:64 word) (c0_hi:64 word))
                                         (word_xor (H3_LO:64 word) (H3_HI:64 word))` THEN
    ABBREV_TAC `Mp_h1:int128 = word_pmul (word_xor (c1_lo:64 word) (c1_hi:64 word))
                                         (word_xor (H2_LO:64 word) (H2_HI:64 word))` THEN
    ABBREV_TAC `Mp_h2:int128 = word_pmul (word_xor (c2_lo:64 word) (c2_hi:64 word))
                                         (word_xor (H1_LO:64 word) (H1_HI:64 word))` THEN
    ABBREV_TAC `Mp_h3:int128 = word_pmul (word_xor (c3_lo:64 word) (c3_hi:64 word))
                                         (word_xor (H0_LO:64 word) (H0_HI:64 word))` THEN
    SUBGOAL_THEN
     `word_xor (c0_hi:64 word) c0_lo = word_xor c0_lo c0_hi /\
      word_xor (c1_hi:64 word) c1_lo = word_xor c1_lo c1_hi /\
      word_xor (c2_hi:64 word) c2_lo = word_xor c2_lo c2_hi /\
      word_xor (c3_hi:64 word) c3_lo = word_xor c3_lo c3_hi` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s175" THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  MAP_EVERY EXISTS_TAC
   [`q1_kmc:int128`; `q2_kmc:int128`; `q3_kmc:int128`;
    `x19_kmc:int64`; `x20_kmc:int64`; `x21_kmc:int64`;
    `x22_kmc:int64`; `x23_kmc:int64`; `x24_kmc:int64`] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* NIST_FULL_PLUS_Q567_FLAG_CORRECT (slice) and NIST_FULL_KERNEL_PLUS_Q567_  *)
(* FLAG_CORRECT (kernel): same FLAG cut but WITHOUT aligned_bytes_loaded in *)
(* the post (the _LOADED variant has it for slice_mc, but slice_mc loaded   *)
(* doesn't bridge to kernel_mc loaded; ENSURES_PRECONDITION_THM only        *)
(* handles same posts).  These non-LOADED variants enable the kernel-level *)
(* promotion via the existing ENSURES_PRECONDITION_THM + SLICE_TO_KERNEL_   *)
(* BODY_LOAD pattern.                                                        *)
(*                                                                           *)
(* For the wrapper body subgoal, aligned_bytes_loaded for kernel_mc must    *)
(* be threaded separately (from the wrapper's pre, preserved through the    *)
(* frame because the frame's only memory MAYCHANGE is bytes(cptr,64) which *)
(* is nonoverlapping with the kernel code region).                          *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_PLUS_Q567_FLAG_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (x0_in:int64) (x5_in:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_body_slice_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_body_slice_mc /\
              read PC s = word pc /\
              read X2 s = cptr /\
              read X0 s = x0_in /\
              read X5 s = x5_in /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x2bc) /\
              read X0 s = word_add x0_in (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_in /\
              (read NF s <=>
               ival (word_sub (word_add x0_in (word 64)) x5_in) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_in (word 64)) - ival x5_in =
                 ival (word_sub (word_add x0_in (word 64)) x5_in))) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3] /\
              (?(q1k:int128) (q2k:int128) (q3k:int128)
                (x19k:int64) (x20k:int64) (x21k:int64)
                (x22k:int64) (x23k:int64) (x24k:int64).
                 read Q5 s = (word_xor (aese q1k rk9)
                               (word_insert
                                 (word_zx x19k :int128)
                                 (64,64)
                                 (word_xor x20k sx14)) :int128) /\
                 read Q6 s = (word_xor (aese q2k rk9)
                               (word_insert
                                 (word_zx x21k :int128)
                                 (64,64)
                                 x22k) :int128) /\
                 read Q7 s = (word_xor (aese q3k rk9)
                               (word_insert
                                 (word_zx x23k :int128)
                                 (64,64)
                                 (word_xor x24k sx14)) :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL[`pc:num`; `b0:int128`; `b1:int128`; `b2:int128`;
               `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
               `q7_pre:int128`; `q6_pre:int128`;
               `q12:int128`; `q13:int128`; `q14:int128`; `q15:int128`;
               `q16:int128`; `q17:int128`;
               `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
               `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
               `rk8:int128`;
               `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_DISCHARGE_CORRECT) THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s114" THEN
  ABBREV_TAC `q0_kmc:int128 = read Q0 s114` THEN
  ABBREV_TAC `q1_kmc:int128 = read Q1 s114` THEN
  ABBREV_TAC `q2_kmc:int128 = read Q2 s114` THEN
  ABBREV_TAC `q3_kmc:int128 = read Q3 s114` THEN
  ABBREV_TAC `x19_kmc:int64 = read X19 s114` THEN
  ABBREV_TAC `x20_kmc:int64 = read X20 s114` THEN
  ABBREV_TAC `x21_kmc:int64 = read X21 s114` THEN
  ABBREV_TAC `x22_kmc:int64 = read X22 s114` THEN
  ABBREV_TAC `x23_kmc:int64 = read X23 s114` THEN
  ABBREV_TAC `x24_kmc:int64 = read X24 s114` THEN
  MP_TAC(SPECL[`pc:num`; `cptr:int64`;
   `q0_kmc:int128`; `q1_kmc:int128`; `q2_kmc:int128`; `q3_kmc:int128`;
   `(word_zx (word_subword
      (word_xor (aes_gcm_rev64_int128 q7_pre)
      (word_zx (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
       :int128))
     (0,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (64,64) :64 word)
               (word_subword (q12:int128) (64,64) :64 word) :int128):int128`;
   `(word_pmul (word_subword (aes_gcm_rev64_int128 q7_pre) (0,64) :64 word)
               (word_subword (q12:int128) (0,64) :64 word) :int128):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (64,64) :64 word)
          (word_subword (q15:int128) (64,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (64,64) :64 word)
          (word_subword (q14:int128) (64,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64) :64 word)
        (word_subword (q13:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor
              (word_xor (aes_gcm_rev64_int128 q4_pre)
                        (byteswap128 q11_pre))
              (word_zx
                (word_subword
                  (word_xor (aes_gcm_rev64_int128 q4_pre)
                            (byteswap128 q11_pre))
                  (64,64) :64 word) :int128))
            (0,64) :64 word)
          (word_subword
            (word_zx (word_subword (q17:int128) (64,64) :64 word) :int128)
            (0,64) :64 word) :int128)
        (word_pmul
          (word_subword
            (word_xor
              (word_zx (word_subword (aes_gcm_rev64_int128 q5_pre)
                                     (64,64) :64 word) :int128)
              (aes_gcm_rev64_int128 q5_pre)) (0,64) :64 word)
          (word_subword (q17:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword
          (word_insert
            (word_zx
              (word_xor
                (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                              :64 word)
                (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                              :64 word) :64 word) :int128)
            (64,64)
            (word_subword
              (word_subword
                (word_zx
                  (word_xor
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64)
                                  :64 word)
                    (word_subword (aes_gcm_rev64_int128 q6_pre) (64,64)
                                  :64 word) :64 word) :int128)
                (0,64) :64 word) (0,64) :64 word) :int128) (64,64)
          :64 word)
        (word_subword (q16:int128) (64,64) :64 word) :int128)):int128`;
   `(word_xor
      (word_xor
        (word_pmul
          (word_subword
            (word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre))
            (0,64) :64 word)
          (word_subword (q15:int128) (0,64) :64 word) :int128)
        (word_pmul
          (word_subword (aes_gcm_rev64_int128 q5_pre) (0,64) :64 word)
          (word_subword (q14:int128) (0,64) :64 word) :int128))
      (word_pmul
        (word_subword (aes_gcm_rev64_int128 q6_pre) (0,64) :64 word)
        (word_subword (q13:int128) (0,64) :64 word) :int128)):int128`;
   `q16:int128`; `rk9:int128`;
   `x19_kmc:int64`; `x20_kmc:int64`; `x21_kmc:int64`;
   `x22_kmc:int64`; `x23_kmc:int64`; `x24_kmc:int64`; `sx14:int64`;
   `x0_in:int64`; `x5_in:int64`;
   `h:int128`; `prev_tag:int128`;
   `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
              AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_SPEC_FORM_PLUS_Q567_FLAG_CORRECT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[karatsuba_components; karatsuba_mid; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128] THEN
    SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
             DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH;
             WORD_SUBWORD_TRIVIAL] THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ABBREV_TAC `c0_lo:64 word = word_subword ((word_xor prev_tag ct0):int128) (0,64)` THEN
    ABBREV_TAC `c0_hi:64 word = word_subword ((word_xor prev_tag ct0):int128) (64,64)` THEN
    ABBREV_TAC `c1_lo:64 word = word_subword (ct1:int128) (0,64)` THEN
    ABBREV_TAC `c1_hi:64 word = word_subword (ct1:int128) (64,64)` THEN
    ABBREV_TAC `c2_lo:64 word = word_subword (ct2:int128) (0,64)` THEN
    ABBREV_TAC `c2_hi:64 word = word_subword (ct2:int128) (64,64)` THEN
    ABBREV_TAC `c3_lo:64 word = word_subword (ct3:int128) (0,64)` THEN
    ABBREV_TAC `c3_hi:64 word = word_subword (ct3:int128) (64,64)` THEN
    ABBREV_TAC `H0_LO:64 word = word_subword (h_power (ghash_twist h) 0) (0,64)` THEN
    ABBREV_TAC `H0_HI:64 word = word_subword (h_power (ghash_twist h) 0) (64,64)` THEN
    ABBREV_TAC `H1_LO:64 word = word_subword (h_power (ghash_twist h) 1) (0,64)` THEN
    ABBREV_TAC `H1_HI:64 word = word_subword (h_power (ghash_twist h) 1) (64,64)` THEN
    ABBREV_TAC `H2_LO:64 word = word_subword (h_power (ghash_twist h) 2) (0,64)` THEN
    ABBREV_TAC `H2_HI:64 word = word_subword (h_power (ghash_twist h) 2) (64,64)` THEN
    ABBREV_TAC `H3_LO:64 word = word_subword (h_power (ghash_twist h) 3) (0,64)` THEN
    ABBREV_TAC `H3_HI:64 word = word_subword (h_power (ghash_twist h) 3) (64,64)` THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_join (c0_lo:64 word) (c0_hi:64 word):int128)
                              (word_zx (c0_lo:64 word):int128)) (0,64) :64 word) =
      word_xor c0_hi c0_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_xor (word_zx (c1_lo:64 word):int128)
                              (word_join (c1_lo:64 word) (c1_hi:64 word):int128))
                    (0,64) :64 word) =
      word_xor c1_hi c1_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_subword (word_xor (word_join (c3_lo:64 word) (c3_hi:64 word):int128)
                                                     (word_zx (c3_lo:64 word):int128))
                                           (0,64) :64 word):int128) (0,64) :64 word) =
      word_xor c3_hi c3_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `(word_subword (word_insert (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                 (64,64)
                                 (word_subword (word_zx (word_xor (c2_hi:64 word) (c2_lo:64 word):64 word):int128)
                                               (0,64) :64 word):int128) (64,64) :64 word) =
      word_xor c2_hi c2_lo` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(word_subword (word_zx (word_xor (H3_LO:64 word) (H3_HI:64 word):64 word)
                    :int128) (0,64) :64 word) = word_xor H3_LO H3_HI` ASSUME_TAC THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `Mp_h0:int128 = word_pmul (word_xor (c0_lo:64 word) (c0_hi:64 word))
                                         (word_xor (H3_LO:64 word) (H3_HI:64 word))` THEN
    ABBREV_TAC `Mp_h1:int128 = word_pmul (word_xor (c1_lo:64 word) (c1_hi:64 word))
                                         (word_xor (H2_LO:64 word) (H2_HI:64 word))` THEN
    ABBREV_TAC `Mp_h2:int128 = word_pmul (word_xor (c2_lo:64 word) (c2_hi:64 word))
                                         (word_xor (H1_LO:64 word) (H1_HI:64 word))` THEN
    ABBREV_TAC `Mp_h3:int128 = word_pmul (word_xor (c3_lo:64 word) (c3_hi:64 word))
                                         (word_xor (H0_LO:64 word) (H0_HI:64 word))` THEN
    SUBGOAL_THEN
     `word_xor (c0_hi:64 word) c0_lo = word_xor c0_lo c0_hi /\
      word_xor (c1_hi:64 word) c1_lo = word_xor c1_lo c1_hi /\
      word_xor (c2_hi:64 word) c2_lo = word_xor c2_lo c2_hi /\
      word_xor (c3_hi:64 word) c3_lo = word_xor c3_lo c3_hi` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC "s175" THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[]) THEN
  MAP_EVERY EXISTS_TAC
   [`q1_kmc:int128`; `q2_kmc:int128`; `q3_kmc:int128`;
    `x19_kmc:int64`; `x20_kmc:int64`; `x21_kmc:int64`;
    `x22_kmc:int64`; `x23_kmc:int64`; `x24_kmc:int64`] THEN
  ASM_REWRITE_TAC[]);;

(* Kernel cut WITHOUT aligned_bytes_loaded in post *)
let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_PLUS_Q567_FLAG_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (x0_in:int64) (x5_in:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x308) /\
              read X2 s = cptr /\
              read X0 s = x0_in /\
              read X5 s = x5_in /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read PC s = word (pc + 0x5c4) /\
              read X0 s = word_add x0_in (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_in /\
              (read NF s <=>
               ival (word_sub (word_add x0_in (word 64)) x5_in) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_in (word 64)) - ival x5_in =
                 ival (word_sub (word_add x0_in (word 64)) x5_in))) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3] /\
              (?(q1k:int128) (q2k:int128) (q3k:int128)
                (x19k:int64) (x20k:int64) (x21k:int64)
                (x22k:int64) (x23k:int64) (x24k:int64).
                 read Q5 s = (word_xor (aese q1k rk9)
                               (word_insert
                                 (word_zx x19k :int128)
                                 (64,64)
                                 (word_xor x20k sx14)) :int128) /\
                 read Q6 s = (word_xor (aese q2k rk9)
                               (word_insert
                                 (word_zx x21k :int128)
                                 (64,64)
                                 x22k) :int128) /\
                 read Q7 s = (word_xor (aese q3k rk9)
                               (word_insert
                                 (word_zx x23k :int128)
                                 (64,64)
                                 (word_xor x24k sx14)) :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`pc + 0x308:num`; `cptr:int64`; `b0:int128`; `b1:int128`;
                 `b2:int128`; `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
                 `q7_pre:int128`; `q6_pre:int128`; `q12:int128`; `q13:int128`;
                 `q14:int128`; `q15:int128`; `q16:int128`; `q17:int128`;
                 `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
                 `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
                 `rk8:int128`; `rk9:int128`;
                 `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`;
                 `x0_in:int64`; `x5_in:int64`;
                 `h:int128`; `prev_tag:int128`;
                 `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
                AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_PLUS_Q567_FLAG_CORRECT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
    REWRITE_TAC[fst AES_GCM_MAIN_LOOP_BODY_SLICE_EXEC;
                fst AES_GCM_ENC_KERNEL_EXEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[fst AES_GCM_ENC_KERNEL_EXEC;
                                NONOVERLAPPING_CLAUSES]) THEN
    NONOVERLAPPING_TAC;
    REWRITE_TAC[ARITH_RULE `(pc + 0x308) + 0x2bc = pc + 0x5c4`] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    GEN_TAC THEN STRIP_TAC THEN
    POP_ASSUM(STRIP_ASSUME_TAC o BETA_RULE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SLICE_TO_KERNEL_BODY_LOAD]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 (s049) — generic helper for adding `aligned_bytes_loaded ... mc`  *)
(* to the postcondition of an `ensures arm` cut, given:                      *)
(*   (a) the frame preserves `read (memory :> bytelist(word pc, LENGTH mc))` *)
(*       (provable via COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV +           *)
(*        nonoverlapping reasoning on the bytes(cptr, n) write);             *)
(*   (b) the precondition implies `aligned_bytes_loaded s (word pc) mc`.     *)
(*                                                                           *)
(* Used in the Phase 8 main-loop wrapper to weave aligned_bytes_loaded       *)
(* through the body subgoal (the kernel cut FLAG variant lacks aligned in    *)
(* its post; this lifts it inline without a separate cut artifact).          *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ADD_ALIGNED_TO_POST = prove
 (`!pc (mc:byte list) step (P:armstate->bool) Q R.
    (!s s2. R s s2 ==> read (memory :> bytelist(word pc:int64, LENGTH mc)) s2 =
                       read (memory :> bytelist(word pc, LENGTH mc)) s) /\
    (!s. P s ==> aligned_bytes_loaded s (word pc) mc) /\
    ensures step P Q R
    ==> ensures step P (\s. aligned_bytes_loaded s (word pc) mc /\ Q s) R`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN STRIP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  GEN_TAC THEN REWRITE_TAC[aligned_bytes_loaded; bytes_loaded] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[aligned_bytes_loaded; bytes_loaded]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 (s051) — generic FACT lifter, generalisation of                   *)
(* ENSURES_ADD_ALIGNED_TO_POST: lift any preserved-by-frame fact             *)
(* `read c s = v` (with v fixed by P) into the post.                         *)
(*                                                                           *)
(* Used by the FULL kernel cut to thread Q12..Q17 (H-power table),          *)
(* Q18..Q26+Q31 (round keys), and X9/X10/X13/X14 (preserved scalars) from   *)
(* the cut's pre into its post — these registers are outside the cut's     *)
(* MAYCHANGE frame so they ARE preserved, but the FLAG_LOADED cut's post   *)
(* doesn't assert that.  Iterating this helper over each preserved          *)
(* component enriches the post enough that ENSURES_PREPOSTCONDITION_THM     *)
(* matches the wrapper's loop invariant directly.                           *)
(*                                                                           *)
(* Antecedent (a) `R s s2 ==> read c s2 = read c s` is the standard         *)
(* preservation predicate; for MAYCHANGE frames not mentioning c it         *)
(* discharges via READ_OVER_WRITE_ORTHOGONAL_TAC.  Antecedent (b)            *)
(* `P s ==> read c s = v` is trivial when P directly asserts                 *)
(* `read c s = v` (SIMP_TAC[]).                                              *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ADD_FACT_TO_POST = prove
 (`!(c:(armstate,A)component) v step (P:armstate->bool) Q R.
    (!s s2. R s s2 ==> read c s2 = read c s) /\
    (!s. P s ==> read c s = v) /\
    ensures step P Q R
    ==> ensures step P (\s. read c s = v /\ Q s) R`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN STRIP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 (s049) — kernel-level body cut (LOADED variant): same as the      *)
(* FLAG cut but with `aligned_bytes_loaded ... aes_gcm_enc_kernel_mc` in     *)
(* both pre AND post.  Lifted from the FLAG cut via                          *)
(* ENSURES_ADD_ALIGNED_TO_POST helper; the frame's only memory MAYCHANGE     *)
(* component is `bytes(cptr, 64)` which is nonoverlapping with the kernel    *)
(* code memory by precondition, so READ_OVER_WRITE_ORTHOGONAL_TAC discharges *)
(* the bytelist preservation cleanly.                                        *)
(*                                                                           *)
(* This cut is the natural input to the wrapper's body subgoal               *)
(* (ENSURES_PREPOSTCONDITION_THM bridge from PUP's program_decodes).         *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_PLUS_Q567_FLAG_LOADED_CORRECT
    = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (x0_in:int64) (x5_in:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x308) /\
              read X2 s = cptr /\
              read X0 s = x0_in /\
              read X5 s = x5_in /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x5c4) /\
              read X0 s = word_add x0_in (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_in /\
              (read NF s <=>
               ival (word_sub (word_add x0_in (word 64)) x5_in) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_in (word 64)) - ival x5_in =
                 ival (word_sub (word_add x0_in (word 64)) x5_in))) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3] /\
              (?(q1k:int128) (q2k:int128) (q3k:int128)
                (x19k:int64) (x20k:int64) (x21k:int64)
                (x22k:int64) (x23k:int64) (x24k:int64).
                 read Q5 s = (word_xor (aese q1k rk9)
                               (word_insert
                                 (word_zx x19k :int128)
                                 (64,64)
                                 (word_xor x20k sx14)) :int128) /\
                 read Q6 s = (word_xor (aese q2k rk9)
                               (word_insert
                                 (word_zx x21k :int128)
                                 (64,64)
                                 x22k) :int128) /\
                 read Q7 s = (word_xor (aese q3k rk9)
                               (word_insert
                                 (word_zx x23k :int128)
                                 (64,64)
                                 (word_xor x24k sx14)) :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_ADD_ALIGNED_TO_POST THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    READ_OVER_WRITE_ORTHOGONAL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC (SPECL [`pc:num`; `cptr:int64`; `b0:int128`; `b1:int128`;
                 `b2:int128`; `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
                 `q7_pre:int128`; `q6_pre:int128`; `q12:int128`; `q13:int128`;
                 `q14:int128`; `q15:int128`; `q16:int128`; `q17:int128`;
                 `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
                 `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
                 `rk8:int128`; `rk9:int128`;
                 `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`;
                 `x0_in:int64`; `x5_in:int64`;
                 `h:int128`; `prev_tag:int128`;
                 `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
                AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_PLUS_Q567_FLAG_CORRECT) THEN
  ASM_REWRITE_TAC[SOME_FLAGS]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 (s052) — FULL_LOADED kernel cut: lifts the FLAG_LOADED cut's      *)
(* post with 19 preserved-component facts (Q12..Q17 = 6, Q18..Q26 = 9,       *)
(* Q31 = 1, X10/X13/X14 = 3 — total 19), via 19 applications of the s051    *)
(* helper ENSURES_ADD_FACT_TO_POST.                                          *)
(*                                                                           *)
(* X9 was originally in s051's plan but X9 IS in the cut's MAYCHANGE frame   *)
(* (the kernel writes X9 as the CTR-block scratch register; see lines 79..92 *)
(* and 212..236 of aes_gcm_enc_kernel_aes128.S).  Therefore the helper's     *)
(* preservation antecedent does not hold for X9 — it is NOT lifted.  The     *)
(* wrapper using this cut must GHOST_INTRO_TAC X9 or treat its exit value    *)
(* as unconstrained.                                                          *)
(*                                                                           *)
(* This is the strongest body-cut variant in the chain; it is the natural    *)
(* input to a spec-level wrapper's body subgoal.                              *)
(* ------------------------------------------------------------------------- *)

let LIFT_FACT_TAC =
  MATCH_MP_TAC ENSURES_ADD_FACT_TO_POST THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    READ_OVER_WRITE_ORTHOGONAL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC];;

let AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_FULL_LOADED_CORRECT = prove
 (`!pc (cptr:int64) (b0:int128) (b1:int128) (b2:int128)
        (q4_pre:int128) (q11_pre:int128) (q5_pre:int128) (q7_pre:int128)
        (q6_pre:int128)
        (q12:int128) (q13:int128) (q14:int128) (q15:int128) (q16:int128)
        (q17:int128)
        (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
        (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
        (sx9:int64) (sx10:int64) (sx13:int64) (sx14:int64)
        (x0_in:int64) (x5_in:int64)
        (h:int128) (prev_tag:int128) (ct0:int128) (ct1:int128) (ct2:int128)
        (ct3:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64) /\
    word_xor (aes_gcm_rev64_int128 q4_pre) (byteswap128 q11_pre) =
      byteswap128 (word_xor prev_tag ct0) /\
    aes_gcm_rev64_int128 q5_pre = byteswap128 ct1 /\
    aes_gcm_rev64_int128 q6_pre = byteswap128 ct2 /\
    aes_gcm_rev64_int128 q7_pre = byteswap128 ct3 /\
    q15 = byteswap128 (h_power (ghash_twist h) 3) /\
    q14 = byteswap128 (h_power (ghash_twist h) 2) /\
    q13 = byteswap128 (h_power (ghash_twist h) 1) /\
    q12 = byteswap128 (h_power (ghash_twist h) 0) /\
    q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
           :int128) /\
    q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                     (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
           :int128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x308) /\
              read X2 s = cptr /\
              read X0 s = x0_in /\
              read X5 s = x5_in /\
              read Q0 s = b0 /\
              read Q1 s = b1 /\
              read Q2 s = b2 /\
              read Q4 s = q4_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              read Q11 s = q11_pre /\
              read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14)
         (\s. read Q12 s = q12 /\
              read Q13 s = q13 /\
              read Q14 s = q14 /\
              read Q15 s = q15 /\
              read Q16 s = q16 /\
              read Q17 s = q17 /\
              read Q18 s = rk0 /\
              read Q19 s = rk1 /\
              read Q20 s = rk2 /\
              read Q21 s = rk3 /\
              read Q22 s = rk4 /\
              read Q23 s = rk5 /\
              read Q24 s = rk6 /\
              read Q25 s = rk7 /\
              read Q26 s = rk8 /\
              read Q31 s = rk9 /\
              read X10 s = sx10 /\
              read X13 s = sx13 /\
              read X14 s = sx14 /\
              aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
              read PC s = word (pc + 0x5c4) /\
              read X0 s = word_add x0_in (word 64) /\
              read X2 s = word_add cptr (word 64) /\
              read X5 s = x5_in /\
              (read NF s <=>
               ival (word_sub (word_add x0_in (word 64)) x5_in) < &0) /\
              (read VF s <=>
               ~(ival (word_add x0_in (word 64)) - ival x5_in =
                 ival (word_sub (word_add x0_in (word 64)) x5_in))) /\
              read Q11 s = nist_ghash h prev_tag [ct0; ct1; ct2; ct3] /\
              (?(q1k:int128) (q2k:int128) (q3k:int128)
                (x19k:int64) (x20k:int64) (x21k:int64)
                (x22k:int64) (x23k:int64) (x24k:int64).
                 read Q5 s = (word_xor (aese q1k rk9)
                               (word_insert
                                 (word_zx x19k :int128)
                                 (64,64)
                                 (word_xor x20k sx14)) :int128) /\
                 read Q6 s = (word_xor (aese q2k rk9)
                               (word_insert
                                 (word_zx x21k :int128)
                                 (64,64)
                                 x22k) :int128) /\
                 read Q7 s = (word_xor (aese q3k rk9)
                               (word_insert
                                 (word_zx x23k :int128)
                                 (64,64)
                                 (word_xor x24k sx14)) :int128)))
         (MAYCHANGE [PC] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
          MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(cptr, 64)] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  REPLICATE_TAC 19 LIFT_FACT_TAC THEN
  MP_TAC (SPECL [`pc:num`; `cptr:int64`; `b0:int128`; `b1:int128`;
                 `b2:int128`; `q4_pre:int128`; `q11_pre:int128`; `q5_pre:int128`;
                 `q7_pre:int128`; `q6_pre:int128`; `q12:int128`; `q13:int128`;
                 `q14:int128`; `q15:int128`; `q16:int128`; `q17:int128`;
                 `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
                 `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
                 `rk8:int128`; `rk9:int128`;
                 `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`;
                 `x0_in:int64`; `x5_in:int64`;
                 `h:int128`; `prev_tag:int128`;
                 `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
                AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_PLUS_Q567_FLAG_LOADED_CORRECT) THEN
  ASM_REWRITE_TAC[SOME_FLAGS]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 (s054) — generic existential-precondition lifter for ensures.     *)
(*                                                                           *)
(* If for every value of `a` the cut works under pre `P s a`, then it works *)
(* under the existentially-quantified pre `\s. ?a. P s a`.  Used by the      *)
(* main-loop wrapper's body subgoal to peel the per-iteration emit-form     *)
(* witnesses and the partial-ciphertext list `cts` from the loop invariant *)
(* before applying the FULL_LOADED kernel body cut.                         *)
(* ------------------------------------------------------------------------- *)

let ENSURES_EXIST_PRECONDITION = prove
 (`!step (P:armstate->A->bool) Q C.
     (!a. ensures step (\s. P s a) Q C)
     ==> ensures step (\s. ?a. P s a) Q C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
  STRIP_TAC THEN GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 (s055) — Full spec-level main-loop wrapper.                       *)
(*                                                                           *)
(* Lifts AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_FULL_LOADED_CORRECT   *)
(* into a multi-iteration `ensures arm` over the entire main-loop range      *)
(* `pc + 0x308 .. pc + 0x5c8` via ENSURES_WHILE_PUP_TAC.                     *)
(*                                                                           *)
(* Loop invariant (existentially quantified over partial ciphertext list    *)
(* `cts` and per-iteration emit-form witnesses `q4..q7, b0..b2, ct0..ct3`):  *)
(*                                                                           *)
(*   X0 = word_add x0_init (word(64*i))                                      *)
(*   X2 = word_add cptr (word(64*i))                                         *)
(*   X5 = x5_init                                                            *)
(*   Q12..Q15 = byteswap128(h_power(ghash_twist h, 0..3))                   *)
(*   Q16/Q17 = h-power karatsuba_mid pairs                                   *)
(*   Q18..Q26+Q31 = round keys rk0..rk9                                      *)
(*   X10/X13/X14 = sx10/sx13/sx14 (preserved scalars)                        *)
(*   ?cts q4..ct3.                                                           *)
(*     LENGTH cts = 4 * i                                                    *)
(*     Q11 = nist_ghash h initial_tag cts                                    *)
(*     Q0..Q2 = b0..b2 ; Q4..Q7 = q4..q7                                     *)
(*     <byteswap-id constraints linking rev64 q4..q7 to ct0..ct3>            *)
(*                                                                           *)
(* Postcondition projects to a simpler `?cts. LENGTH cts = 4 * N /\ Q11 =    *)
(* nist_ghash h initial_tag cts` — leaving Q0..Q7 unconstrained, since      *)
(* their final values are implementation-detail and Phase 9 (prelude/tail)  *)
(* will discharge them.                                                      *)
(*                                                                           *)
(* The body subgoal applies the FULL_LOADED kernel cut after peeling the    *)
(* 12 existentials via ENSURES_EXIST_PRECONDITION.  The byteswap-id         *)
(* constraints at iter (i+1) are existential, witnessed by                  *)
(*   ct0' := nist_ghash ⊕ byteswap128 (rev64 q4 ⊕ byteswap128 nist_ghash)  *)
(*   ct1' := byteswap128 (rev64 q5)                                          *)
(*   ct2' := byteswap128 (rev64 q6)                                          *)
(*   ct3' := byteswap128 (rev64 q7)                                          *)
(* using the byteswap128 involution + XOR self-cancellation.                *)
(*                                                                           *)
(* Q11 advance via NIST_GHASH_APPEND, identifying                            *)
(*   nist_ghash h initial_tag (APPEND cts [ct0;ct1;ct2;ct3])                *)
(*   = nist_ghash h (nist_ghash h initial_tag cts) [ct0;ct1;ct2;ct3]        *)
(* which the cut produces directly.                                          *)
(*                                                                           *)
(* Flag advance (Condition_LT <=> i+1 < N) via IVAL_WORD_SUB_NFVF_TO_LT +   *)
(* IVAL_WORD_ADD_BOUND, mirroring the SKELETON wrapper's pattern.            *)
(*                                                                           *)
(* This wrapper is the spec-level analogue of                                *)
(* AES_GCM_MAIN_LOOP_WRAPPER_SKELETON_CORRECT (s047), but carries the       *)
(* full Q-state and Q11=spec-form invariant.  It is the input to Phase 9    *)
(* (prelude + tail wrapping) and Phase 11 (public byte-level theorem).       *)
(* ------------------------------------------------------------------------- *)

let BYTESWAP128_INVOLUTION_LOCAL = prove
 (`!x:int128. byteswap128 (byteswap128 x) = x`,
  REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

let AES_GCM_MAIN_LOOP_WRAPPER_FULL_CORRECT = prove
 (`!pc (cptr:int64) (x0_init:int64) (x5_init:int64) (N:num)
       (h:int128) (initial_tag:int128)
       (q12:int128) (q13:int128) (q14:int128) (q15:int128)
       (q16:int128) (q17:int128)
       (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128) (rk4:int128)
       (rk5:int128) (rk6:int128) (rk7:int128) (rk8:int128) (rk9:int128)
       (sx10:int64) (sx13:int64) (sx14:int64).
   ~(N = 0) /\
   nonoverlapping (word pc, LENGTH aes_gcm_enc_kernel_mc) (cptr, 64*N) /\
   word_add x0_init (word(64*N)) = x5_init /\
   val x0_init + 64 * N < 2 EXP 63 /\
   q15 = byteswap128 (h_power (ghash_twist h) 3) /\
   q14 = byteswap128 (h_power (ghash_twist h) 2) /\
   q13 = byteswap128 (h_power (ghash_twist h) 1) /\
   q12 = byteswap128 (h_power (ghash_twist h) 0) /\
   q17 = (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                    (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
          :int128) /\
   q16 = (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                    (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
          :int128)
   ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
             read PC s = word (pc + 0x308) /\
             read X0 s = x0_init /\
             read X2 s = cptr /\
             read X5 s = x5_init /\
             read Q12 s = q12 /\
             read Q13 s = q13 /\
             read Q14 s = q14 /\
             read Q15 s = q15 /\
             read Q16 s = q16 /\
             read Q17 s = q17 /\
             read Q18 s = rk0 /\
             read Q19 s = rk1 /\
             read Q20 s = rk2 /\
             read Q21 s = rk3 /\
             read Q22 s = rk4 /\
             read Q23 s = rk5 /\
             read Q24 s = rk6 /\
             read Q25 s = rk7 /\
             read Q26 s = rk8 /\
             read Q31 s = rk9 /\
             read X10 s = sx10 /\
             read X13 s = sx13 /\
             read X14 s = sx14 /\
             (?(q4:int128) (q5:int128) (q6:int128) (q7:int128)
               (b0:int128) (b1:int128) (b2:int128)
               (ct0:int128) (ct1:int128) (ct2:int128) (ct3:int128).
                read Q11 s = initial_tag /\
                read Q0 s = b0 /\ read Q1 s = b1 /\ read Q2 s = b2 /\
                read Q4 s = q4 /\ read Q5 s = q5 /\
                read Q6 s = q6 /\ read Q7 s = q7 /\
                word_xor (aes_gcm_rev64_int128 q4) (byteswap128 initial_tag) =
                byteswap128 (word_xor initial_tag ct0) /\
                aes_gcm_rev64_int128 q5 = byteswap128 ct1 /\
                aes_gcm_rev64_int128 q6 = byteswap128 ct2 /\
                aes_gcm_rev64_int128 q7 = byteswap128 ct3))
        (\s. read PC s = word (pc + 0x5c8) /\
             read X0 s = x5_init /\
             read X2 s = word_add cptr (word(64*N)) /\
             read X5 s = x5_init /\
             read Q12 s = q12 /\
             read Q13 s = q13 /\
             read Q14 s = q14 /\
             read Q15 s = q15 /\
             read Q16 s = q16 /\
             read Q17 s = q17 /\
             read Q18 s = rk0 /\
             read Q19 s = rk1 /\
             read Q20 s = rk2 /\
             read Q21 s = rk3 /\
             read Q22 s = rk4 /\
             read Q23 s = rk5 /\
             read Q24 s = rk6 /\
             read Q25 s = rk7 /\
             read Q26 s = rk8 /\
             read Q31 s = rk9 /\
             read X10 s = sx10 /\
             read X13 s = sx13 /\
             read X14 s = sx14 /\
             (?cts. LENGTH cts = 4 * N /\
                    read Q11 s = nist_ghash h initial_tag cts))
        (MAYCHANGE [PC] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
         MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
         MAYCHANGE SOME_FLAGS ,,
         MAYCHANGE [memory :> bytes(cptr, 64*N)] ,,
         MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `N:num` `pc + 0x308` `pc + 0x5c4`
    `\i s.
        (read X0 s = word_add x0_init (word(64*i)) /\
         read X2 s = word_add cptr (word(64*i)) /\
         read X5 s = (x5_init:int64) /\
         read Q12 s = (q12:int128) /\
         read Q13 s = (q13:int128) /\
         read Q14 s = (q14:int128) /\
         read Q15 s = (q15:int128) /\
         read Q16 s = (q16:int128) /\
         read Q17 s = (q17:int128) /\
         read Q18 s = (rk0:int128) /\
         read Q19 s = (rk1:int128) /\
         read Q20 s = (rk2:int128) /\
         read Q21 s = (rk3:int128) /\
         read Q22 s = (rk4:int128) /\
         read Q23 s = (rk5:int128) /\
         read Q24 s = (rk6:int128) /\
         read Q25 s = (rk7:int128) /\
         read Q26 s = (rk8:int128) /\
         read Q31 s = (rk9:int128) /\
         read X10 s = (sx10:int64) /\
         read X13 s = (sx13:int64) /\
         read X14 s = (sx14:int64) /\
         (?(cts:int128 list)
           (q4:int128) (q5:int128) (q6:int128) (q7:int128)
           (b0:int128) (b1:int128) (b2:int128)
           (ct0:int128) (ct1:int128) (ct2:int128) (ct3:int128).
              LENGTH cts = 4 * i /\
              read Q11 s = nist_ghash (h:int128) initial_tag cts /\
              read Q0 s = b0 /\ read Q1 s = b1 /\ read Q2 s = b2 /\
              read Q4 s = q4 /\ read Q5 s = q5 /\
              read Q6 s = q6 /\ read Q7 s = q7 /\
              word_xor (aes_gcm_rev64_int128 q4)
                       (byteswap128 (nist_ghash h initial_tag cts)) =
              byteswap128 (word_xor (nist_ghash h initial_tag cts) ct0) /\
              aes_gcm_rev64_int128 q5 = byteswap128 ct1 /\
              aes_gcm_rev64_int128 q6 = byteswap128 ct2 /\
              aes_gcm_rev64_int128 q7 = byteswap128 ct3)) /\
        (condition_semantics Condition_LT s <=> i < N)` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [(* Init subgoal — 0-step transition; existential at i=0 with cts := [] *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; WORD_VAL] THEN
    POP_ASSUM(K ALL_TAC) THEN
    POP_ASSUM(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `[]:int128 list` THEN
    MAP_EVERY EXISTS_TAC
      [`q4:int128`; `q5:int128`; `q6:int128`; `q7:int128`;
       `b0:int128`; `b1:int128`; `b2:int128`;
       `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`] THEN
    ASM_REWRITE_TAC[LENGTH; nist_ghash; MULT_CLAUSES];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* Body subgoal — peel 12 existentials, apply FULL_LOADED cut *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPLICATE_TAC 12
      (MATCH_MP_TAC ENSURES_EXIST_PRECONDITION THEN GEN_TAC) THEN
    GHOST_INTRO_TAC `sx9:int64` `read X9` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    MP_TAC (SPECL
     [`pc:num`; `word_add (cptr:int64) (word(64*i)):int64`;
      `b0:int128`; `b1:int128`; `b2:int128`;
      `q4:int128`; `nist_ghash (h:int128) initial_tag cts`;
      `q5:int128`; `q7:int128`; `q6:int128`;
      `byteswap128 (h_power (ghash_twist (h:int128)) 0)`;
      `byteswap128 (h_power (ghash_twist (h:int128)) 1)`;
      `byteswap128 (h_power (ghash_twist (h:int128)) 2)`;
      `byteswap128 (h_power (ghash_twist (h:int128)) 3)`;
      `(word_join (karatsuba_mid (h_power (ghash_twist (h:int128)) 1) :64 word)
                  (karatsuba_mid (h_power (ghash_twist (h:int128)) 0) :64 word)
        :int128)`;
      `(word_join (karatsuba_mid (h_power (ghash_twist (h:int128)) 3) :64 word)
                  (karatsuba_mid (h_power (ghash_twist (h:int128)) 2) :64 word)
        :int128)`;
      `rk0:int128`; `rk1:int128`; `rk2:int128`; `rk3:int128`;
      `rk4:int128`; `rk5:int128`; `rk6:int128`; `rk7:int128`;
      `rk8:int128`; `rk9:int128`;
      `sx9:int64`; `sx10:int64`; `sx13:int64`; `sx14:int64`;
      `word_add (x0_init:int64) (word(64*i)):int64`;
      `x5_init:int64`;
      `h:int128`; `nist_ghash (h:int128) initial_tag cts`;
      `ct0:int128`; `ct1:int128`; `ct2:int128`; `ct3:int128`]
     AES_GCM_MAIN_LOOP_BODY_GHASH_NIST_FULL_KERNEL_FULL_LOADED_CORRECT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst AES_GCM_ENC_KERNEL_EXEC] THEN
      CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                                    fst AES_GCM_ENC_KERNEL_EXEC]) THEN
        NONOVERLAPPING_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SOME_FLAGS] THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11] ,,
      MAYCHANGE [X0; X2; X6; X7; X9; X12; X19; X20; X21; X22; X23; X24] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,,
      MAYCHANGE [memory :> bytes(word_add (cptr:int64) (word(64*i)), 64)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                                  fst AES_GCM_ENC_KERNEL_EXEC]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    EXISTS_TAC
     `\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
          read PC s = word (pc + 776) /\
          read X2 s = word_add (cptr:int64) (word (64 * i)) /\
          read X0 s = word_add (x0_init:int64) (word (64 * i)) /\
          read X5 s = (x5_init:int64) /\
          read Q0 s = (b0:int128) /\
          read Q1 s = (b1:int128) /\
          read Q2 s = (b2:int128) /\
          read Q4 s = (q4:int128) /\
          read Q5 s = (q5:int128) /\
          read Q6 s = (q6:int128) /\
          read Q7 s = (q7:int128) /\
          read Q11 s = nist_ghash (h:int128) initial_tag cts /\
          read Q12 s = byteswap128 (h_power (ghash_twist h) 0) /\
          read Q13 s = byteswap128 (h_power (ghash_twist h) 1) /\
          read Q14 s = byteswap128 (h_power (ghash_twist h) 2) /\
          read Q15 s = byteswap128 (h_power (ghash_twist h) 3) /\
          read Q16 s =
            (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
             :int128) /\
          read Q17 s =
            (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
             :int128) /\
          read Q18 s = (rk0:int128) /\
          read Q19 s = (rk1:int128) /\
          read Q20 s = (rk2:int128) /\
          read Q21 s = (rk3:int128) /\
          read Q22 s = (rk4:int128) /\
          read Q23 s = (rk5:int128) /\
          read Q24 s = (rk6:int128) /\
          read Q25 s = (rk7:int128) /\
          read Q26 s = (rk8:int128) /\
          read Q31 s = (rk9:int128) /\
          read X9 s = (sx9:int64) /\
          read X10 s = (sx10:int64) /\
          read X13 s = (sx13:int64) /\
          read X14 s = (sx14:int64)` THEN
    EXISTS_TAC
     `\s. read Q12 s = byteswap128 (h_power (ghash_twist (h:int128)) 0) /\
          read Q13 s = byteswap128 (h_power (ghash_twist h) 1) /\
          read Q14 s = byteswap128 (h_power (ghash_twist h) 2) /\
          read Q15 s = byteswap128 (h_power (ghash_twist h) 3) /\
          read Q16 s =
            (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
             :int128) /\
          read Q17 s =
            (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
             :int128) /\
          read Q18 s = (rk0:int128) /\
          read Q19 s = (rk1:int128) /\
          read Q20 s = (rk2:int128) /\
          read Q21 s = (rk3:int128) /\
          read Q22 s = (rk4:int128) /\
          read Q23 s = (rk5:int128) /\
          read Q24 s = (rk6:int128) /\
          read Q25 s = (rk7:int128) /\
          read Q26 s = (rk8:int128) /\
          read Q31 s = (rk9:int128) /\
          read X10 s = (sx10:int64) /\
          read X13 s = (sx13:int64) /\
          read X14 s = (sx14:int64) /\
          aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
          read PC s = word (pc + 1476) /\
          read X0 s = word_add (word_add (x0_init:int64) (word (64 * i))) (word 64) /\
          read X2 s = word_add (word_add (cptr:int64) (word (64 * i))) (word 64) /\
          read X5 s = (x5_init:int64) /\
          (read NF s <=>
           ival (word_sub (word_add (word_add x0_init (word (64 * i))) (word 64))
                          x5_init) < &0) /\
          (read VF s <=>
           ~(ival (word_add (word_add x0_init (word (64 * i))) (word 64)) -
             ival x5_init =
             ival (word_sub (word_add (word_add x0_init (word (64 * i))) (word 64))
                            x5_init))) /\
          read Q11 s = nist_ghash h (nist_ghash h initial_tag cts) [ct0; ct1; ct2; ct3] /\
          (?(q1k:int128) (q2k:int128) (q3k:int128)
            (x19k:int64) (x20k:int64) (x21k:int64)
            (x22k:int64) (x23k:int64) (x24k:int64).
               read Q5 s = (word_xor (aese q1k rk9)
                             (word_insert
                               (word_zx x19k :int128)
                               (64,64)
                               (word_xor x20k sx14)) :int128) /\
               read Q6 s = (word_xor (aese q2k rk9)
                             (word_insert
                               (word_zx x21k :int128)
                               (64,64)
                               x22k) :int128) /\
               read Q7 s = (word_xor (aese q3k rk9)
                             (word_insert
                               (word_zx x23k :int128)
                               (64,64)
                               (word_xor x24k sx14)) :int128))` THEN
    REPEAT CONJ_TAC THEN BETA_TAC THENL
     [(* Pre' ==> cut.Pre *)
      MESON_TAC[];
      (* cut.Post ==> Post' *)
      X_GEN_TAC `s2:armstate` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `APPEND (cts:int128 list) [ct0; ct1; ct2; ct3]` THEN
        EXISTS_TAC `read Q4 (s2:armstate)` THEN
        EXISTS_TAC `word_xor (aese (q1k:int128) (rk9:int128))
                      (word_insert (word_zx (x19k:int64) :int128)
                                   (64,64)
                                   (word_xor (x20k:int64) (sx14:int64)))` THEN
        EXISTS_TAC `word_xor (aese (q2k:int128) (rk9:int128))
                      (word_insert (word_zx (x21k:int64) :int128)
                                   (64,64)
                                   (x22k:int64))` THEN
        EXISTS_TAC `word_xor (aese (q3k:int128) (rk9:int128))
                      (word_insert (word_zx (x23k:int64) :int128)
                                   (64,64)
                                   (word_xor (x24k:int64) (sx14:int64)))` THEN
        EXISTS_TAC `read Q0 (s2:armstate)` THEN
        EXISTS_TAC `read Q1 (s2:armstate)` THEN
        EXISTS_TAC `read Q2 (s2:armstate)` THEN
        EXISTS_TAC `word_xor (nist_ghash (h:int128) initial_tag
                                (APPEND cts [ct0; ct1; ct2; ct3]))
                      (byteswap128
                        (word_xor (aes_gcm_rev64_int128 (read Q4 (s2:armstate)))
                                  (byteswap128 (nist_ghash h initial_tag
                                                  (APPEND cts [ct0; ct1; ct2; ct3])))))` THEN
        EXISTS_TAC `byteswap128
                      (aes_gcm_rev64_int128
                        (word_xor (aese (q1k:int128) (rk9:int128))
                           (word_insert (word_zx (x19k:int64) :int128)
                                        (64,64)
                                        (word_xor (x20k:int64) (sx14:int64)))))` THEN
        EXISTS_TAC `byteswap128
                      (aes_gcm_rev64_int128
                        (word_xor (aese (q2k:int128) (rk9:int128))
                           (word_insert (word_zx (x21k:int64) :int128)
                                        (64,64)
                                        (x22k:int64))))` THEN
        EXISTS_TAC `byteswap128
                      (aes_gcm_rev64_int128
                        (word_xor (aese (q3k:int128) (rk9:int128))
                           (word_insert (word_zx (x23k:int64) :int128)
                                        (64,64)
                                        (word_xor (x24k:int64) (sx14:int64)))))` THEN
        ASM_REWRITE_TAC[GSYM NIST_GHASH_APPEND; LENGTH_APPEND; LENGTH;
                        ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                        ARITH_RULE `4 + a = a + 4`] THEN
        REPEAT CONJ_TAC THENL
         [CONV_TAC WORD_RULE;
          CONV_TAC WORD_RULE;
          ARITH_TAC;
          ONCE_REWRITE_TAC[WORD_RULE `word_xor a (word_xor a b) = b`] THEN
          ONCE_REWRITE_TAC[BYTESWAP128_INVOLUTION_LOCAL] THEN REFL_TAC;
          ONCE_REWRITE_TAC[BYTESWAP128_INVOLUTION_LOCAL] THEN REFL_TAC;
          ONCE_REWRITE_TAC[BYTESWAP128_INVOLUTION_LOCAL] THEN REFL_TAC;
          ONCE_REWRITE_TAC[BYTESWAP128_INVOLUTION_LOCAL] THEN REFL_TAC];
        REWRITE_TAC[condition_semantics] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IVAL_WORD_SUB_NFVF_TO_LT] THEN
        SUBGOAL_THEN
         `word_add (word_add (x0_init:int64) (word (64 * i))) (word 64) =
          word_add x0_init (word(64 * (i+1)):int64)` SUBST1_TAC THENL
         [CONV_TAC WORD_RULE; ALL_TAC] THEN
        MP_TAC (SPECL [`x0_init:int64`; `x5_init:int64`; `i:num`; `N:num`]
                IVAL_WORD_ADD_BOUND) THEN
        ASM_REWRITE_TAC[]];
      (* The cut ensures *)
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* Backedge subgoal *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                                fst AES_GCM_ENC_KERNEL_EXEC]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[condition_semantics]) THEN
    ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Exit subgoal *)
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_ENC_KERNEL_EXEC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[condition_semantics; LT_REFL]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_KERNEL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
  STRIP_TAC THEN
  EXISTS_TAC `cts:int128 list` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s056) — prelude slice + design plan.                             *)
(*                                                                           *)
(* The prelude covers kernel byte offsets 0..0x308 (194 instructions),       *)
(* spanning from function entry through the main-loop top label              *)
(* `.Lenc_main_loop` at offset 0x308.  Internally the prelude:               *)
(*   1.  Saves callee-saved registers (X19..X24 + D8..D15) and the           *)
(*       frame pointer (X29/X30) on the stack — these belong to the          *)
(*       Phase 10 SUBROUTINE wrapper (`ARM_ADD_RETURN_STACK_TAC`).           *)
(*   2.  Sets up scalar pointers and counter scratch:                        *)
(*         mov x16, x4   ; ivec_ptr                                          *)
(*         mov x8, x5    ; key_ptr                                           *)
(*         ldr w17, [x8, #240]  ; nr (always 10 for AES-128)                 *)
(*         add x4, x0, x1, lsr #3 ; end_input_ptr                            *)
(*         lsr x5, x1, #3        ; byte_len                                  *)
(*         and x5, x5, #~0x3f    ; byte_len rounded down to 64                *)
(*         add x5, x5, x0        ; end-of-main-loop pointer                  *)
(*       Loads the initial counter as Q0 from [x16] and replicates as Q1/Q2/ *)
(*       Q3 (with the low-32-bit big-endian counter incremented by 1/2/3).   *)
(*   3.  Loads round keys rk0..rk7 + rk9 + rk_N-1 (Q31) into Q18..Q25/Q31    *)
(*       from [x8, #0..#112].  rk8 (Q26), rk10 (Q28), rk11 (Q29), rk12 (Q30) *)
(*       loaded later for AES-128 only Q26+Q31 are used (rk8 and rk9).       *)
(*   4.  Loads the H-power table (htable_mem):                                *)
(*         ldr q12, [x6]      ; h1                                           *)
(*         ldr q13, [x6, #32] ; h2                                           *)
(*         ldr q14, [x6, #48] ; h3                                           *)
(*         ldr q15, [x6, #80] ; h4                                           *)
(*       and computes the karatsuba_mid pairs Q16/Q17 via `trn1`/`trn2`/`eor`*)
(*       on Q12/Q13 and Q14/Q15.                                             *)
(*   5.  Loads the running GHASH tag from [x3] and reflects it (`ld1`+`ext`+ *)
(*       `rev64`) into Q11.                                                  *)
(*   6.  Runs 9 rounds of AES on Q0..Q3 (rk0..rk8) and the final round-N-1   *)
(*       (rk9 from Q31).                                                     *)
(*   7.  At offset 0x224 (`.Lenc_finish_first_blocks`):                      *)
(*         cmp x0, x5                                                        *)
(*         b.ge 0x7c8 (.Lenc_tail) — taken if ≤4 blocks; main loop skipped *)
(*       This branch falls through (NOT taken) iff the input has ≥5 blocks  *)
(*       — i.e. the wrapper's `~(N = 0)` precondition + the first-block     *)
(*       allocation imply we have at least one main-loop iteration.          *)
(*   8.  Loads the first 4-block plaintext via `ldp` × 4, XORs with rkN     *)
(*       (deferred via x13/x14), XORs with the AES result Q0..Q3, stores    *)
(*       the first 4 ciphertext blocks via `st1` × 4.                       *)
(*   9.  At offset 0x304:                                                    *)
(*         b.ge 0x5c8 (.Lenc_prepretail) — taken if no main-loop iters left*)
(*       Falls through to the main loop top at 0x308 iff there are ≥2 full  *)
(*       4-block iterations remaining.                                       *)
(*                                                                           *)
(* The wrapper PRE at pc+0x308 (per Phase 8 wrapper) expects:                *)
(*   - PC, X0=x0_init, X2=cptr, X5=x5_init                                   *)
(*   - Q12..Q17 = byteswap128 H-powers + karatsuba_mid pairs                 *)
(*   - Q18..Q26 + Q31 = round keys rk0..rk9                                  *)
(*   - X10, X13, X14 = sx10, sx13, sx14 (preserved scalars)                  *)
(*   - Q11 = initial_tag (the GHASH starting tag)                            *)
(*   - Q0..Q2 = b0,b1,b2 (next-iter counters; existential)                   *)
(*   - Q4..Q7 = q4,q5,q6,q7 (this iter's first 4 ciphertext blocks in        *)
(*               aes_gcm_rev64_int128 form, satisfying byteswap-id           *)
(*               constraints against ct0..ct3)                               *)
(*                                                                           *)
(* The Phase 9a wrapper must therefore:                                      *)
(*   (a) Take a function-entry precondition listing C arguments              *)
(*       (in_ptr, in_bits, out_ptr, Xi_ptr, ivec_ptr, key_ptr, htable_ptr)  *)
(*       plus the `htable_mem` and key-schedule-in-memory shapes.            *)
(*   (b) Establish the wrapper's PRE at pc+0x308 by symbolic execution      *)
(*       through 194 instructions, including the two conditional branches.  *)
(*   (c) Witness the iter-0 byteswap-id existential: ct0..ct3 are derived  *)
(*       from the first 4-block ciphertext stored at cptr-64..cptr by       *)
(*       byteswap128(rev64) of Q4..Q7.                                       *)
(*                                                                           *)
(* This is multi-session work.  This session lands the prelude slice +       *)
(* EXEC as a foundation artifact, mirroring how Phase 7 first committed      *)
(* `aes_gcm_main_loop_body_slice_mc` (s019) before attacking the body proof  *)
(* incrementally over ~30 sessions.                                          *)
(*                                                                           *)
(* The slice covers the full 0..0x308 range (including the 11-instruction    *)
(* function prologue at 0..0x2c).  Phase 10 (SUBROUTINE wrapper) will        *)
(* separately carve the prologue out via `ARM_ADD_RETURN_STACK_TAC`'s        *)
(* `pre_post_nsteps` parameter; at the kernel-level the prologue and the     *)
(* compute-prelude live in the same `aes_gcm_enc_kernel_mc` byte list.      *)
(* ------------------------------------------------------------------------- *)

let aes_gcm_main_loop_prelude_slice_mc_def,
    aes_gcm_main_loop_prelude_slice_mc,
    AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC =
  mk_sublist_of_mc "aes_gcm_main_loop_prelude_slice_mc"
    aes_gcm_enc_kernel_mc
    (`0x0`,`0x308`)
    (fst AES_GCM_ENC_KERNEL_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s056) — tail slice + design plan.                                *)
(*                                                                           *)
(* The tail covers kernel byte offsets 0x5c8..0x970 (234 instructions),      *)
(* spanning from `.Lenc_prepretail` (0x5c8) through the final `st1` of      *)
(* the Q11 GHASH tag (0x96c).  The 0x970..0x990 range is the epilogue       *)
(* (LDP × 6 + LDP X29/X30 + RET) and is handled by the Phase 10 SUBROUTINE   *)
(* wrapper via `ARM_ADD_RETURN_STACK_TAC`.                                   *)
(*                                                                           *)
(* Two distinct entry points reach the tail:                                 *)
(*   (a)  Lenc_prepretail at 0x5c8 — reached via the main-loop fall-through *)
(*        (after `b.lt 0x308` not taken) AND via the `b.ge 0x5c8` from      *)
(*        the prelude when there's exactly 1 main-loop iteration.            *)
(*   (b)  Lenc_tail at 0x7c8 — reached via the prelude's `b.ge 0x7c8` when *)
(*        the input is ≤4 blocks (no main-loop iterations at all).          *)
(*                                                                           *)
(* The tail proper consists of:                                              *)
(*   1.  0x5c8..0x7c4 (Lenc_prepretail, 127 instructions): one final         *)
(*       4-block AES + GHASH iteration, but with NO ciphertext store at the *)
(*       end — instead, a final Karatsuba MODULO reduction folds the        *)
(*       running GHASH into Q11.  This handles the case where the loop      *)
(*       wrapper already wrote the last 4 ciphertext blocks; we just need   *)
(*       to absorb them into the tag.                                       *)
(*   2.  0x7c8..0x96c (Lenc_tail / blocks_{1,2,3,4}_remaining, 105          *)
(*       instructions): the residual 1..4-block tail, structured as a      *)
(*       cascade of `b.gt` checks against `cmp x5, #0x10/0x20/0x30`.        *)
(*       Each "blocks-N-remaining" label handles N residual blocks by       *)
(*       loading, XORing with AES, storing, and absorbing into GHASH.       *)
(*       Falls through to the final tag finalization.                       *)
(*   3.  0x950..0x96c: store final counter (`str w9, [x16, #12]`), store   *)
(*       last AES result if any, fold final Q11 (ext + rev64), store final  *)
(*       tag (`st1 {v11.16b}, [x3]`).                                       *)
(*                                                                           *)
(* The Phase 9b wrapper must:                                                *)
(*   (a) Take a precondition matching the WRAPPER_FULL_CORRECT POST          *)
(*       (`?cts. LENGTH cts = 4 * N /\ Q11 = nist_ghash h initial_tag cts`) *)
(*       OR the prelude's "≤4 blocks" exit shape.                            *)
(*   (b) Symbolically execute through the prepretail, the tail-cascade      *)
(*       branches, and the final tag fold.                                  *)
(*   (c) Establish the post-condition: the spec-level final ciphertext       *)
(*       (= ctr-keystream XOR plaintext for all blocks) is at memory         *)
(*       [out_ptr..out_ptr+byte_len], and the spec-level final tag          *)
(*       `nist_ghash h initial_tag full_ciphertext` is at memory [Xi_ptr]   *)
(*       (after byteswap to NIST byte order).                                *)
(*                                                                           *)
(* This is multi-session work; the cascade logic with N=1,2,3,4 cases is    *)
(* nontrivial.  Lands the slice + EXEC here as a foundation artifact.        *)
(* ------------------------------------------------------------------------- *)

let aes_gcm_main_loop_tail_slice_mc_def,
    aes_gcm_main_loop_tail_slice_mc,
    AES_GCM_MAIN_LOOP_TAIL_SLICE_EXEC =
  mk_sublist_of_mc "aes_gcm_main_loop_tail_slice_mc"
    aes_gcm_enc_kernel_mc
    (`0x5c8`,`0x3a8`)
    (fst AES_GCM_ENC_KERNEL_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s056) — prelude-slice smoke cut.                                 *)
(*                                                                           *)
(* Tiny single-step cut over the prelude slice's `mov x16, x4` instruction  *)
(* (kernel offset 0xc, slice instruction index 4).  Validates that the      *)
(* prelude slice + EXEC tactic machinery actually works for symbolic        *)
(* execution — i.e. that `ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_     *)
(* EXEC` produces the expected register update.                             *)
(*                                                                           *)
(* This is the simplest possible non-trivial cut over the prelude slice,    *)
(* analogous to how `AES_GCM_MAIN_LOOP_BODY_R0_BLOCKS012_CORRECT` was the   *)
(* first body-slice cut (s019).  Subsequent sessions can extend it          *)
(* incrementally to the full prelude-end-to-wrapper-PRE wrapper.            *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_SMOKE_CUT_CORRECT = prove
 (`!pc (a:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
          read PC s = word (pc + 0xc) /\
          read X4 s = a)
     (\s. read PC s = word (pc + 0x10) /\
          read X4 s = a /\
          read X16 s = a)
     (MAYCHANGE [PC; X16])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC [4] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s057) — tail-slice smoke cut.                                    *)
(*                                                                           *)
(* Tiny single-step cut over the tail slice's `sub x5, x4, x0` instruction  *)
(* (kernel offset 0x7cc, slice instruction index 129).  Validates that the  *)
(* tail slice + EXEC tactic machinery actually works for symbolic execution *)
(* — i.e. that `ARM_STEPS_TAC AES_GCM_MAIN_LOOP_TAIL_SLICE_EXEC` produces  *)
(* the expected register update on a 64-bit scalar instruction.              *)
(*                                                                           *)
(* Mirrors `AES_GCM_PRELUDE_SMOKE_CUT_CORRECT` for the prelude slice; pinned *)
(* to a non-Q-named instruction per s056's note that `fmov d3, x10` (also   *)
(* in the tail) hits a Q3 typecheck issue when stated as `read Q3 s = ...`. *)
(* The `sub x5, x4, x0` lives in the post-Lenc_tail "blocks-N-remaining"    *)
(* cascade region (offset 0x7cc, after the prelude's `b.ge .Lenc_tail`     *)
(* lands at 0x7c8).                                                          *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_TAIL_SMOKE_CUT_CORRECT = prove
 (`!pc (a:int64) (b:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_tail_slice_mc /\
          read PC s = word (pc + 0x204) /\
          read X4 s = a /\
          read X0 s = b)
     (\s. read PC s = word (pc + 0x208) /\
          read X4 s = a /\
          read X0 s = b /\
          read X5 s = word_sub a b)
     (MAYCHANGE [PC; X5])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_TAIL_SLICE_EXEC [130] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s057) — post-prologue baseline cut.                              *)
(*                                                                           *)
(* The 11 prologue instructions (kernel offsets 0..0x28, slice instr indices *)
(* 1..11) save callee-saved registers and frame pointer to the stack and     *)
(* set up the basic scalar pointers `x16 = x4 = ivec_ptr` and `x8 = x5 =     *)
(* key_ptr` for use by the rest of the prelude:                              *)
(*                                                                           *)
(*   0x00  stp x29, x30, [sp, #-128]!  ; pre-decrement SP, save FP/LR       *)
(*   0x04  mov x29, sp                  ; new frame pointer                  *)
(*   0x08  stp x19, x20, [sp, #16]                                          *)
(*   0x0c  mov x16, x4                  ; ivec_ptr (X16)                     *)
(*   0x10  mov x8, x5                   ; key_ptr  (X8)                      *)
(*   0x14  stp x21, x22, [sp, #32]                                          *)
(*   0x18  stp x23, x24, [sp, #48]                                          *)
(*   0x1c  stp d8, d9,   [sp, #64]                                          *)
(*   0x20  stp d10, d11, [sp, #80]                                          *)
(*   0x24  stp d12, d13, [sp, #96]                                          *)
(*   0x28  stp d14, d15, [sp, #112]                                         *)
(*                                                                           *)
(* The cut establishes the post-prologue baseline state (PC = pc + 0x2c,    *)
(* SP = stackpointer - 128, X16 = a, X8 = b) under a stack-nonoverlapping   *)
(* precondition mirroring the SUBROUTINE wrapper shape.  The MAYCHANGE      *)
(* includes the 128-byte stack frame as `bytes(stackpointer-128, 128)` —    *)
(* the simulator emits 16 individual `bytes64` writes which                  *)
(* `ENSURES_FINAL_STATE_TAC` subsumes into the larger `bytes(...,128)` slot. *)
(*                                                                           *)
(* This is the entry point for all subsequent prelude cuts: scalar setup    *)
(* (ldr w17 / ldp x13,x14 / ldr q31 / add x4 / lsr x5 / mov x15 / and x5),  *)
(* then the H-table + key loads, then the AES rounds, then the first 4-     *)
(* block CTR/store, terminating at the wrapper-PRE shape at pc + 0x308.     *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_POST_PROLOGUE_CORRECT = prove
 (`!pc (a:int64) (b:int64) (stackpointer:int64).
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_prelude_slice_mc)
                   (word_sub stackpointer (word 128), 128)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X4 s = a /\
              read X5 s = b)
         (\s. read PC s = word (pc + 0x2c) /\
              read SP s = word_sub stackpointer (word 128) /\
              read X4 s = a /\
              read X5 s = b /\
              read X16 s = a /\
              read X8 s = b)
         (MAYCHANGE [PC; SP; X16; X8; X29] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 128), 128)] ,,
          MAYCHANGE [events])`,
  REWRITE_TAC[fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s057) — scalar setup cut.                                        *)
(*                                                                           *)
(* The 6 instructions at kernel offsets 0x2c..0x40 (slice instr indices      *)
(* 12..17) load the AES-128 key-schedule's last-round-key halves and round- *)
(* N-1 key, and compute the input-pointer arithmetic                         *)
(*                                                                           *)
(*   0x2c  ldr w17, [x8, #240]            ; nr (= 10 for AES-128)           *)
(*   0x30  add x19, x8, x17, lsl #4       ; last-key pointer = x8 + 16*nr   *)
(*   0x34  ldp x13, x14, [x19]            ; round-N key halves              *)
(*   0x38  ldur q31, [x19, #-16]          ; round-N-1 key (rk9)             *)
(*   0x3c  add x4, x0, x1, lsr #3         ; end_input_ptr                   *)
(*   0x40  lsr x5, x1, #3                 ; byte_len                        *)
(*                                                                           *)
(* The cut takes a key-schedule-in-memory precondition specifying the bytes *)
(* at offsets 240 (nr), 160/168 (rk10 halves), and 144 (rk9 q-load).        *)
(* For AES-128 the round count is hardcoded to 10, so `nr = 10` is a        *)
(* concrete value in the precondition; the cut commits to this              *)
(* specialization rather than parametrizing over an arbitrary nr (the       *)
(* AES-128 fork removes the AES-192/256 branches, so only nr=10 reaches    *)
(* this prelude — the unverified aws-lc kernel branches on nr at offset    *)
(* 0x7c / 0x84 to dispatch round counts).                                   *)
(*                                                                           *)
(* MAYCHANGE is split across [PC; X4; X5; X13; X14; X17; X19] (int64),     *)
(* [Q31] (int128), and [events] (lists of memory accesses).  Unifying      *)
(* PC/Xn with Q31 in a single [...] would force a typecheck error since    *)
(* PC and Xn are :64 word components while Q31 is :128 word.                *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_SCALAR_SETUP_CORRECT = prove
 (`!pc (x0_init:int64) (x1_init:int64) (x5_init:int64) (b:int64)
       (lk_lo:int64) (lk_hi:int64) (rk9:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
          read PC s = word (pc + 0x2c) /\
          read X0 s = x0_init /\
          read X1 s = x1_init /\
          read X8 s = b /\
          read X5 s = x5_init /\
          read (memory :> bytes32 (word_add b (word 240))) s = (word 10:32 word) /\
          read (memory :> bytes64 (word_add b (word 160))) s = lk_lo /\
          read (memory :> bytes64 (word_add b (word 168))) s = lk_hi /\
          read (memory :> bytes128 (word_add b (word 144))) s = rk9)
     (\s. read PC s = word (pc + 0x44) /\
          read X0 s = x0_init /\
          read X1 s = x1_init /\
          read X8 s = b /\
          read X17 s = (word 10:64 word) /\
          read X19 s = word_add b (word 160) /\
          read X13 s = lk_lo /\
          read X14 s = lk_hi /\
          read X4 s = word_add x0_init (word_ushr x1_init 3) /\
          read X5 s = word_ushr x1_init 3 /\
          read Q31 s = rk9)
     (MAYCHANGE [PC; X4; X5; X13; X14; X17; X19] ,,
      MAYCHANGE [Q31] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (12--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s057) — ivec-load + counter setup cut.                           *)
(*                                                                           *)
(* The 4 instructions at kernel offsets 0x44..0x50 (slice instr indices      *)
(* 18..21) load the initial counter from the ivec buffer and pre-decrement  *)
(* the byte count for the round-down-to-64 step that follows:                *)
(*                                                                           *)
(*   0x44  mov x15, x5                ; save byte_len before rounding        *)
(*   0x48  ldp x10, x11, [x16]        ; ctr96_b64, ctr96_t32 (scalar copies)*)
(*   0x4c  ld1 {v0.16b}, [x16]        ; ctr0 (whole 128-bit counter)        *)
(*   0x50  sub x5, x5, #1             ; byte_len - 1                        *)
(*                                                                           *)
(* The cut takes ivec memory preconditions for the two 64-bit halves and    *)
(* the 128-bit whole — both shapes are needed because the kernel uses both *)
(* the scalar (X10/X11) and vector (Q0) views of the same counter bytes.    *)
(* The stepper handles the redundancy via component aliasing; the           *)
(* precondition explicitly lists both shapes since the spec doesn't reduce  *)
(* one to the other automatically.                                          *)
(*                                                                           *)
(* MAYCHANGE again split by component type per s057's pattern:              *)
(* [PC; X5; X10; X11; X15] (int64), [Q0] (int128), [events].                *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_IVEC_CTR_CORRECT = prove
 (`!pc (a:int64) (sx5_pre:int64) (ctr_lo:int64) (ctr_hi:int64) (ctr0:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
          read PC s = word (pc + 0x44) /\
          read X16 s = a /\
          read X5 s = sx5_pre /\
          read (memory :> bytes64 a) s = ctr_lo /\
          read (memory :> bytes64 (word_add a (word 8))) s = ctr_hi /\
          read (memory :> bytes128 a) s = ctr0)
     (\s. read PC s = word (pc + 0x54) /\
          read X16 s = a /\
          read X10 s = ctr_lo /\
          read X11 s = ctr_hi /\
          read X15 s = sx5_pre /\
          read X5 s = word_sub sx5_pre (word 1) /\
          read Q0 s = ctr0)
     (MAYCHANGE [PC; X5; X10; X11; X15] ,,
      MAYCHANGE [Q0] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (18--21) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s059) — round-keys preload cut.                                  *)
(*                                                                           *)
(* The 39-instruction range at kernel byte offsets 0x54..0xf0 (slice instr  *)
(* indices 22..60) loads round keys rk0..rk7 (excluding rk4 = Q22 which is  *)
(* loaded later in the H-table range), interleaved with the start of the    *)
(* counter setup (Q1/Q2/Q3 from Q0 via fmov + counter increments) and the   *)
(* first four AES rounds on Q0..Q3:                                         *)
(*                                                                           *)
(*   0x54  ldr  q18, [x8]                       ; rk0  -> Q18                *)
(*   0x5c  ldr  q25, [x8, #112]                 ; rk7  -> Q25                *)
(*   0x94  ldr  q19, [x8, #16]                  ; rk1  -> Q19                *)
(*   0xa8  ldr  q20, [x8, #32]                  ; rk2  -> Q20                *)
(*   0xcc  ldr  q21, [x8, #48]                  ; rk3  -> Q21                *)
(*   0xd8  ldr  q24, [x8, #96]                  ; rk6  -> Q24                *)
(*   0xe4  ldr  q23, [x8, #80]                  ; rk5  -> Q23                *)
(*                                                                           *)
(* The post asserts the seven round-key loads.  Q22 (rk4 from [x8,#64]) is  *)
(* loaded inside the H-table range (0xf0..0x244) and is NOT covered by      *)
(* this cut.  Q0..Q3, X5/X9/X11/X12, and round-key Qs go in MAYCHANGE.      *)
(* SOME_FLAGS is NOT in MAYCHANGE: this range has no flag-setting           *)
(* instructions (no cmp / adds variant).                                    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_ROUND_KEYS_CORRECT = prove
 (`!pc (b:int64)
       (rk0:int128) (rk1:int128) (rk2:int128) (rk3:int128)
       (rk5:int128) (rk6:int128) (rk7:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
          read PC s = word (pc + 0x54) /\
          read X8 s = b /\
          read (memory :> bytes128 b) s = rk0 /\
          read (memory :> bytes128 (word_add b (word 16))) s = rk1 /\
          read (memory :> bytes128 (word_add b (word 32))) s = rk2 /\
          read (memory :> bytes128 (word_add b (word 48))) s = rk3 /\
          read (memory :> bytes128 (word_add b (word 80))) s = rk5 /\
          read (memory :> bytes128 (word_add b (word 96))) s = rk6 /\
          read (memory :> bytes128 (word_add b (word 112))) s = rk7)
     (\s. read PC s = word (pc + 0xf0) /\
          read X8 s = b /\
          read Q18 s = rk0 /\
          read Q19 s = rk1 /\
          read Q20 s = rk2 /\
          read Q21 s = rk3 /\
          read Q23 s = rk5 /\
          read Q24 s = rk6 /\
          read Q25 s = rk7)
     (MAYCHANGE [PC; X5; X9; X11; X12] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3;
                 Q18; Q19; Q20; Q21; Q23; Q24; Q25] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (22--60) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s058) — H-table load + karatsuba_mid construction cut.           *)
(*                                                                           *)
(* The 85-instruction range at kernel byte offsets 0xf0..0x244 contains the  *)
(* four `ldr q12/q13/q14/q15, [x6, ...]` H-power table loads interleaved    *)
(* with AES rounds and round-key loads, plus the six `trn1`/`trn2`/`eor`    *)
(* instructions that build Q16/Q17 = packed `karatsuba_mid` pairs.          *)
(*                                                                           *)
(* Spec mapping (using `byteswap128 x = word_join x_lo x_hi`):                *)
(*                                                                           *)
(*   ldr q14, [x6, #48] ; v14 = byteswap128(h_power(ghash_twist h) 2)       *)
(*   ldr q13, [x6, #32] ; v13 = byteswap128(h_power(ghash_twist h) 1)       *)
(*   ldr q15, [x6, #80] ; v15 = byteswap128(h_power(ghash_twist h) 3)       *)
(*   ldr q12, [x6]      ; v12 = byteswap128(h_power(ghash_twist h) 0)       *)
(*                                                                           *)
(*   trn2  v17.2d,  v14.2d, v15.2d                                          *)
(*     ; v17 = word_interleave_hi v14 v15                                   *)
(*     ;     = word_join (h_power 3)_LO (h_power 2)_LO                      *)
(*   trn1  v9.2d,   v14.2d, v15.2d                                          *)
(*     ; v9  = word_join (h_power 3)_HI (h_power 2)_HI                      *)
(*   trn2  v16.2d,  v12.2d, v13.2d                                          *)
(*     ; v16 = word_join (h_power 1)_LO (h_power 0)_LO                      *)
(*   eor   v17.16b, v17.16b, v9.16b                                         *)
(*     ; v17 = word_join (km(h_power 3)) (km(h_power 2))                    *)
(*   trn1  v8.2d,   v12.2d, v13.2d                                          *)
(*     ; v8  = word_join (h_power 1)_HI (h_power 0)_HI                      *)
(*   eor   v16.16b, v16.16b, v8.16b                                         *)
(*     ; v16 = word_join (km(h_power 1)) (km(h_power 0))                    *)
(*                                                                           *)
(* The post Q12..Q17 layout exactly matches the Phase 8 wrapper PRE          *)
(* (`AES_GCM_MAIN_LOOP_WRAPPER_FULL_CORRECT` parameters q12..q17), so this   *)
(* cut bridges the prelude's H-table load to the wrapper-pre's H-table       *)
(* state.  The Q16/Q17 raw post produced by the simulator after `eor` is    *)
(*                                                                           *)
(*   word_xor (word_join (bs.lo,bs.lo)) (word_join (bs.hi,bs.hi))           *)
(*                                                                           *)
(* (where bs = byteswap128 of the relevant h_power); after unfolding         *)
(* `byteswap128` and `karatsuba_mid`, `WORD_BLAST` discharges the equality   *)
(* in <1s.                                                                   *)
(*                                                                           *)
(* MAYCHANGE captures everything clobbered in this 85-instr range:           *)
(*   - Q0..Q3 (AES rounds 1..8 on counters)                                  *)
(*   - Q8, Q9 (intermediate trn1 results)                                    *)
(*   - Q11 (loaded from [x3] at offset 0x160 + ext + rev64)                  *)
(*   - Q12..Q17 (H-table state — the post specifies these)                   *)
(*   - Q22 (rk4 from [x8,#64]); Q26 (rk8 from [x8,#128])                     *)
(*   - Q27..Q30 (round keys rk9..rk12; rk10..rk12 unused for AES-128)        *)
(*   - X9, X12 (counter scratch via add/orr/rev)                             *)
(*   - SOME_FLAGS (cmp at 0x224 sets NF/ZF/CF/VF)                            *)
(*   - events (memory loads)                                                  *)
(* Note Q18..Q21, Q23..Q25 are NOT written in 0xf0..0x244 — those round-     *)
(* keys are loaded earlier in the prelude (0x54..0xf0) and pass through      *)
(* this slice unchanged.  Tightening MAYCHANGE to exclude them keeps         *)
(* downstream cuts via ARM_BIGSTEP_TAC composition able to thread their      *)
(* values from before this range to after.                                    *)
(*                                                                           *)
(* The slice instr indices for offsets 0xf0..0x240 (last instruction before  *)
(* b.ge at 0x244) are 61..145 (1-based, since 0xf0/4+1 = 61, 0x240/4+1 =     *)
(* 145).                                                                     *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_HTABLE_KMID_CORRECT = prove
 (`!pc (htable_ptr:int64) (h:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_prelude_slice_mc)
                   (htable_ptr, 96)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0xf0) /\
              read X6 s = htable_ptr /\
              read (memory :> bytes128 htable_ptr) s =
                byteswap128 (h_power (ghash_twist h) 0) /\
              read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
                byteswap128 (h_power (ghash_twist h) 1) /\
              read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
                byteswap128 (h_power (ghash_twist h) 2) /\
              read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
                byteswap128 (h_power (ghash_twist h) 3))
         (\s. read PC s = word (pc + 0x244) /\
              read X6 s = htable_ptr /\
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
         (MAYCHANGE [PC; X9; X12] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q8; Q9; Q11;
                     Q12; Q13; Q14; Q15; Q16; Q17;
                     Q22; Q26; Q27; Q28; Q29; Q30] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC]) THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (61--145) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[byteswap128; karatsuba_mid] THEN CONV_TAC WORD_BLAST;
    REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s060) — first 4-block region opening: b.ge fall-through + first  *)
(* two plaintext-block loads (slice instr indices 146..149, kernel offsets  *)
(* 0x244..0x254).                                                            *)
(*                                                                           *)
(* This is the first cut in the 0x244..0x308 first-4-block region (the      *)
(* "Lenc_finish_first_blocks" pre-loop preamble that handles the iter-0     *)
(* AES-CTR encrypt of 4 plaintext blocks before the main loop).  The cut    *)
(* covers:                                                                   *)
(*                                                                           *)
(*   0x244  b.ge .Lenc_tail               ; falls through under condition_LT*)
(*   0x248  ldp x19, x20, [x0, #16]        ; pt block 1 halves              *)
(*   0x24c  rev w9, w12                    ; counter byte-swap scratch      *)
(*   0x250  ldp x6, x7, [x0]               ; pt block 0 halves              *)
(*                                                                           *)
(* The b.ge falls through when `~(NF <=> VF)` (signed-LT) holds; under the  *)
(* main-loop entry, this corresponds to `condition_semantics Condition_LT`  *)
(* which is what the wrapper sees as `i < N` for iteration 0.  The b.ge's   *)
(* `~(NF <=> VF)` precondition is supplied by the cmp at 0x224 (inside the  *)
(* H-table cut's range) when the input pointer is strictly less than the    *)
(* end pointer.                                                              *)
(*                                                                           *)
(* The two LDPs introduce 8 bytes each of plaintext: block 1's two 64-bit   *)
(* halves at [X0+16, X0+24] and block 0's at [X0, X0+8].  Memory at these   *)
(* offsets is named in the precondition as `b0_lo, b0_hi, b1_lo, b1_hi`.   *)
(*                                                                           *)
(* Pre `val a + 16 < val sx5` ensures the simulator can rule out (1) the    *)
(* code region overlapping with [X0..X0+24] (program-text non-overlap is    *)
(* implicit via `aligned_bytes_loaded`) and (2) any X5-related pointer       *)
(* arithmetic from underflowing.  Pre `val a + 64 < 2 EXP 63` is for the    *)
(* later `add x0, x0, #0x40` (in the next cut); kept here for forward       *)
(* compatibility with the chained cut composition.                          *)
(*                                                                           *)
(* MAYCHANGE: PC, X6/X7 (pt block 0), X9 (rev w9 scratch), X19/X20 (pt      *)
(* block 1).                                                                 *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_PT01_LOAD_CORRECT = prove
 (`!pc (a:int64) (sx5:int64)
       (b0_lo:int64) (b0_hi:int64) (b1_lo:int64) (b1_hi:int64).
    val a + 64 < 2 EXP 63 /\ val a + 16 < val sx5
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x244) /\
              read X0 s = a /\
              read X5 s = sx5 /\
              ~(read NF s <=> read VF s) /\
              read (memory :> bytes64 a) s = b0_lo /\
              read (memory :> bytes64 (word_add a (word 8))) s = b0_hi /\
              read (memory :> bytes64 (word_add a (word 16))) s = b1_lo /\
              read (memory :> bytes64 (word_add a (word 24))) s = b1_hi)
         (\s. read PC s = word (pc + 0x254) /\
              read X0 s = a /\
              read X5 s = sx5 /\
              read X6 s = b0_lo /\
              read X7 s = b0_hi /\
              read X19 s = b1_lo /\
              read X20 s = b1_hi)
         (MAYCHANGE [PC; X6; X7; X9; X19; X20] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (146--149) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s060) — first 4-block region: plaintext blocks 2 & 3 loads +    *)
(* input pointer advance (slice instr indices 150..152, kernel offsets      *)
(* 0x254..0x260).                                                            *)
(*                                                                           *)
(*   0x254  ldp x23, x24, [x0, #48]        ; pt block 3 halves              *)
(*   0x258  ldp x21, x22, [x0, #32]        ; pt block 2 halves              *)
(*   0x25c  add x0, x0, #0x40              ; advance input ptr by 64 bytes  *)
(*                                                                           *)
(* Following PT01_LOAD's exit at 0x254, this cut completes the plaintext    *)
(* load phase by reading blocks 2 and 3 (4 X-register halves) and bumping   *)
(* the input pointer past the consumed 64 bytes.  After this cut, X0 points *)
(* at the next 4-block group (or end-of-input + tail).                       *)
(*                                                                           *)
(* Pre `val a + 64 < 2 EXP 63` ensures the `add x0, x0, #0x40` doesn't      *)
(* overflow.                                                                 *)
(*                                                                           *)
(* MAYCHANGE: PC, X0 (advance), X21/X22 (pt block 2), X23/X24 (pt block 3). *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_PT23_LOAD_CORRECT = prove
 (`!pc (a:int64) (sx5:int64)
       (b2_lo:int64) (b2_hi:int64) (b3_lo:int64) (b3_hi:int64).
    val a + 64 < 2 EXP 63
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x254) /\
              read X0 s = a /\
              read X5 s = sx5 /\
              read (memory :> bytes64 (word_add a (word 32))) s = b2_lo /\
              read (memory :> bytes64 (word_add a (word 40))) s = b2_hi /\
              read (memory :> bytes64 (word_add a (word 48))) s = b3_lo /\
              read (memory :> bytes64 (word_add a (word 56))) s = b3_hi)
         (\s. read PC s = word (pc + 0x260) /\
              read X0 s = word_add a (word 64) /\
              read X5 s = sx5 /\
              read X21 s = b2_lo /\
              read X22 s = b2_hi /\
              read X23 s = b3_lo /\
              read X24 s = b3_hi)
         (MAYCHANGE [PC; X0; X21; X22; X23; X24] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (150--152) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s060) — first 4-block region: scalar XORs of plaintext halves   *)
(* with rk10 (last round key) halves + first fmov d5 (slice instr indices  *)
(* 153..158, kernel offsets 0x260..0x278).                                  *)
(*                                                                           *)
(*   0x260  eor x19, x19, x13              ; pt1_lo XOR rk10_lo             *)
(*   0x264  eor x20, x20, x14              ; pt1_hi XOR rk10_hi             *)
(*   0x268  fmov d5, x19                    ; Q5 low half = pt1_lo XOR rk10_lo
                                             ; (Q5 high cleared via fmov d) *)
(*   0x26c  eor x6, x6, x13                ; pt0_lo XOR rk10_lo             *)
(*   0x270  eor x7, x7, x14                ; pt0_hi XOR rk10_hi             *)
(*   0x274  eor x24, x24, x14              ; pt3_hi XOR rk10_hi             *)
(*                                                                           *)
(* These 6 instructions XOR plaintext halves with the AES last-round-key    *)
(* (rk10) halves so that subsequent vector EOR with the AES-encrypted       *)
(* counter (which has 10 aese rounds applied — i.e. is at the rk9 stage)   *)
(* completes the final round.  This implements the standard AES-CTR        *)
(* optimization where the last key-schedule XOR is folded into the          *)
(* plaintext-XOR.                                                            *)
(*                                                                           *)
(* `fmov d5, x19` writes a 64-bit value to D5; the architectural semantic   *)
(* zero-extends to the full Q5 register (top half cleared).  The simulator  *)
(* emits this as `read Q5 s = word_zx (word_xor b1_lo rk10_lo) :int128`.    *)
(*                                                                           *)
(* MAYCHANGE: PC, X6/X7 (pt0 XOR'd), X19/X20 (pt1 XOR'd), X24 (pt3_hi       *)
(* XOR'd), Q5 (low half set).                                               *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_RK10_XOR0_CORRECT = prove
 (`!pc (a:int64) (sx5:int64)
       (rk10_lo:int64) (rk10_hi:int64)
       (b0_lo:int64) (b0_hi:int64) (b1_lo:int64) (b1_hi:int64)
       (b2_lo:int64) (b2_hi:int64) (b3_lo:int64) (b3_hi:int64).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
          read PC s = word (pc + 0x260) /\
          read X0 s = a /\
          read X5 s = sx5 /\
          read X13 s = rk10_lo /\
          read X14 s = rk10_hi /\
          read X6 s = b0_lo /\
          read X7 s = b0_hi /\
          read X19 s = b1_lo /\
          read X20 s = b1_hi /\
          read X21 s = b2_lo /\
          read X22 s = b2_hi /\
          read X23 s = b3_lo /\
          read X24 s = b3_hi)
     (\s. read PC s = word (pc + 0x278) /\
          read X0 s = a /\
          read X5 s = sx5 /\
          read X13 s = rk10_lo /\
          read X14 s = rk10_hi /\
          read X6 s = word_xor b0_lo rk10_lo /\
          read X7 s = word_xor b0_hi rk10_hi /\
          read X19 s = word_xor b1_lo rk10_lo /\
          read X20 s = word_xor b1_hi rk10_hi /\
          read X21 s = b2_lo /\
          read X22 s = b2_hi /\
          read X23 s = b3_lo /\
          read X24 s = word_xor b3_hi rk10_hi /\
          read Q5 s = word_zx (word_xor b1_lo rk10_lo) :int128)
     (MAYCHANGE [PC; X6; X7; X19; X20; X24] ,,
      MAYCHANGE [Q5] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (153--158) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s060) — first 4-block region: Q4 build + cmp + scalar XOR       *)
(* (slice instr indices 159..162, kernel offsets 0x278..0x288).             *)
(*                                                                           *)
(*   0x278  fmov d4, x6                    ; Q4 low half = pt0_lo XOR rk10_lo*)
(*   0x27c  cmp x0, x5                     ; reset flags (sets NF/ZF/CF/VF) *)
(*   0x280  fmov v4.d[1], x7                ; Q4 high half = pt0_hi XOR rk10_hi
                                            ; (combined: word_insert form)  *)
(*   0x284  eor x23, x23, x13              ; pt3_lo XOR rk10_lo             *)
(*                                                                           *)
(* After the first fmov d4, Q4 = `word_zx X6` (64-bit value zero-extended). *)
(* After fmov v4.d[1], the high 64 bits of Q4 are written to X7.  The       *)
(* simulator's combined emit form is                                         *)
(* `word_insert (word_zx X6_in_state) (64,64) X7_in_state`.  This is the    *)
(* canonical AES-GCM body emit form (see body cuts at line 1753+).          *)
(*                                                                           *)
(* The cmp at 0x27c sets all four flags from `X0 - X5`; the simulator       *)
(* propagates the symbolic-form flag facts.  These are SOME_FLAGS in the   *)
(* MAYCHANGE frame.                                                          *)
(*                                                                           *)
(* Note: the X6/X7 inputs in the precondition correspond to the rk10-XOR'd  *)
(* plaintext halves (output of the previous cut), but at this cut's level   *)
(* they're just opaque 64-bit values.  Calling code should bind X6/X7 to    *)
(* word_xor b0_lo rk10_lo and word_xor b0_hi rk10_hi.                       *)
(*                                                                           *)
(* MAYCHANGE: PC, X23 (XOR'd), Q4 (Q4 fully built), SOME_FLAGS (cmp).       *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_Q4_CMP_CORRECT = prove
 (`!pc (a:int64) (sx5:int64)
       (b0_lo:int64) (b0_hi:int64)
       (rk10_lo:int64) (rk10_hi:int64) (b3_lo:int64).
    val a + 64 < 2 EXP 63
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x278) /\
              read X0 s = a /\
              read X5 s = sx5 /\
              read X13 s = rk10_lo /\
              read X14 s = rk10_hi /\
              read X6 s = b0_lo /\
              read X7 s = b0_hi /\
              read X23 s = b3_lo)
         (\s. read PC s = word (pc + 0x288) /\
              read X0 s = a /\
              read X5 s = sx5 /\
              read X13 s = rk10_lo /\
              read X14 s = rk10_hi /\
              read X6 s = b0_lo /\
              read X7 s = b0_hi /\
              read X23 s = word_xor b3_lo rk10_lo /\
              read Q4 s = word_insert (word_zx b0_lo :int128) (64,64) b0_hi)
         (MAYCHANGE [PC; X23] ,,
          MAYCHANGE [Q4] ,,
          MAYCHANGE SOME_FLAGS)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (159--162) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s060) — first 4-block region: Q5 finalize + Q6 build + Q7 low + *)
(* counter advance (slice instr indices 163..170, kernel offsets             *)
(* 0x288..0x2a8).                                                            *)
(*                                                                           *)
(*   0x288  eor x21, x21, x13              ; pt2_lo XOR rk10_lo             *)
(*   0x28c  fmov v5.d[1], x20               ; Q5 high half = X20 (Q5 done)  *)
(*   0x290  fmov d6, x21                    ; Q6 low half = X21              *)
(*   0x294  add w12, w12, #0x1               ; counter increment             *)
(*   0x298  orr x9, x11, x9, lsl #32         ; counter scratch               *)
(*   0x29c  fmov d7, x23                    ; Q7 low half = X23              *)
(*   0x2a0  eor x22, x22, x14              ; pt2_hi XOR rk10_hi             *)
(*   0x2a4  fmov v6.d[1], x22                ; Q6 high half = X22 (Q6 done)  *)
(*                                                                           *)
(* After this cut Q5 and Q6 are fully built (in canonical word_insert       *)
(* emit form), Q7 has its low half but high half is still pending until    *)
(* 0x2d4 (`fmov v7.d[1], x24`).                                             *)
(*                                                                           *)
(* The counter `add w12, w12, #1` advances X12 by 1 (mod 2^32 since W12);   *)
(* simulator emits `word_zx (word_add (word_zx (word_zx sx12)) (word 1))`  *)
(* which collapses to `word_zx (word_add sx12 (word 1))` via WORD_ZX_ZX +   *)
(* DIMINDEX_32/64 + LE_REFL.                                                 *)
(*                                                                           *)
(* The Q5 form emerges as `word_insert (word_zx (b1_lo XOR rk10_lo)) (64,64)*)
(* (b1_hi XOR rk10_hi)` if q5_pre was `word_zx (b1_lo XOR rk10_lo)` from   *)
(* the prior cut.  Stated here parametrically as `word_insert q5_pre (64,64)*)
(* X20_value` — caller composes by binding q5_pre.                          *)
(*                                                                           *)
(* MAYCHANGE: PC, X9 (orr scratch), X12 (counter), X21/X22 (XOR'd), Q5/Q6/Q7*)
(* (built).                                                                  *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_Q5Q6Q7LO_CTR_CORRECT = prove
 (`!pc (b2_lo:int64) (rk10_lo:int64) (rk10_hi:int64)
       (b1_lo_pre:int64) (b1_hi_pre:int64) (b2_hi:int64) (b3_lo_pre:int64)
       (sx9:int64) (sx11:int64) (sx12:int32)
       (q5_pre:int128) (q6_pre:int128) (q7_pre:int128).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
          read PC s = word (pc + 0x288) /\
          read X9 s = sx9 /\
          read X11 s = sx11 /\
          read X12 s = word_zx sx12 /\
          read X13 s = rk10_lo /\
          read X14 s = rk10_hi /\
          read X19 s = b1_lo_pre /\
          read X20 s = b1_hi_pre /\
          read X21 s = b2_lo /\
          read X22 s = b2_hi /\
          read X23 s = b3_lo_pre /\
          read Q5 s = q5_pre /\
          read Q6 s = q6_pre /\
          read Q7 s = q7_pre)
     (\s. read PC s = word (pc + 0x2a8) /\
          read X12 s = word_zx (word_add sx12 (word 1):int32) /\
          read X19 s = b1_lo_pre /\
          read X20 s = b1_hi_pre /\
          read X21 s = word_xor b2_lo rk10_lo /\
          read X22 s = word_xor b2_hi rk10_hi /\
          read X23 s = b3_lo_pre /\
          read Q5 s = word_insert q5_pre (64,64) b1_hi_pre /\
          read Q6 s = word_insert (word_zx (word_xor b2_lo rk10_lo) :int128)
                                   (64,64) (word_xor b2_hi rk10_hi) /\
          read Q7 s = word_zx b3_lo_pre :int128)
     (MAYCHANGE [PC; X9; X12; X21; X22] ,,
      MAYCHANGE [Q5; Q6; Q7] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (163--170) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s060) — first 4-block region: ciphertext blocks 0/1 + Q0 reload *)
(* (slice instr indices 171..176, kernel offsets 0x2a8..0x2c0).             *)
(*                                                                           *)
(*   0x2a8  eor v4.16b, v4.16b, v0.16b      ; ciphertext block 0 in Q4      *)
(*   0x2ac  fmov d0, x10                     ; Q0 = next-counter low (X10)  *)
(*   0x2b0  fmov v0.d[1], x9                  ; Q0 = full next counter      *)
(*   0x2b4  rev w9, w12                       ; counter byte-swap scratch   *)
(*   0x2b8  add w12, w12, #0x1                ; counter advance             *)
(*   0x2bc  eor v5.16b, v5.16b, v1.16b      ; ciphertext block 1 in Q5      *)
(*                                                                           *)
(* Q4 absorbs the first AES-encrypted-counter into the rk10-XOR'd plaintext *)
(* word (i.e. completing the AES final round + plaintext XOR).  Q5 likewise *)
(* for block 1.  Q0 is overwritten with the NEXT counter to start its       *)
(* 10-round AES pipeline for the next iteration.                             *)
(*                                                                           *)
(* Q0's new value is `word_insert (word_zx X10) (64,64) X9` — the canonical *)
(* counter-byteswap-into-128 emit form.                                      *)
(*                                                                           *)
(* MAYCHANGE: PC, X9 (rev scratch), X12 (counter), Q0 (next counter),       *)
(* Q4/Q5 (ciphertexts).  Note Q4/Q5 take the simulator's emit order        *)
(* `word_xor q_aes q_pt` (NOT pt-first); callers must pass q_aes_pre as Q0  *)
(* and q_pt_pre as Q4 since the simulator's `eor v4, v4, v0` reads v4 first.*)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_CT01_CTRADV_CORRECT = prove
 (`!pc (q4_pre:int128) (q0_pre:int128) (q5_pre:int128) (q1_pre:int128)
       (sx10:int64) (sx9:int64) (sx12:int32).
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
          read PC s = word (pc + 0x2a8) /\
          read X9 s = sx9 /\
          read X10 s = sx10 /\
          read X12 s = word_zx sx12 /\
          read Q0 s = q0_pre /\
          read Q1 s = q1_pre /\
          read Q4 s = q4_pre /\
          read Q5 s = q5_pre)
     (\s. read PC s = word (pc + 0x2c0) /\
          read X10 s = sx10 /\
          read X12 s = word_zx (word_add sx12 (word 1):int32) /\
          read Q0 s = word_insert (word_zx sx10 :int128) (64,64) sx9 /\
          read Q4 s = word_xor q0_pre q4_pre /\
          read Q5 s = word_xor q1_pre q5_pre)
     (MAYCHANGE [PC; X9; X12] ,,
      MAYCHANGE [Q0; Q4; Q5] ,,
      MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (171--176) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s060) — first 4-block region: Q1 next-counter + ciphertext      *)
(* store 0 + Q7 high half (slice instr indices 177..183, kernel offsets     *)
(* 0x2c0..0x2dc).                                                            *)
(*                                                                           *)
(*   0x2c0  fmov d1, x10                     ; Q1 low half = next-counter   *)
(*   0x2c4  orr x9, x11, x9, lsl #32         ; X9 = NEW counter scratch     *)
(*   0x2c8  fmov v1.d[1], x9                  ; Q1 high half = NEW X9       *)
(*   0x2cc  rev w9, w12                       ; counter byte-swap scratch   *)
(*   0x2d0  st1 {v4.16b}, [x2], #16          ; store ciphertext block 0     *)
(*   0x2d4  fmov v7.d[1], x24                 ; Q7 high half = X24          *)
(*   0x2d8  orr x9, x11, x9, lsl #32          ; X9 = NEXT counter scratch   *)
(*                                                                           *)
(* This is the FIRST cut introducing a memory store (`st1 {v4.16b}, [x2],   *)
(* #16` writes 16 bytes of ciphertext block 0 + post-increments X2 by 16). *)
(* The `nonoverlapping (word pc, LENGTH ...) (cptr, 16)` precondition       *)
(* certifies the program text is not modified by this store.                *)
(*                                                                           *)
(* Q1 receives the next-iteration counter via fmov d1 + fmov v1.d[1].  The *)
(* counter's high half goes through `orr x9, x11, x9 lsl 32` (which        *)
(* assembles a 32-bit counter into the upper half of a 64-bit word).        *)
(*                                                                           *)
(* Q7 receives its high half from X24 (= b3_hi XOR rk10_hi from earlier    *)
(* cut), completing the Q7 build started by `fmov d7, x23` at 0x29c.       *)
(*                                                                           *)
(* MAYCHANGE: PC, X2 (advance by 16), X9 (orr scratch), Q1 (next counter), *)
(* Q7 (high half), `memory :> bytes128 cptr` (the ciphertext block).        *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_Q1NEXT_ST0_Q7HI_CORRECT = prove
 (`!pc (cptr:int64) (q4_post:int128)
       (sx10:int64) (sx11:int64) (sx9:int64) (sx12:int32)
       (sx24:int64) (q7_pre:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_prelude_slice_mc)
                   (cptr, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x2c0) /\
              read X2 s = cptr /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X11 s = sx11 /\
              read X12 s = word_zx sx12 /\
              read X24 s = sx24 /\
              read Q4 s = q4_post /\
              read Q7 s = q7_pre)
         (\s. read PC s = word (pc + 0x2dc) /\
              read X2 s = word_add cptr (word 16) /\
              read X10 s = sx10 /\
              read X11 s = sx11 /\
              read Q4 s = q4_post /\
              read Q1 s = word_insert (word_zx sx10 :int128)
                                       (64,64)
                                       (word_or sx11 (word_shl sx9 32)) /\
              read Q7 s = word_insert q7_pre (64,64) sx24 /\
              read (memory :> bytes128 cptr) s = q4_post)
         (MAYCHANGE [PC; X2; X9] ,,
          MAYCHANGE [Q1; Q7] ,,
          MAYCHANGE [memory :> bytes128 cptr] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC]) THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (177--183) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s061) — first 4-block region: ciphertext stores 1, 2 + Q2       *)
(* next-counter (slice instr indices 184..190, kernel offsets               *)
(* 0x2dc..0x2f4).                                                            *)
(*                                                                           *)
(*   0x2dc  eor v6.16b, v6.16b, v2.16b      ; ciphertext block 2 in Q6      *)
(*   0x2e0  st1 {v5.16b}, [x2], #16         ; store ciphertext block 1      *)
(*   0x2e4  add w12, w12, #0x1              ; counter advance               *)
(*   0x2e8  fmov d2, x10                    ; Q2 low half = next-counter    *)
(*   0x2ec  fmov v2.d[1], x9                ; Q2 high half = X9             *)
(*   0x2f0  st1 {v6.16b}, [x2], #16         ; store ciphertext block 2      *)
(*   0x2f4  rev w9, w12                     ; counter byte-swap scratch     *)
(*                                                                           *)
(* This cut absorbs the v2-encrypted plaintext (Q2 = AES-encrypted counter  *)
(* for block 2) into Q6 (which holds plaintext block 2 XOR'd with rk10).    *)
(* The two `st1` writes lay down ciphertext blocks 1 and 2 at [cptr8,       *)
(* cptr8+32) and post-increment X2 by 32 total.                              *)
(*                                                                           *)
(* Q2 is then overwritten with the next-iteration counter (low = X10, high  *)
(* = X9 carrying the prior `orr x9, x11, x9 lsl 32`-assembled counter half).*)
(*                                                                           *)
(* Note Q6's exit form is `word_xor q2_pre q6_pre` (NOT q6_pre q2_pre):     *)
(* the simulator's `eor v6, v6, v2` emit reads v6 first, so the second      *)
(* operand q2_pre is the LHS of `word_xor`.  Same convention as cut 6.      *)
(*                                                                           *)
(* MAYCHANGE: PC, X2 (advance by 32), X9 (rev scratch), X12 (counter        *)
(* advance), Q2 (next counter), Q6 (ciphertext), memory :> bytes128 chunks  *)
(* at cptr8 and cptr8+16 (the two ciphertext blocks), events.               *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_CT12_Q2NEXT_CORRECT = prove
 (`!pc (cptr8:int64)
       (q5_pre:int128) (q6_pre:int128) (q2_pre:int128)
       (sx9:int64) (sx10:int64) (sx12:int32).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_prelude_slice_mc)
                   (cptr8, 32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x2dc) /\
              read X2 s = cptr8 /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X12 s = word_zx sx12 /\
              read Q2 s = q2_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre)
         (\s. read PC s = word (pc + 0x2f8) /\
              read X2 s = word_add cptr8 (word 32) /\
              read X10 s = sx10 /\
              read X12 s = word_zx (word_add sx12 (word 1):int32) /\
              read Q2 s = word_insert (word_zx sx10 :int128) (64,64) sx9 /\
              read Q6 s = word_xor q2_pre q6_pre /\
              read (memory :> bytes128 cptr8) s = q5_pre /\
              read (memory :> bytes128 (word_add cptr8 (word 16))) s =
                   word_xor q2_pre q6_pre)
         (MAYCHANGE [PC; X2; X9; X12] ,,
          MAYCHANGE [Q2; Q6] ,,
          MAYCHANGE [memory :> bytes128 cptr8;
                     memory :> bytes128 (word_add cptr8 (word 16))] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC]) THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (184--190) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s061) — first 4-block region: ciphertext store 3 + b.ge          *)
(* fall-through to main-loop body (slice instr indices 191..194, kernel     *)
(* offsets 0x2f8..0x308).  This closes the 0x244..0x308 first-4-block       *)
(* prelude region.                                                            *)
(*                                                                           *)
(*   0x2f8  orr x9, x11, x9, lsl #32          ; X9 = NEW counter scratch    *)
(*   0x2fc  eor v7.16b, v7.16b, v3.16b        ; ciphertext block 3 in Q7    *)
(*   0x300  st1 {v7.16b}, [x2], #16           ; store ciphertext block 3    *)
(*   0x304  b.ge .Lenc_prepretail (0x5c8)     ; falls through to main loop   *)
(*                                                                           *)
(* Falls through to the main loop body at 0x308 under signed-LT condition   *)
(* (`~(NF <=> VF)`) — same b.ge fall-through pattern as the cut-1 b.ge      *)
(* at 0x244.  The b.ge at 0x304 jumps to `Lenc_prepretail` (0x5c8) when     *)
(* the input pointer has caught up to/passed the end (X0 ≥ X5), but the     *)
(* main-loop entry case has X0 strictly less, so the branch falls through.  *)
(*                                                                           *)
(* Q7 absorbs the AES-encrypted counter (Q3 = AES output for block 3) into  *)
(* the rk10-XOR'd plaintext block 3, completing the ciphertext for block 3. *)
(* The `st1 {v7.16b}, [x2], #16` writes ciphertext block 3 and advances X2  *)
(* by 16, completing the 4-block write (cptr9 = base + 48 from cuts 7+8).   *)
(*                                                                           *)
(* X9's exit value `word_or sx11 (word_shl sx9 32)` is the next-iteration's *)
(* high-half counter material; it'll be consumed by the next-iter's         *)
(* `fmov v.d[1], x9` chain.                                                  *)
(*                                                                           *)
(* MAYCHANGE: PC, X2 (advance by 16), X9 (orr scratch), Q7 (ciphertext),    *)
(* memory:bytes128 cptr9 (the ciphertext block), events.                    *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_CT3_BGE_CORRECT = prove
 (`!pc (cptr9:int64)
       (q3_pre:int128) (q7_pre:int128)
       (sx9:int64) (sx11:int64).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_prelude_slice_mc)
                   (cptr9, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x2f8) /\
              read X2 s = cptr9 /\
              read X9 s = sx9 /\
              read X11 s = sx11 /\
              read Q3 s = q3_pre /\
              read Q7 s = q7_pre /\
              ~(read NF s <=> read VF s))
         (\s. read PC s = word (pc + 0x308) /\
              read X2 s = word_add cptr9 (word 16) /\
              read X9 s = word_or sx11 (word_shl sx9 32) /\
              read Q7 s = word_xor q3_pre q7_pre /\
              read (memory :> bytes128 cptr9) s = word_xor q3_pre q7_pre)
         (MAYCHANGE [PC; X2; X9] ,,
          MAYCHANGE [Q7] ,,
          MAYCHANGE [memory :> bytes128 cptr9] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC]) THEN
  ARM_STEPS_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC (191--194) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s061) — chain composition of cuts 8 + 9 covering slice instr   *)
(* indices 184..194 (kernel offsets 0x2dc..0x308).                          *)
(*                                                                           *)
(* Validates the ARM_BIGSTEP_TAC chain composition pattern for cuts that    *)
(* introduce memory writes and have `nonoverlapping ==>` antecedents.       *)
(* The pattern:                                                              *)
(*                                                                           *)
(*   1.  ENSURES_INIT_TAC "s0"                                              *)
(*   2.  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst EXEC])     *)
(*       — required for ARM_BIGSTEP_TAC to verify the program isn't        *)
(*       modified by the cut's memory writes.                               *)
(*   3.  REWRITE_TAC[SOME_FLAGS] — required when MAYCHANGE includes         *)
(*       SOME_FLAGS (per `bigstep_with_memory_writes` memory).              *)
(*   4.  For each cut to chain:                                             *)
(*       a.  MP_TAC(SPECL[...] CUT_THM)                                     *)
(*       b.  ANTS_TAC THENL [REWRITE_TAC[NONOVERLAPPING_CLAUSES; ...] THEN  *)
(*           NONOVERLAPPING_TAC; ALL_TAC]                                   *)
(*       c.  ARM_BIGSTEP_TAC EXEC "sN" (where N is cumulative instr count) *)
(*   5.  ENSURES_FINAL_STATE_TAC                                            *)
(*   6.  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE — final closure;        *)
(*       WORD_RULE handles the residual `word_add (word_add ...) (word ...)*)
(*       = word_add ... (word ...)` arithmetic.                              *)
(*                                                                           *)
(* For X-register threading across cuts where the prior cut's POST doesn't *)
(* expose the register value (cut 8's MAYCHANGE includes X9 but no X9      *)
(* exit value), bind the next cut's X9 parameter to the unevaluated         *)
(* `read X9 (s7:armstate):int64` term.  ARM_BIGSTEP_TAC accepts this and    *)
(* propagates correctly.                                                     *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_CT123_BGE_CORRECT = prove
 (`!pc (cptr:int64)
       (q3_pre:int128) (q2_pre:int128) (q5_pre:int128) (q6_pre:int128)
       (sx9:int64) (sx10:int64) (sx11:int64) (sx12:int32)
       (q7_pre:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_prelude_slice_mc)
                   (cptr, 48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x2dc) /\
              read X2 s = cptr /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X11 s = sx11 /\
              read X12 s = word_zx sx12 /\
              read Q2 s = q2_pre /\
              read Q3 s = q3_pre /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              ~(read NF s <=> read VF s))
         (\s. read PC s = word (pc + 0x308) /\
              read X2 s = word_add cptr (word 48) /\
              read (memory :> bytes128 cptr) s = q5_pre /\
              read (memory :> bytes128 (word_add cptr (word 16))) s =
                   word_xor q2_pre q6_pre /\
              read (memory :> bytes128 (word_add cptr (word 32))) s =
                   word_xor q3_pre q7_pre)
         (MAYCHANGE [PC; X2; X9; X12] ,,
          MAYCHANGE [Q2; Q6; Q7] ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16));
                     memory :> bytes128 (word_add cptr (word 32))] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  MP_TAC(SPECL[`pc:num`; `cptr:int64`;
               `q5_pre:int128`; `q6_pre:int128`; `q2_pre:int128`;
               `sx9:int64`; `sx10:int64`; `sx12:int32`]
              AES_GCM_PRELUDE_FIRSTBLOCKS_CT12_Q2NEXT_CORRECT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES;
                fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC] THEN
    NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC "s7" THEN
  MP_TAC(SPECL[`pc:num`; `word_add cptr (word 32):int64`;
               `q3_pre:int128`; `q7_pre:int128`;
               `read X9 (s7:armstate):int64`; `sx11:int64`]
              AES_GCM_PRELUDE_FIRSTBLOCKS_CT3_BGE_CORRECT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES;
                fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC] THEN
    NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC "s11" THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 (s061) — chain composition cuts 7 + 8 + 9 covering slice instr  *)
(* indices 177..194 (kernel offsets 0x2c0..0x308).                          *)
(*                                                                           *)
(* Extension of CT123_BGE that also chains in cut 7 (Q1 next-counter +     *)
(* ciphertext store 0 + Q7 high half).  Demonstrates the full chain         *)
(* composition pattern for 3 cuts; the same pattern scales to all 9        *)
(* first-4-block cuts.                                                       *)
(*                                                                           *)
(* New tactic detail: the residual `word_add (word_add cptr (word 16))     *)
(* (word 16) = word_add cptr (word 32)` produced by ARM_BIGSTEP after cut 8 *)
(* needs SUBGOAL_THEN + RULE_ASSUM_TAC to normalise the memory location of *)
(* ciphertext block 2 in the assumption set BEFORE                          *)
(* ENSURES_FINAL_STATE_TAC tries to match it against the goal's            *)
(* `word_add cptr (word 32)` form.                                          *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_PRELUDE_FIRSTBLOCKS_Q1NEXT_CT123_BGE_CORRECT = prove
 (`!pc (cptr:int64) (q4_post:int128)
       (q3_pre:int128) (q2_pre:int128) (q5_pre:int128) (q6_pre:int128)
       (sx9:int64) (sx10:int64) (sx11:int64) (sx12:int32)
       (sx24:int64) (q7_pre:int128).
    nonoverlapping (word pc, LENGTH aes_gcm_main_loop_prelude_slice_mc)
                   (cptr, 64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes_gcm_main_loop_prelude_slice_mc /\
              read PC s = word (pc + 0x2c0) /\
              read X2 s = cptr /\
              read X9 s = sx9 /\
              read X10 s = sx10 /\
              read X11 s = sx11 /\
              read X12 s = word_zx sx12 /\
              read X24 s = sx24 /\
              read Q2 s = q2_pre /\
              read Q3 s = q3_pre /\
              read Q4 s = q4_post /\
              read Q5 s = q5_pre /\
              read Q6 s = q6_pre /\
              read Q7 s = q7_pre /\
              ~(read NF s <=> read VF s))
         (\s. read PC s = word (pc + 0x308) /\
              read X2 s = word_add cptr (word 64) /\
              read (memory :> bytes128 cptr) s = q4_post /\
              read (memory :> bytes128 (word_add cptr (word 16))) s = q5_pre /\
              read (memory :> bytes128 (word_add cptr (word 32))) s =
                   word_xor q2_pre q6_pre /\
              read (memory :> bytes128 (word_add cptr (word 48))) s =
                   word_xor q3_pre (word_insert q7_pre (64,64) sx24))
         (MAYCHANGE [PC; X2; X9; X12] ,,
          MAYCHANGE [Q1; Q2; Q6; Q7] ,,
          MAYCHANGE [memory :> bytes128 cptr;
                     memory :> bytes128 (word_add cptr (word 16));
                     memory :> bytes128 (word_add cptr (word 32));
                     memory :> bytes128 (word_add cptr (word 48))] ,,
          MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES;
                              fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  (* Cut 7: 0x2c0..0x2dc *)
  MP_TAC(SPECL[`pc:num`; `cptr:int64`; `q4_post:int128`;
               `sx10:int64`; `sx11:int64`; `sx9:int64`; `sx12:int32`;
               `sx24:int64`; `q7_pre:int128`]
              AES_GCM_PRELUDE_FIRSTBLOCKS_Q1NEXT_ST0_Q7HI_CORRECT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES;
                fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC] THEN
    NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC "s7" THEN
  (* Cut 8: 0x2dc..0x2f8 *)
  MP_TAC(SPECL[`pc:num`; `word_add cptr (word 16):int64`;
               `q5_pre:int128`; `q6_pre:int128`; `q2_pre:int128`;
               `read X9 (s7:armstate):int64`; `sx10:int64`; `sx12:int32`]
              AES_GCM_PRELUDE_FIRSTBLOCKS_CT12_Q2NEXT_CORRECT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES;
                fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC] THEN
    NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC "s14" THEN
  (* Cut 9: 0x2f8..0x308 *)
  MP_TAC(SPECL[`pc:num`; `word_add cptr (word 48):int64`;
               `q3_pre:int128`;
               `(word_insert (q7_pre:int128) (64,64) (sx24:int64)):int128`;
               `read X9 (s14:armstate):int64`; `sx11:int64`]
              AES_GCM_PRELUDE_FIRSTBLOCKS_CT3_BGE_CORRECT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES;
                fst AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC] THEN
    NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_MAIN_LOOP_PRELUDE_SLICE_EXEC "s18" THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add (cptr:int64) (word 16)) (word 16) =
                word_add cptr (word 32)` ASSUME_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add (word_add (cptr:int64) (word 16)) (word 16) =
                                        word_add cptr (word 32)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;
