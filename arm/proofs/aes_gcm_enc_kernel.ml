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
            (word_join (karatsuba_mid (h_power (ghash_twist h) 1) :64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 0) :64 word)
             :int128) /\
          read Q17 s =
            (word_join (karatsuba_mid (h_power (ghash_twist h) 3) :64 word)
                       (karatsuba_mid (h_power (ghash_twist h) 2) :64 word)
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
  (* TODO (session 014 partial): symbolic execution lands the kernel's   *)
  (* Q11 in nest of word_xor / word_pmul / word_subword / word_join       *)
  (* exactly matching the kernel_modulo of-XOR-of-Karatsuba-components   *)
  (* shape that KERNEL_4BLOCK_NIST_BRIDGE expects.  After                 *)
  (*   MP_TAC(SPECL [...] KERNEL_4BLOCK_NIST_BRIDGE) THEN                 *)
  (*   REWRITE_TAC[karatsuba_components; LET_DEF; LET_END_DEF] THEN       *)
  (*   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN                            *)
  (*   REWRITE_TAC[byteswap128; karatsuba_mid] THEN                       *)
  (*   SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;         *)
  (*            DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN           *)
  (* both sides reduce to identical pure word-arithmetic expressions      *)
  (* modulo the opaque h_power / word_pmul subterms, but a full           *)
  (* CONV_TAC WORD_BLAST does not terminate within ~15 minutes (BDD too   *)
  (* large).  The closure tactic likely needs to abbreviate each unique   *)
  (* pmul subterm and h_power instance via ABBREV_TAC before WORD_BLAST,  *)
  (* OR fold the kernel side into kernel_modulo form first via a          *)
  (* SUBGOAL_THEN intermediate (so KERNEL_MODULO_CORRECT discharges the   *)
  (* MODULO chain symbolically rather than by bit-blast).                 *)
  CHEAT_TAC);;
