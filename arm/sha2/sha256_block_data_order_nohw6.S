// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-256 multi-block compression using scalar instructions only
// (nohw6 = nohw5 + cyclic state-register naming to eliminate 6 MOVs/round).
//
// Optimisation relative to sha256_block_data_order_nohw5:
//   * Cyclic state-register naming. a..h live in a rotating set of eight
//     registers. At round t, logical state position j (0..7 <=> a..h) is
//     held in physical register w[4 + ((j - t) mod 8)]. The only writes
//     per round are new_e (into the slot that held d) and new_a (into the
//     slot that held h). This removes the 6 state-rotation MOVs per round
//     (384 per block) present in nohw5.
//   * Because the rotation cycle has period 8 and each period of the
//     schedule loop is 16 rounds, state returns to canonical w4..w11 at
//     every period boundary (0, 16, 32, 48) and after round 64. The proof
//     invariant shape is therefore identical to nohw5's at those boundaries.
//   * Schedule window layout, period structure (3 fused iterations then a
//     16-round D-tail), K-pointer handling, and frame size are unchanged
//     from nohw5.
//
// Input:
//   X0 = pointer to 8-word state (big-endian 32-bit lanes, in memory order)
//   X1 = pointer to message data (num_blocks * 64 bytes of big-endian words)
//   X2 = num_blocks (64-bit count; caller must ensure >= 1)
//   X3 = pointer to SHA-256 round constant table K[0..63]
// Output:
//   (memory at X0) = sha256_hash_blocks num_blocks blocks [a,b,c,d,e,f,g,h]
// Stack frame: 112 bytes.
//   [sp +   0 .. +  95]: saved x19..x30 (callee-saved frame)
//   [sp +  96 .. + 111]: per-block spill of x1 (data ptr) and x2 (counter)
// Preserves: X0, X3, X19..X28, X29, X30, SP.

        .text
        .globl  sha256_block_data_order_nohw6

// State register assignment as a function of K = t mod 8.
// K = 0:  a=w4,  b=w5,  c=w6,  d=w7,  e=w8,  f=w9,  g=w10, h=w11
// K = 1:  a=w11, b=w4,  c=w5,  d=w6,  e=w7,  f=w8,  g=w9,  h=w10
// K = 2:  a=w10, b=w11, c=w4,  d=w5,  e=w6,  f=w7,  g=w8,  h=w9
// K = 3:  a=w9,  b=w10, c=w11, d=w4,  e=w5,  f=w6,  g=w7,  h=w8
// K = 4:  a=w8,  b=w9,  c=w10, d=w11, e=w4,  f=w5,  g=w6,  h=w7
// K = 5:  a=w7,  b=w8,  c=w9,  d=w10, e=w11, f=w4,  g=w5,  h=w6
// K = 6:  a=w6,  b=w7,  c=w8,  d=w9,  e=w10, f=w11, g=w4,  h=w5
// K = 7:  a=w5,  b=w6,  c=w7,  d=w8,  e=w9,  f=w10, g=w11, h=w4
//
// Each ROUND_SCHED_K macro performs one compression round + one schedule
// step; each ROUND_NOSCHED_K macro performs a compression round only.
// Parameters: WT (slot holding W[t], overwritten with W[t+16]),
//             WT1 (W[t+1], read by sigma0),
//             WT9 (W[t+9], add-in for schedule),
//             WT14 (W[t+14], read by sigma1).
// Scratch: w0 (K/T1), w1 (Sigma1/Maj/T2), w2 (Ch/Sigma0 scratch).

// Compression-only round body, at rotation index i (for D-tail).
// Uses state-register slot assignments _a .. _h. Scratch: w0, w1, w2.
#define ROUND_NOSCHED_BODY(_a, _b, _c, _d, _e, _f, _g, _h, WT)    \
        ldr     w0, [x3], #4                                    ;\
        ror     w1, _e, #6                                      ;\
        eor     w1, w1, _e, ror #11                             ;\
        eor     w1, w1, _e, ror #25                             ;\
        eor     w2, _f, _g                                      ;\
        and     w2, w2, _e                                      ;\
        eor     w2, w2, _g                                      ;\
        add     w0, w0, WT                                      ;\
        add     w0, w2, w0                                      ;\
        add     w0, w1, w0                                      ;\
        add     w0, _h, w0                                      ;\
        eor     w1, _b, _c                                      ;\
        and     w1, w1, _a                                      ;\
        and     w2, _b, _c                                      ;\
        eor     w1, w1, w2                                      ;\
        ror     w2, _a, #2                                      ;\
        eor     w2, w2, _a, ror #13                             ;\
        eor     w2, w2, _a, ror #22                             ;\
        add     w1, w1, w2                                      ;\
        add     _d, _d, w0                                      ;\
        add     _h, w0, w1

// Fused compression + schedule step. The schedule arithmetic only reads
// the schedule slots (WT, WT1, WT9, WT14) and writes WT (which at this
// point has already been consumed as the compression's K+W input into
// w0, so WT is dead until the three add-back instructions below write
// the new value W[t+16]). The schedule's ror/eor chain is therefore
// independent of the Maj/Sigma0 side of the compression body and can
// run in parallel on a wide OoO backend.
//
// Scheduling policy (for Neoverse-V1 / Graviton3):
//   * We issue the compression's T1 chain first (through `add w0, _h, w0`).
//   * At that point new_e's final add_d, new_a's final add_h both need
//     the T2 computation (Maj + Sigma0), which reads only _a, _b, _c.
//     The schedule's sigma0/sigma1 computation reads only WT1, WT14.
//     These two groups are independent, so we interleave them to keep
//     the ALU issue queues full.
#define ROUND_SCHED_BODY(_a, _b, _c, _d, _e, _f, _g, _h, WT, WT1, WT9, WT14) \
        ldr     w0, [x3], #4                                    ;\
        ror     w1, _e, #6                                      ;\
        eor     w1, w1, _e, ror #11                             ;\
        eor     w1, w1, _e, ror #25                             ;\
        eor     w2, _f, _g                                      ;\
        and     w2, w2, _e                                      ;\
        eor     w2, w2, _g                                      ;\
        add     w0, w0, WT                                      ;\
        add     w0, w2, w0                                      ;\
        add     w0, w1, w0                                      ;\
        add     w0, _h, w0                                      ;\
        add     _d, _d, w0                                      ;\
        ror     w1, WT1, #7                                     ;\
        eor     w1, w1, WT1, ror #18                            ;\
        eor     w1, w1, WT1, lsr #3                             ;\
        ror     w2, WT14, #17                                   ;\
        eor     w2, w2, WT14, ror #19                           ;\
        eor     w2, w2, WT14, lsr #10                           ;\
        add     WT, WT, w1                                      ;\
        add     WT, WT, WT9                                     ;\
        add     WT, WT, w2                                      ;\
        eor     w1, _b, _c                                      ;\
        and     w1, w1, _a                                      ;\
        and     w2, _b, _c                                      ;\
        eor     w1, w1, w2                                      ;\
        ror     w2, _a, #2                                      ;\
        eor     w2, w2, _a, ror #13                             ;\
        eor     w2, w2, _a, ror #22                             ;\
        add     w1, w1, w2                                      ;\
        add     _h, w0, w1

// ROUND_SCHED_K<i>: compression + schedule, at rotation index i.
#define ROUND_SCHED_K0(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w4,  w5,  w6,  w7,  w8,  w9,  w10, w11, WT, WT1, WT9, WT14)
#define ROUND_SCHED_K1(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w11, w4,  w5,  w6,  w7,  w8,  w9,  w10, WT, WT1, WT9, WT14)
#define ROUND_SCHED_K2(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w10, w11, w4,  w5,  w6,  w7,  w8,  w9,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K3(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w9,  w10, w11, w4,  w5,  w6,  w7,  w8,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K4(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w8,  w9,  w10, w11, w4,  w5,  w6,  w7,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K5(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w7,  w8,  w9,  w10, w11, w4,  w5,  w6,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K6(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w6,  w7,  w8,  w9,  w10, w11, w4,  w5,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K7(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(w5,  w6,  w7,  w8,  w9,  w10, w11, w4,  WT, WT1, WT9, WT14)

// ROUND_NOSCHED_K<i>: round body only, at rotation index i (for D-tail).
#define ROUND_NOSCHED_K0(WT) ROUND_NOSCHED_BODY(w4,  w5,  w6,  w7,  w8,  w9,  w10, w11, WT)
#define ROUND_NOSCHED_K1(WT) ROUND_NOSCHED_BODY(w11, w4,  w5,  w6,  w7,  w8,  w9,  w10, WT)
#define ROUND_NOSCHED_K2(WT) ROUND_NOSCHED_BODY(w10, w11, w4,  w5,  w6,  w7,  w8,  w9,  WT)
#define ROUND_NOSCHED_K3(WT) ROUND_NOSCHED_BODY(w9,  w10, w11, w4,  w5,  w6,  w7,  w8,  WT)
#define ROUND_NOSCHED_K4(WT) ROUND_NOSCHED_BODY(w8,  w9,  w10, w11, w4,  w5,  w6,  w7,  WT)
#define ROUND_NOSCHED_K5(WT) ROUND_NOSCHED_BODY(w7,  w8,  w9,  w10, w11, w4,  w5,  w6,  WT)
#define ROUND_NOSCHED_K6(WT) ROUND_NOSCHED_BODY(w6,  w7,  w8,  w9,  w10, w11, w4,  w5,  WT)
#define ROUND_NOSCHED_K7(WT) ROUND_NOSCHED_BODY(w5,  w6,  w7,  w8,  w9,  w10, w11, w4,  WT)

sha256_block_data_order_nohw6:
        // === Prologue: allocate frame, save callee-saved registers ===
        sub     sp, sp, #112
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        stp     x29, x30, [sp, #80]
        mov     x29, x0                 // x29 = state pointer (stable across body)

.Lblock_loop6:
        // === Phase A: load 16 big-endian words from [x1] into slot regs ===
        //   slot[0..15] = [w19,w20,w21,w22,w23,w24,w25,w26,
        //                  w27,w28,w12,w13,w14,w15,w16,w17]
        ldr     w19, [x1]
        rev     w19, w19
        ldr     w20, [x1, #4]
        rev     w20, w20
        ldr     w21, [x1, #8]
        rev     w21, w21
        ldr     w22, [x1, #12]
        rev     w22, w22
        ldr     w23, [x1, #16]
        rev     w23, w23
        ldr     w24, [x1, #20]
        rev     w24, w24
        ldr     w25, [x1, #24]
        rev     w25, w25
        ldr     w26, [x1, #28]
        rev     w26, w26
        ldr     w27, [x1, #32]
        rev     w27, w27
        ldr     w28, [x1, #36]
        rev     w28, w28
        ldr     w12, [x1, #40]
        rev     w12, w12
        ldr     w13, [x1, #44]
        rev     w13, w13
        ldr     w14, [x1, #48]
        rev     w14, w14
        ldr     w15, [x1, #52]
        rev     w15, w15
        ldr     w16, [x1, #56]
        rev     w16, w16
        ldr     w17, [x1, #60]
        rev     w17, w17

        // === Phase C: load initial state from [x29] into w4..w11 ===
        ldr     w4,  [x29]
        ldr     w5,  [x29, #4]
        ldr     w6,  [x29, #8]
        ldr     w7,  [x29, #12]
        ldr     w8,  [x29, #16]
        ldr     w9,  [x29, #20]
        ldr     w10, [x29, #24]
        ldr     w11, [x29, #28]

        // === Spill x1 (data) and x2 (counter) so w0,w1,w2 are scratch ===
        stp     x1, x2, [sp, #96]

        // === Fused periods: three iterations of 16 rounds (rounds 0..47) ===
        // State at every period entry is canonical (16 mod 8 = 0).
        mov     x30, #3
.Lperiod_loop6:
        ROUND_SCHED_K0(w19, w20, w28, w16)      // k =  0
        ROUND_SCHED_K1(w20, w21, w12, w17)      // k =  1
        ROUND_SCHED_K2(w21, w22, w13, w19)      // k =  2
        ROUND_SCHED_K3(w22, w23, w14, w20)      // k =  3
        ROUND_SCHED_K4(w23, w24, w15, w21)      // k =  4
        ROUND_SCHED_K5(w24, w25, w16, w22)      // k =  5
        ROUND_SCHED_K6(w25, w26, w17, w23)      // k =  6
        ROUND_SCHED_K7(w26, w27, w19, w24)      // k =  7
        ROUND_SCHED_K0(w27, w28, w20, w25)      // k =  8
        ROUND_SCHED_K1(w28, w12, w21, w26)      // k =  9
        ROUND_SCHED_K2(w12, w13, w22, w27)      // k = 10
        ROUND_SCHED_K3(w13, w14, w23, w28)      // k = 11
        ROUND_SCHED_K4(w14, w15, w24, w12)      // k = 12
        ROUND_SCHED_K5(w15, w16, w25, w13)      // k = 13
        ROUND_SCHED_K6(w16, w17, w26, w14)      // k = 14
        ROUND_SCHED_K7(w17, w19, w27, w15)      // k = 15
        sub     x30, x30, #1
        cbnz    x30, .Lperiod_loop6

        // === D-tail: 16 compression-only rounds (rounds 48..63) ===
        // Enters with state canonical (48 mod 8 = 0).
        ROUND_NOSCHED_K0(w19)
        ROUND_NOSCHED_K1(w20)
        ROUND_NOSCHED_K2(w21)
        ROUND_NOSCHED_K3(w22)
        ROUND_NOSCHED_K4(w23)
        ROUND_NOSCHED_K5(w24)
        ROUND_NOSCHED_K6(w25)
        ROUND_NOSCHED_K7(w26)
        ROUND_NOSCHED_K0(w27)
        ROUND_NOSCHED_K1(w28)
        ROUND_NOSCHED_K2(w12)
        ROUND_NOSCHED_K3(w13)
        ROUND_NOSCHED_K4(w14)
        ROUND_NOSCHED_K5(w15)
        ROUND_NOSCHED_K6(w16)
        ROUND_NOSCHED_K7(w17)
        // After round 63 state is canonical again (64 mod 8 = 0).

        // === Phase E: add-back initial state from [x29] ===
        ldr     w0, [x29]
        add     w4, w4, w0
        ldr     w0, [x29, #4]
        add     w5, w5, w0
        ldr     w0, [x29, #8]
        add     w6, w6, w0
        ldr     w0, [x29, #12]
        add     w7, w7, w0
        ldr     w0, [x29, #16]
        add     w8, w8, w0
        ldr     w0, [x29, #20]
        add     w9, w9, w0
        ldr     w0, [x29, #24]
        add     w10, w10, w0
        ldr     w0, [x29, #28]
        add     w11, w11, w0

        // === Phase F: store updated state back to [x29] ===
        str     w4,  [x29]
        str     w5,  [x29, #4]
        str     w6,  [x29, #8]
        str     w7,  [x29, #12]
        str     w8,  [x29, #16]
        str     w9,  [x29, #20]
        str     w10, [x29, #24]
        str     w11, [x29, #28]

        // === Block-loop post-amble ===
        ldp     x1, x2, [sp, #96]
        add     x1, x1, #64
        sub     x2, x2, #1
        sub     x3, x3, #256                    // reset K pointer
        cbnz    x2, .Lblock_loop6

        // === Epilogue: restore x0, callee-saved regs, deallocate frame ===
        mov     x0, x29                         // restore caller's state ptr
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldp     x29, x30, [sp, #80]
        add     sp, sp, #112
        ret
