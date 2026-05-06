// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-512 multi-block compression using scalar instructions only
// (nohw3 = nohw2 + cyclic state-register naming to eliminate 6 MOVs/round).
//
// Optimisation relative to sha512_block_data_order_nohw2:
//   * Cyclic state-register naming. a..h live in a rotating set of eight
//     x-registers. At round t, logical state position j (0..7 <=> a..h) is
//     held in physical register x[4 + ((j - t) mod 8)]. The only writes
//     per round are new_e (into the slot that held d) and new_a (into the
//     slot that held h). This removes the 6 state-rotation MOVs per round
//     (480 per block) present in nohw2.
//   * Because the rotation cycle has period 8 and each period of the
//     schedule loop is 16 rounds, state returns to canonical x4..x11 at
//     every period boundary (0, 16, 32, 48, 64) and after round 80. The
//     proof invariant at those boundaries therefore matches nohw2's.
//   * Schedule window layout, period structure (4 fused iterations then a
//     16-round D-tail), K-pointer handling, and frame size are unchanged
//     from nohw2.
//   * Round bodies interleave the T1 chain / T2 chain / schedule chain to
//     expose more ILP to wide OoO backends (mirrors sha256 nohw6).
//
// Input:
//   X0 = pointer to 8-word state (big-endian 64-bit lanes, in memory order)
//   X1 = pointer to message data (num_blocks * 128 bytes of big-endian words)
//   X2 = num_blocks (64-bit count; caller must ensure >= 1)
//   X3 = pointer to SHA-512 round constant table K[0..79]
// Output:
//   (memory at X0) = sha512_hash_blocks num_blocks blocks [a,b,c,d,e,f,g,h]
// Stack frame: 112 bytes.
//   [sp +   0 .. +  95]: saved x19..x30 (callee-saved frame)
//   [sp +  96 .. + 111]: per-block spill of x1 (data ptr) and x2 (counter)
// Preserves: X0, X3, X19..X28, X29, X30, SP.

        .text
        .globl  sha512_block_data_order_nohw3

// State register assignment as a function of K = t mod 8.
// K = 0:  a=x4,  b=x5,  c=x6,  d=x7,  e=x8,  f=x9,  g=x10, h=x11
// K = 1:  a=x11, b=x4,  c=x5,  d=x6,  e=x7,  f=x8,  g=x9,  h=x10
// K = 2:  a=x10, b=x11, c=x4,  d=x5,  e=x6,  f=x7,  g=x8,  h=x9
// K = 3:  a=x9,  b=x10, c=x11, d=x4,  e=x5,  f=x6,  g=x7,  h=x8
// K = 4:  a=x8,  b=x9,  c=x10, d=x11, e=x4,  f=x5,  g=x6,  h=x7
// K = 5:  a=x7,  b=x8,  c=x9,  d=x10, e=x11, f=x4,  g=x5,  h=x6
// K = 6:  a=x6,  b=x7,  c=x8,  d=x9,  e=x10, f=x11, g=x4,  h=x5
// K = 7:  a=x5,  b=x6,  c=x7,  d=x8,  e=x9,  f=x10, g=x11, h=x4
//
// Rotations: Sigma1 14/18/41, Sigma0 28/34/39, sigma0 1/8/shr7,
//            sigma1 19/61/shr6 (FIPS 180-4 Section 4.1.3).

// Compression-only round body, at rotation index i (for D-tail).
// Uses state-register slot assignments _a .. _h. Scratch: x0, x1, x2.
#define ROUND_NOSCHED_BODY(_a, _b, _c, _d, _e, _f, _g, _h, WT)    \
        ldr     x0, [x3], #8                                    ;\
        ror     x1, _e, #14                                     ;\
        eor     x1, x1, _e, ror #18                             ;\
        eor     x1, x1, _e, ror #41                             ;\
        eor     x2, _f, _g                                      ;\
        and     x2, x2, _e                                      ;\
        eor     x2, x2, _g                                      ;\
        add     x0, x0, WT                                      ;\
        add     x0, x2, x0                                      ;\
        add     x0, x1, x0                                      ;\
        add     x0, _h, x0                                      ;\
        eor     x1, _b, _c                                      ;\
        and     x1, x1, _a                                      ;\
        and     x2, _b, _c                                      ;\
        eor     x1, x1, x2                                      ;\
        ror     x2, _a, #28                                     ;\
        eor     x2, x2, _a, ror #34                             ;\
        eor     x2, x2, _a, ror #39                             ;\
        add     x1, x1, x2                                      ;\
        add     _d, _d, x0                                      ;\
        add     _h, x0, x1

// Fused compression + schedule step, interleaved for ILP.
#define ROUND_SCHED_BODY(_a, _b, _c, _d, _e, _f, _g, _h, WT, WT1, WT9, WT14) \
        ldr     x0, [x3], #8                                    ;\
        ror     x1, _e, #14                                     ;\
        eor     x1, x1, _e, ror #18                             ;\
        eor     x1, x1, _e, ror #41                             ;\
        eor     x2, _f, _g                                      ;\
        and     x2, x2, _e                                      ;\
        eor     x2, x2, _g                                      ;\
        add     x0, x0, WT                                      ;\
        add     x0, x2, x0                                      ;\
        add     x0, x1, x0                                      ;\
        add     x0, _h, x0                                      ;\
        add     _d, _d, x0                                      ;\
        ror     x1, WT1, #1                                     ;\
        eor     x1, x1, WT1, ror #8                             ;\
        eor     x1, x1, WT1, lsr #7                             ;\
        ror     x2, WT14, #19                                   ;\
        eor     x2, x2, WT14, ror #61                           ;\
        eor     x2, x2, WT14, lsr #6                            ;\
        add     WT, WT, x1                                      ;\
        add     WT, WT, WT9                                     ;\
        add     WT, WT, x2                                      ;\
        eor     x1, _b, _c                                      ;\
        and     x1, x1, _a                                      ;\
        and     x2, _b, _c                                      ;\
        eor     x1, x1, x2                                      ;\
        ror     x2, _a, #28                                     ;\
        eor     x2, x2, _a, ror #34                             ;\
        eor     x2, x2, _a, ror #39                             ;\
        add     x1, x1, x2                                      ;\
        add     _h, x0, x1

// ROUND_SCHED_K<i>: compression + schedule, at rotation index i.
#define ROUND_SCHED_K0(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x4,  x5,  x6,  x7,  x8,  x9,  x10, x11, WT, WT1, WT9, WT14)
#define ROUND_SCHED_K1(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x11, x4,  x5,  x6,  x7,  x8,  x9,  x10, WT, WT1, WT9, WT14)
#define ROUND_SCHED_K2(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x10, x11, x4,  x5,  x6,  x7,  x8,  x9,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K3(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x9,  x10, x11, x4,  x5,  x6,  x7,  x8,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K4(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x8,  x9,  x10, x11, x4,  x5,  x6,  x7,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K5(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x7,  x8,  x9,  x10, x11, x4,  x5,  x6,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K6(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x6,  x7,  x8,  x9,  x10, x11, x4,  x5,  WT, WT1, WT9, WT14)
#define ROUND_SCHED_K7(WT, WT1, WT9, WT14)                        \
        ROUND_SCHED_BODY(x5,  x6,  x7,  x8,  x9,  x10, x11, x4,  WT, WT1, WT9, WT14)

// ROUND_NOSCHED_K<i>: round body only, at rotation index i (for D-tail).
#define ROUND_NOSCHED_K0(WT) ROUND_NOSCHED_BODY(x4,  x5,  x6,  x7,  x8,  x9,  x10, x11, WT)
#define ROUND_NOSCHED_K1(WT) ROUND_NOSCHED_BODY(x11, x4,  x5,  x6,  x7,  x8,  x9,  x10, WT)
#define ROUND_NOSCHED_K2(WT) ROUND_NOSCHED_BODY(x10, x11, x4,  x5,  x6,  x7,  x8,  x9,  WT)
#define ROUND_NOSCHED_K3(WT) ROUND_NOSCHED_BODY(x9,  x10, x11, x4,  x5,  x6,  x7,  x8,  WT)
#define ROUND_NOSCHED_K4(WT) ROUND_NOSCHED_BODY(x8,  x9,  x10, x11, x4,  x5,  x6,  x7,  WT)
#define ROUND_NOSCHED_K5(WT) ROUND_NOSCHED_BODY(x7,  x8,  x9,  x10, x11, x4,  x5,  x6,  WT)
#define ROUND_NOSCHED_K6(WT) ROUND_NOSCHED_BODY(x6,  x7,  x8,  x9,  x10, x11, x4,  x5,  WT)
#define ROUND_NOSCHED_K7(WT) ROUND_NOSCHED_BODY(x5,  x6,  x7,  x8,  x9,  x10, x11, x4,  WT)

sha512_block_data_order_nohw3:
        // === Prologue: allocate frame, save callee-saved registers ===
        sub     sp, sp, #112
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        stp     x29, x30, [sp, #80]
        mov     x29, x0                 // x29 = state pointer (stable across body)

.Lblock_loop3:
        // === Phase A: load 16 big-endian 64-bit words from [x1] into slots ===
        //   slot[0..15] = [x19,x20,x21,x22,x23,x24,x25,x26,
        //                  x27,x28,x12,x13,x14,x15,x16,x17]
        ldr     x19, [x1]
        rev     x19, x19
        ldr     x20, [x1, #8]
        rev     x20, x20
        ldr     x21, [x1, #16]
        rev     x21, x21
        ldr     x22, [x1, #24]
        rev     x22, x22
        ldr     x23, [x1, #32]
        rev     x23, x23
        ldr     x24, [x1, #40]
        rev     x24, x24
        ldr     x25, [x1, #48]
        rev     x25, x25
        ldr     x26, [x1, #56]
        rev     x26, x26
        ldr     x27, [x1, #64]
        rev     x27, x27
        ldr     x28, [x1, #72]
        rev     x28, x28
        ldr     x12, [x1, #80]
        rev     x12, x12
        ldr     x13, [x1, #88]
        rev     x13, x13
        ldr     x14, [x1, #96]
        rev     x14, x14
        ldr     x15, [x1, #104]
        rev     x15, x15
        ldr     x16, [x1, #112]
        rev     x16, x16
        ldr     x17, [x1, #120]
        rev     x17, x17

        // === Phase C: load initial state from [x29] into x4..x11 ===
        ldr     x4,  [x29]
        ldr     x5,  [x29, #8]
        ldr     x6,  [x29, #16]
        ldr     x7,  [x29, #24]
        ldr     x8,  [x29, #32]
        ldr     x9,  [x29, #40]
        ldr     x10, [x29, #48]
        ldr     x11, [x29, #56]

        // === Spill x1 (data) and x2 (counter) so x0,x1,x2 are scratch ===
        stp     x1, x2, [sp, #96]

        // === Fused periods: four iterations of 16 rounds (rounds 0..63) ===
        // State at every period entry is canonical (16 mod 8 = 0).
        mov     x30, #4
.Lperiod_loop3:
        ROUND_SCHED_K0(x19, x20, x28, x16)      // k =  0
        ROUND_SCHED_K1(x20, x21, x12, x17)      // k =  1
        ROUND_SCHED_K2(x21, x22, x13, x19)      // k =  2
        ROUND_SCHED_K3(x22, x23, x14, x20)      // k =  3
        ROUND_SCHED_K4(x23, x24, x15, x21)      // k =  4
        ROUND_SCHED_K5(x24, x25, x16, x22)      // k =  5
        ROUND_SCHED_K6(x25, x26, x17, x23)      // k =  6
        ROUND_SCHED_K7(x26, x27, x19, x24)      // k =  7
        ROUND_SCHED_K0(x27, x28, x20, x25)      // k =  8
        ROUND_SCHED_K1(x28, x12, x21, x26)      // k =  9
        ROUND_SCHED_K2(x12, x13, x22, x27)      // k = 10
        ROUND_SCHED_K3(x13, x14, x23, x28)      // k = 11
        ROUND_SCHED_K4(x14, x15, x24, x12)      // k = 12
        ROUND_SCHED_K5(x15, x16, x25, x13)      // k = 13
        ROUND_SCHED_K6(x16, x17, x26, x14)      // k = 14
        ROUND_SCHED_K7(x17, x19, x27, x15)      // k = 15
        sub     x30, x30, #1
        cbnz    x30, .Lperiod_loop3

        // === D-tail: 16 compression-only rounds (rounds 64..79) ===
        // Enters with state canonical (64 mod 8 = 0).
        ROUND_NOSCHED_K0(x19)
        ROUND_NOSCHED_K1(x20)
        ROUND_NOSCHED_K2(x21)
        ROUND_NOSCHED_K3(x22)
        ROUND_NOSCHED_K4(x23)
        ROUND_NOSCHED_K5(x24)
        ROUND_NOSCHED_K6(x25)
        ROUND_NOSCHED_K7(x26)
        ROUND_NOSCHED_K0(x27)
        ROUND_NOSCHED_K1(x28)
        ROUND_NOSCHED_K2(x12)
        ROUND_NOSCHED_K3(x13)
        ROUND_NOSCHED_K4(x14)
        ROUND_NOSCHED_K5(x15)
        ROUND_NOSCHED_K6(x16)
        ROUND_NOSCHED_K7(x17)
        // After round 79 state is canonical again (80 mod 8 = 0).

        // === Phase E: add-back initial state from [x29] ===
        ldr     x0, [x29]
        add     x4, x4, x0
        ldr     x0, [x29, #8]
        add     x5, x5, x0
        ldr     x0, [x29, #16]
        add     x6, x6, x0
        ldr     x0, [x29, #24]
        add     x7, x7, x0
        ldr     x0, [x29, #32]
        add     x8, x8, x0
        ldr     x0, [x29, #40]
        add     x9, x9, x0
        ldr     x0, [x29, #48]
        add     x10, x10, x0
        ldr     x0, [x29, #56]
        add     x11, x11, x0

        // === Phase F: store updated state back to [x29] ===
        str     x4,  [x29]
        str     x5,  [x29, #8]
        str     x6,  [x29, #16]
        str     x7,  [x29, #24]
        str     x8,  [x29, #32]
        str     x9,  [x29, #40]
        str     x10, [x29, #48]
        str     x11, [x29, #56]

        // === Block-loop post-amble ===
        ldp     x1, x2, [sp, #96]
        add     x1, x1, #128
        sub     x2, x2, #1
        sub     x3, x3, #640                    // reset K pointer
        cbnz    x2, .Lblock_loop3

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
