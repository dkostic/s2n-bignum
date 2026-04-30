// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-256 multi-block compression using scalar instructions only
// (nohw5 = nohw4 + message-schedule window resident in registers).
//
// Optimisation relative to sha256_block_data_order_nohw4:
//   * The 16-word sliding message-schedule window lives in 16 named
//     registers (w12..w17, w19..w28) instead of the 256-byte stack
//     scratch used by nohw4. Each fused compression round reads W[t]
//     directly from its slot register and writes W[t+16] back to the
//     same slot once W[t] is consumed. This eliminates 2 LDR + 1 STR
//     per fused round and the entire 256-byte scratch area.
//   * The three "fused" periods (rounds 0..47) run as a counted loop
//     of three iterations, each iteration expanding 16 round bodies
//     inline so that the slot register names rotate with the round
//     index within the period. The final 16 rounds (48..63) run as
//     a compression-only D-tail.
//   * The K round-constant table is walked via post-incremented LDR
//     (`ldr w0, [x3], #4`) instead of indexed access, saving the
//     per-round index shift and freeing x17 for use as a schedule
//     slot. x3 is restored at block-end via `sub x3, x3, #256`.
//   * x29 (FP) holds the state pointer across the inner body so that
//     x0 is free as round-body scratch; x30 (LR) drives the period
//     counter. Both are saved/restored across the call boundary.
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
        .globl  sha256_block_data_order_nohw5

// Compression round + schedule step (used inside the fused period loop).
//   WT   = slot holding W[t]          (reg that will receive W[t+16])
//   WT1  = slot holding W[t+1]        (source for sigma0)
//   WT9  = slot holding W[t+9]        (add-in for schedule)
//   WT14 = slot holding W[t+14]       (source for sigma1)
// State: a..h = w4..w11. Scratch: w0 (K/T1), w1 (Sigma1/Maj/T2), w2 (Ch/Sigma0).
#define ROUND_SCHED(WT, WT1, WT9, WT14)                           \
        ldr     w0, [x3], #4                                    ;\
        ror     w1, w8, #6                                      ;\
        eor     w1, w1, w8, ror #11                             ;\
        eor     w1, w1, w8, ror #25                             ;\
        eor     w2, w9, w10                                     ;\
        and     w2, w2, w8                                      ;\
        eor     w2, w2, w10                                     ;\
        add     w0, w0, WT                                      ;\
        add     w0, w2, w0                                      ;\
        add     w0, w1, w0                                      ;\
        add     w0, w11, w0                                     ;\
        eor     w1, w5, w6                                      ;\
        and     w1, w1, w4                                      ;\
        and     w2, w5, w6                                      ;\
        eor     w1, w1, w2                                      ;\
        ror     w2, w4, #2                                      ;\
        eor     w2, w2, w4, ror #13                             ;\
        eor     w2, w2, w4, ror #22                             ;\
        add     w1, w1, w2                                      ;\
        mov     w11, w10                                        ;\
        mov     w10, w9                                         ;\
        mov     w9, w8                                          ;\
        add     w8, w7, w0                                      ;\
        mov     w7, w6                                          ;\
        mov     w6, w5                                          ;\
        mov     w5, w4                                          ;\
        add     w4, w0, w1                                      ;\
        ror     w0, WT1, #7                                     ;\
        eor     w0, w0, WT1, ror #18                            ;\
        eor     w0, w0, WT1, lsr #3                             ;\
        ror     w1, WT14, #17                                   ;\
        eor     w1, w1, WT14, ror #19                           ;\
        eor     w1, w1, WT14, lsr #10                           ;\
        add     WT, WT, w0                                      ;\
        add     WT, WT, WT9                                     ;\
        add     WT, WT, w1

// Compression-only round (used in the D-tail loop, rounds 48..63).
#define ROUND_NOSCHED(WT)                                         \
        ldr     w0, [x3], #4                                    ;\
        ror     w1, w8, #6                                      ;\
        eor     w1, w1, w8, ror #11                             ;\
        eor     w1, w1, w8, ror #25                             ;\
        eor     w2, w9, w10                                     ;\
        and     w2, w2, w8                                      ;\
        eor     w2, w2, w10                                     ;\
        add     w0, w0, WT                                      ;\
        add     w0, w2, w0                                      ;\
        add     w0, w1, w0                                      ;\
        add     w0, w11, w0                                     ;\
        eor     w1, w5, w6                                      ;\
        and     w1, w1, w4                                      ;\
        and     w2, w5, w6                                      ;\
        eor     w1, w1, w2                                      ;\
        ror     w2, w4, #2                                      ;\
        eor     w2, w2, w4, ror #13                             ;\
        eor     w2, w2, w4, ror #22                             ;\
        add     w1, w1, w2                                      ;\
        mov     w11, w10                                        ;\
        mov     w10, w9                                         ;\
        mov     w9, w8                                          ;\
        add     w8, w7, w0                                      ;\
        mov     w7, w6                                          ;\
        mov     w6, w5                                          ;\
        mov     w5, w4                                          ;\
        add     w4, w0, w1

sha256_block_data_order_nohw5:
        // === Prologue: allocate frame, save callee-saved registers ===
        sub     sp, sp, #112
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        stp     x29, x30, [sp, #80]
        mov     x29, x0                 // x29 = state pointer (stable across body)

.Lblock_loop5:
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
        mov     x30, #3
.Lperiod_loop5:
        ROUND_SCHED(w19, w20, w28, w16)         // k = 0
        ROUND_SCHED(w20, w21, w12, w17)         // k = 1
        ROUND_SCHED(w21, w22, w13, w19)         // k = 2
        ROUND_SCHED(w22, w23, w14, w20)         // k = 3
        ROUND_SCHED(w23, w24, w15, w21)         // k = 4
        ROUND_SCHED(w24, w25, w16, w22)         // k = 5
        ROUND_SCHED(w25, w26, w17, w23)         // k = 6
        ROUND_SCHED(w26, w27, w19, w24)         // k = 7
        ROUND_SCHED(w27, w28, w20, w25)         // k = 8
        ROUND_SCHED(w28, w12, w21, w26)         // k = 9
        ROUND_SCHED(w12, w13, w22, w27)         // k = 10
        ROUND_SCHED(w13, w14, w23, w28)         // k = 11
        ROUND_SCHED(w14, w15, w24, w12)         // k = 12
        ROUND_SCHED(w15, w16, w25, w13)         // k = 13
        ROUND_SCHED(w16, w17, w26, w14)         // k = 14
        ROUND_SCHED(w17, w19, w27, w15)         // k = 15
        sub     x30, x30, #1
        cbnz    x30, .Lperiod_loop5

        // === D-tail: 16 compression-only rounds (rounds 48..63) ===
        ROUND_NOSCHED(w19)
        ROUND_NOSCHED(w20)
        ROUND_NOSCHED(w21)
        ROUND_NOSCHED(w22)
        ROUND_NOSCHED(w23)
        ROUND_NOSCHED(w24)
        ROUND_NOSCHED(w25)
        ROUND_NOSCHED(w26)
        ROUND_NOSCHED(w27)
        ROUND_NOSCHED(w28)
        ROUND_NOSCHED(w12)
        ROUND_NOSCHED(w13)
        ROUND_NOSCHED(w14)
        ROUND_NOSCHED(w15)
        ROUND_NOSCHED(w16)
        ROUND_NOSCHED(w17)

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
        cbnz    x2, .Lblock_loop5

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
