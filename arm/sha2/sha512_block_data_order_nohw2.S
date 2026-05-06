// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-512 multi-block compression using scalar instructions only
// (nohw2 = sha256 nohw5 transplanted to 64-bit / 80 rounds).
//
// Optimisations relative to sha512_block_data_order_nohw:
//   * The 16-word sliding message-schedule window lives in 16 named
//     x-registers (x12..x17, x19..x28) instead of a 640-byte stack
//     scratch. Each fused compression round reads W[t] directly from
//     its slot register and writes W[t+16] back to the same slot once
//     W[t] is consumed. Eliminates 2 LDR + 1 STR per fused round plus
//     the entire 640-byte scratch area.
//   * Four "fused" periods (rounds 0..63) run as a counted loop of
//     four iterations, each iteration expanding 16 round bodies inline
//     so the slot register names rotate with the round index within the
//     period. The final 16 rounds (64..79) run as a compression-only
//     D-tail.
//   * The K round-constant table is walked via post-incremented LDR
//     (`ldr x0, [x3], #8`) instead of indexed access, saving the
//     per-round index shift and freeing x17 for use as a schedule slot.
//     x3 is restored at block-end via `sub x3, x3, #640`.
//   * x29 (FP) holds the state pointer across the inner body so that x0
//     is free as round-body scratch; x30 (LR) drives the period
//     counter. Both are saved/restored across the call boundary.
//   * Merged rotate-XOR encodings (`eor xd, xn, xm, ror #k`) replace
//     separate ror+eor pairs throughout.
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
        .globl  sha512_block_data_order_nohw2

// Compression round + schedule step (used inside the fused period loop).
//   WT   = slot holding W[t]          (reg that will receive W[t+16])
//   WT1  = slot holding W[t+1]        (source for sigma0)
//   WT9  = slot holding W[t+9]        (add-in for schedule)
//   WT14 = slot holding W[t+14]       (source for sigma1)
// State: a..h = x4..x11. Scratch: x0 (K/T1), x1 (Sigma1/Maj/T2), x2 (Ch/Sigma0).
// Rotations: Sigma1 14/18/41, Sigma0 28/34/39, sigma0 1/8/shr7, sigma1 19/61/shr6.
#define ROUND_SCHED(WT, WT1, WT9, WT14)                           \
        ldr     x0, [x3], #8                                    ;\
        ror     x1, x8, #14                                     ;\
        eor     x1, x1, x8, ror #18                             ;\
        eor     x1, x1, x8, ror #41                             ;\
        eor     x2, x9, x10                                     ;\
        and     x2, x2, x8                                      ;\
        eor     x2, x2, x10                                     ;\
        add     x0, x0, WT                                      ;\
        add     x0, x2, x0                                      ;\
        add     x0, x1, x0                                      ;\
        add     x0, x11, x0                                     ;\
        eor     x1, x5, x6                                      ;\
        and     x1, x1, x4                                      ;\
        and     x2, x5, x6                                      ;\
        eor     x1, x1, x2                                      ;\
        ror     x2, x4, #28                                     ;\
        eor     x2, x2, x4, ror #34                             ;\
        eor     x2, x2, x4, ror #39                             ;\
        add     x1, x1, x2                                      ;\
        mov     x11, x10                                        ;\
        mov     x10, x9                                         ;\
        mov     x9, x8                                          ;\
        add     x8, x7, x0                                      ;\
        mov     x7, x6                                          ;\
        mov     x6, x5                                          ;\
        mov     x5, x4                                          ;\
        add     x4, x0, x1                                      ;\
        ror     x0, WT1, #1                                     ;\
        eor     x0, x0, WT1, ror #8                             ;\
        eor     x0, x0, WT1, lsr #7                             ;\
        ror     x1, WT14, #19                                   ;\
        eor     x1, x1, WT14, ror #61                           ;\
        eor     x1, x1, WT14, lsr #6                            ;\
        add     WT, WT, x0                                      ;\
        add     WT, WT, WT9                                     ;\
        add     WT, WT, x1

// Compression-only round (used in the D-tail loop, rounds 64..79).
#define ROUND_NOSCHED(WT)                                         \
        ldr     x0, [x3], #8                                    ;\
        ror     x1, x8, #14                                     ;\
        eor     x1, x1, x8, ror #18                             ;\
        eor     x1, x1, x8, ror #41                             ;\
        eor     x2, x9, x10                                     ;\
        and     x2, x2, x8                                      ;\
        eor     x2, x2, x10                                     ;\
        add     x0, x0, WT                                      ;\
        add     x0, x2, x0                                      ;\
        add     x0, x1, x0                                      ;\
        add     x0, x11, x0                                     ;\
        eor     x1, x5, x6                                      ;\
        and     x1, x1, x4                                      ;\
        and     x2, x5, x6                                      ;\
        eor     x1, x1, x2                                      ;\
        ror     x2, x4, #28                                     ;\
        eor     x2, x2, x4, ror #34                             ;\
        eor     x2, x2, x4, ror #39                             ;\
        add     x1, x1, x2                                      ;\
        mov     x11, x10                                        ;\
        mov     x10, x9                                         ;\
        mov     x9, x8                                          ;\
        add     x8, x7, x0                                      ;\
        mov     x7, x6                                          ;\
        mov     x6, x5                                          ;\
        mov     x5, x4                                          ;\
        add     x4, x0, x1

sha512_block_data_order_nohw2:
        // === Prologue: allocate frame, save callee-saved registers ===
        sub     sp, sp, #112
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        stp     x29, x30, [sp, #80]
        mov     x29, x0                 // x29 = state pointer (stable across body)

.Lblock_loop2:
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
        mov     x30, #4
.Lperiod_loop2:
        ROUND_SCHED(x19, x20, x28, x16)         // k = 0
        ROUND_SCHED(x20, x21, x12, x17)         // k = 1
        ROUND_SCHED(x21, x22, x13, x19)         // k = 2
        ROUND_SCHED(x22, x23, x14, x20)         // k = 3
        ROUND_SCHED(x23, x24, x15, x21)         // k = 4
        ROUND_SCHED(x24, x25, x16, x22)         // k = 5
        ROUND_SCHED(x25, x26, x17, x23)         // k = 6
        ROUND_SCHED(x26, x27, x19, x24)         // k = 7
        ROUND_SCHED(x27, x28, x20, x25)         // k = 8
        ROUND_SCHED(x28, x12, x21, x26)         // k = 9
        ROUND_SCHED(x12, x13, x22, x27)         // k = 10
        ROUND_SCHED(x13, x14, x23, x28)         // k = 11
        ROUND_SCHED(x14, x15, x24, x12)         // k = 12
        ROUND_SCHED(x15, x16, x25, x13)         // k = 13
        ROUND_SCHED(x16, x17, x26, x14)         // k = 14
        ROUND_SCHED(x17, x19, x27, x15)         // k = 15
        sub     x30, x30, #1
        cbnz    x30, .Lperiod_loop2

        // === D-tail: 16 compression-only rounds (rounds 64..79) ===
        ROUND_NOSCHED(x19)
        ROUND_NOSCHED(x20)
        ROUND_NOSCHED(x21)
        ROUND_NOSCHED(x22)
        ROUND_NOSCHED(x23)
        ROUND_NOSCHED(x24)
        ROUND_NOSCHED(x25)
        ROUND_NOSCHED(x26)
        ROUND_NOSCHED(x27)
        ROUND_NOSCHED(x28)
        ROUND_NOSCHED(x12)
        ROUND_NOSCHED(x13)
        ROUND_NOSCHED(x14)
        ROUND_NOSCHED(x15)
        ROUND_NOSCHED(x16)
        ROUND_NOSCHED(x17)

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
        cbnz    x2, .Lblock_loop2

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
