// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-256 multi-block compression using scalar instructions only
// (nohw4 = nohw2 fusions + message-schedule/compression interleaving;
// same ABI and memory layout as sha256_block_data_order_nohw).
//
// Optimisations relative to sha256_block_data_order_nohw2:
//   * Phase B (message-schedule extension) is fused with the first 48
//     rounds of Phase D (compression). Each fused iteration t in
//     [0, 48) runs compression round t on the scalar state, then
//     extends the schedule by computing W[t+16]. Rounds 48..63 run
//     in a compression-only tail loop identical in shape to the
//     nohw2 body. Interleaving exposes schedule-vs-compression
//     instruction-level parallelism to the out-of-order backend.
//   * Phase C (load initial state) moves ahead of the fused loop so
//     W4..W11 hold scalar state before the first compression round.
//   * X27 is added to the callee-saved set and used as a persistent
//     schedule base register (SP + 4*t), since the fused body
//     requires W16 as compute scratch and so cannot park the base
//     in X16.
//
// Input:
//   X0 = pointer to 8-word state (big-endian 32-bit lanes, in memory order)
//   X1 = pointer to message data (num_blocks * 64 bytes of big-endian words)
//   X2 = num_blocks (64-bit count; caller must ensure >= 1)
//   X3 = pointer to SHA-256 round constant table K[0..63]
// Output:
//   (memory at X0) = sha256_hash_blocks num_blocks blocks [a,b,c,d,e,f,g,h]
// Stack frame: 336 bytes.
//   [sp + 0 .. sp + 255]  : 64-word message schedule buffer (scratch)
//   [sp + 256 .. sp + 319]: saved X19..X26 (callee-saved)
//   [sp + 320 .. sp + 335]: saved X27 + X28 padding (callee-saved)
// Preserves: X0, X3, X19..X27 (saved/restored), SP (restored).

        .text
        .globl  sha256_block_data_order_nohw4

sha256_block_data_order_nohw4:
        // === Prologue: allocate frame, save callee-saved registers ===
        sub     sp, sp, #336
        stp     x19, x20, [sp, #256]
        stp     x21, x22, [sp, #272]
        stp     x23, x24, [sp, #288]
        stp     x25, x26, [sp, #304]
        stp     x27, x28, [sp, #320]

.Lblock_loop4:
        // === Phase A: for t = 0..15, load [x1 + 4*t], REV, store [sp + 4*t] ===
        mov     x17, #0
.LloadA4:
        ldr     w12, [x1, x17, lsl #2]
        rev     w12, w12
        str     w12, [sp, x17, lsl #2]
        add     x17, x17, #1
        cmp     x17, #16
        b.ne    .LloadA4

        // === Phase C: load initial state into W4..W11 and mirror to W19..W26 ===
        ldr     w4,  [x0]
        ldr     w5,  [x0, #4]
        ldr     w6,  [x0, #8]
        ldr     w7,  [x0, #12]
        ldr     w8,  [x0, #16]
        ldr     w9,  [x0, #20]
        ldr     w10, [x0, #24]
        ldr     w11, [x0, #28]
        mov     w19, w4
        mov     w20, w5
        mov     w21, w6
        mov     w22, w7
        mov     w23, w8
        mov     w24, w9
        mov     w25, w10
        mov     w26, w11

        // === Fused Phase B+D loop (t = 0..47): ===
        //   compression round t on scalar state using K[t] and W[t],
        //   then schedule step writing W[t+16] = W[t] + sigma0(W[t+1])
        //                                          + W[t+9] + sigma1(W[t+14]).
        mov     x17, #0
        mov     x27, sp                         // x27 = SP + 4*t (schedule base)
.LfusedBD4:
        // --- Compression round t ---
        ldr     w15, [x3,  x17, lsl #2]         // K_t
        ldr     w16, [x27]                      // W_t  (same as [sp + 4*t])

        ror     w12, w8, #6
        eor     w12, w12, w8, ror #11
        eor     w12, w12, w8, ror #25           // Sigma1(e)

        and     w13, w8, w9
        bic     w14, w10, w8
        eor     w13, w13, w14                   // Ch(e,f,g)

        add     w15, w15, w16                   // K + W_t
        add     w15, w13, w15                   // Ch + (K+W)
        add     w15, w12, w15                   // Sigma1 + (Ch + K+W)
        add     w12, w11, w15                   // T1

        ror     w13, w4, #2
        eor     w13, w13, w4, ror #13
        eor     w13, w13, w4, ror #22           // Sigma0(a)

        and     w15, w4, w5
        eor     w14, w4, w5
        and     w14, w14, w6
        eor     w14, w15, w14                   // Maj(a,b,c)

        add     w13, w13, w14                   // T2

        mov     w11, w10
        mov     w10, w9
        mov     w9, w8
        add     w8, w7, w12                     // e <- d + T1
        mov     w7, w6
        mov     w6, w5
        mov     w5, w4
        add     w4, w12, w13                    // a <- T1 + T2

        // --- Schedule step: W[t+16] = W[t] + sigma0(W[t+1])
        //                                     + W[t+9] + sigma1(W[t+14])
        ldr     w12, [x27]                      // W[t]
        ldr     w13, [x27, #4]                  // W[t+1]
        ldr     w14, [x27, #36]                 // W[t+9]
        ldr     w15, [x27, #56]                 // W[t+14]

        // sigma0(W[t+1]) = ror(w13,7) XOR ror(w13,18) XOR (w13 >> 3)
        ror     w16, w13, #7
        eor     w16, w16, w13, ror #18
        eor     w16, w16, w13, lsr #3           // w16 = sigma0

        // sigma1(W[t+14]) = ror(w15,17) XOR ror(w15,19) XOR (w15 >> 10)
        ror     w13, w15, #17
        eor     w13, w13, w15, ror #19
        eor     w13, w13, w15, lsr #10          // w13 = sigma1

        add     w12, w12, w16
        add     w12, w12, w14
        add     w12, w12, w13
        str     w12, [x27, #64]                 // stack[t+16] = W[t+16]

        add     x27, x27, #4
        add     x17, x17, #1
        cmp     x17, #48
        b.ne    .LfusedBD4

        // === D-tail loop (t = 48..63): compression only, nohw2-shaped body ===
.LDtail4:
        ldr     w15, [x3, x17, lsl #2]          // K_t
        ldr     w16, [sp, x17, lsl #2]          // W_t

        ror     w12, w8, #6
        eor     w12, w12, w8, ror #11
        eor     w12, w12, w8, ror #25           // Sigma1(e)

        and     w13, w8, w9
        bic     w14, w10, w8
        eor     w13, w13, w14                   // Ch(e,f,g)

        add     w15, w15, w16                   // K + W
        add     w15, w13, w15
        add     w15, w12, w15
        add     w12, w11, w15                   // T1

        ror     w13, w4, #2
        eor     w13, w13, w4, ror #13
        eor     w13, w13, w4, ror #22           // Sigma0(a)

        and     w15, w4, w5
        eor     w14, w4, w5
        and     w14, w14, w6
        eor     w14, w15, w14                   // Maj(a,b,c)

        add     w13, w13, w14                   // T2

        mov     w11, w10
        mov     w10, w9
        mov     w9, w8
        add     w8, w7, w12
        mov     w7, w6
        mov     w6, w5
        mov     w5, w4
        add     w4, w12, w13

        add     x17, x17, #1
        cmp     x17, #64
        b.ne    .LDtail4

        // === Phase E: add-back W4..W11 += W19..W26 ===
        add     w4,  w4,  w19
        add     w5,  w5,  w20
        add     w6,  w6,  w21
        add     w7,  w7,  w22
        add     w8,  w8,  w23
        add     w9,  w9,  w24
        add     w10, w10, w25
        add     w11, w11, w26

        // === Phase F: store state back to [X0] ===
        str     w4,  [x0]
        str     w5,  [x0, #4]
        str     w6,  [x0, #8]
        str     w7,  [x0, #12]
        str     w8,  [x0, #16]
        str     w9,  [x0, #20]
        str     w10, [x0, #24]
        str     w11, [x0, #28]

        // === Block-loop post-amble: advance data ptr, decrement counter ===
        add     x1, x1, #64
        sub     x2, x2, #1
        cbnz    x2, .Lblock_loop4

        // === Epilogue: restore callee-saved registers, deallocate frame ===
        ldp     x19, x20, [sp, #256]
        ldp     x21, x22, [sp, #272]
        ldp     x23, x24, [sp, #288]
        ldp     x25, x26, [sp, #304]
        ldp     x27, x28, [sp, #320]
        add     sp, sp, #336
        ret
