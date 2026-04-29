// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-256 multi-block compression using scalar instructions only
// (optimised variant, same ABI and memory layout as
// sha256_block_data_order_nohw).
//
// Optimisations relative to sha256_block_data_order_nohw:
//   * Shifted-register EOR fusion for sigma0/sigma1/Sigma0/Sigma1:
//       ror Wt, Wn, #r1 ; eor Wd, Wd, Wt   ->   eor Wd, Wd, Wn, ror #r1
//     saves two instructions per sigma invocation.
//   * Maj(a,b,c) computed as (a AND b) XOR ((a XOR b) AND c)
//     (one fewer instruction than the classical 5-instruction form).
//
// Per block this saves
//     6 instructions * 64 rounds       = 384 instructions in the
//                                         compression loop, and
//     4 instructions * 48 schedule     = 192 instructions in the
//                                         message-schedule extension,
// while the phase structure, register allocation, stack frame and ABI
// are unchanged.
//
// Input:
//   X0 = pointer to 8-word state (big-endian 32-bit lanes, in memory order)
//   X1 = pointer to message data (num_blocks * 64 bytes of big-endian words)
//   X2 = num_blocks (64-bit count; caller must ensure >= 1)
//   X3 = pointer to SHA-256 round constant table K[0..63]
// Output:
//   (memory at X0) = sha256_hash_blocks num_blocks blocks [a,b,c,d,e,f,g,h]
// Stack frame: 320 bytes.
//   [sp + 0 .. sp + 255]  : 64-word message schedule buffer (scratch)
//   [sp + 256 .. sp + 319]: saved X19..X26 (callee-saved)
// Preserves: X0, X3, X19..X26 (saved/restored), SP (restored).

        .text
        .globl  sha256_block_data_order_nohw2

sha256_block_data_order_nohw2:
        // === Prologue: allocate frame, save callee-saved registers ===
        sub     sp, sp, #320
        stp     x19, x20, [sp, #256]
        stp     x21, x22, [sp, #272]
        stp     x23, x24, [sp, #288]
        stp     x25, x26, [sp, #304]

.Lblock_loop2:
        // === Phase A: for t = 0..15, load [x1 + 4*t], REV, store [sp + 4*t] ===
        mov     x17, #0
.LloadA2:
        ldr     w12, [x1, x17, lsl #2]
        rev     w12, w12
        str     w12, [sp, x17, lsl #2]
        add     x17, x17, #1
        cmp     x17, #16
        b.ne    .LloadA2

        // === Phase B: extend W[16..63] on stack. Base X4 = SP + 4*i. ===
        mov     x4, sp
        mov     x17, #0
.LextB2:
        ldr     w12, [x4]                       // W[i]
        ldr     w13, [x4, #4]                   // W[i+1]
        ldr     w14, [x4, #36]                  // W[i+9]
        ldr     w15, [x4, #56]                  // W[i+14]

        // sigma0(W[i+1]) = ror(w13,7) XOR ror(w13,18) XOR (w13 >> 3)
        ror     w16, w13, #7
        eor     w16, w16, w13, ror #18
        eor     w16, w16, w13, lsr #3           // w16 = sigma0

        // sigma1(W[i+14]) = ror(w15,17) XOR ror(w15,19) XOR (w15 >> 10)
        ror     w13, w15, #17
        eor     w13, w13, w15, ror #19
        eor     w13, w13, w15, lsr #10          // w13 = sigma1

        // accumulate W[i+16] = W[i] + sigma0 + W[i+9] + sigma1
        add     w12, w12, w16
        add     w12, w12, w14
        add     w12, w12, w13
        str     w12, [x4, #64]

        add     x4, x4, #4
        add     x17, x17, #1
        cmp     x17, #48
        b.ne    .LextB2

        // === Phase C: load initial state into W4-W11 and save to W19-W26 ===
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

        // === Phase D: 64-round compression loop (W from SP, K from X3) ===
        mov     w17, #0
.LloopD2:
        ldr     w15, [x3, x17, lsl #2]          // K_t
        ldr     w16, [sp, x17, lsl #2]          // W_t

        // Sigma1(e) = ror(e,6) XOR ror(e,11) XOR ror(e,25)
        ror     w12, w8, #6
        eor     w12, w12, w8, ror #11
        eor     w12, w12, w8, ror #25           // w12 = Sigma1(e)

        // Ch(e,f,g) = (e AND f) XOR (g AND NOT e)
        and     w13, w8, w9
        bic     w14, w10, w8
        eor     w13, w13, w14                   // w13 = Ch(e,f,g)

        // K + W
        add     w15, w15, w16                   // w15 = K_t + W_t

        // T1 = h + (Sigma1 + (Ch + (K + W)))
        add     w15, w13, w15                   // Ch + (K+W)
        add     w15, w12, w15                   // Sigma1 + (Ch + (K+W))
        add     w12, w11, w15                   // w12 = T1

        // Sigma0(a) = ror(a,2) XOR ror(a,13) XOR ror(a,22)
        ror     w13, w4, #2
        eor     w13, w13, w4, ror #13
        eor     w13, w13, w4, ror #22           // w13 = Sigma0(a)

        // Maj(a,b,c) = (a AND b) XOR ((a XOR b) AND c)
        and     w15, w4, w5                     // a AND b
        eor     w14, w4, w5                     // a XOR b
        and     w14, w14, w6                    // (a XOR b) AND c
        eor     w14, w15, w14                   // w14 = Maj

        // T2 = Sigma0(a) + Maj(a,b,c)
        add     w13, w13, w14                   // w13 = T2

        // state rotation
        mov     w11, w10
        mov     w10, w9
        mov     w9, w8
        add     w8, w7, w12                     // e <- d + T1
        mov     w7, w6
        mov     w6, w5
        mov     w5, w4
        add     w4, w12, w13                    // a <- T1 + T2

        add     x17, x17, #1
        cmp     x17, #64
        b.ne    .LloopD2

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
        cbnz    x2, .Lblock_loop2

        // === Epilogue: restore callee-saved registers, deallocate frame ===
        ldp     x19, x20, [sp, #256]
        ldp     x21, x22, [sp, #272]
        ldp     x23, x24, [sp, #288]
        ldp     x25, x26, [sp, #304]
        add     sp, sp, #320
        ret
