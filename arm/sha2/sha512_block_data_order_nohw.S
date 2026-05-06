// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-512 multi-block compression using scalar instructions only.
// Input:
//   X0 = pointer to 8-word state (big-endian 64-bit lanes, in memory order)
//   X1 = pointer to message data (num_blocks * 128 bytes of big-endian words)
//   X2 = num_blocks (64-bit count; caller must ensure >= 1)
//   X3 = pointer to SHA-512 round constant table K[0..79]
// Output:
//   (memory at X0) = sha512_hash_blocks num_blocks blocks [a,b,c,d,e,f,g,h]
// Stack frame: 704 bytes, built in two regions because STP/LDP with a
// base+offset greater than 504 bytes is not encodable:
//   [sp + 0   .. sp + 63 ] : saved X19..X26 (callee-saved)     -- pushed by stp !
//   [sp + 64  .. sp + 703] : 80-word (8-byte words) message schedule buffer
// Preserves: X0, X3, X19..X26 (saved/restored), SP (restored).
//
// This is a direct 64-bit analogue of sha256_block_data_order_nohw.S: the
// phase decomposition (A load+REV, B extend, C load state, D 80-round compress,
// E add-back, F store) mirrors the SHA-256 scalar variant one-for-one, with
// 32-bit -> 64-bit word size, 64 rounds -> 80 rounds, and the different
// Sigma/sigma rotation amounts from FIPS 180-4 Section 4.1.3.

        .text
        .globl  sha512_block_data_order_nohw

sha512_block_data_order_nohw:
        // === Prologue: allocate frame, save callee-saved registers ===
        stp     x19, x20, [sp, #-64]!
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        stp     x25, x26, [sp, #48]
        sub     sp, sp, #640

.Lblock_loop:
        // === Phase A: for t = 0..15, load [x1 + 8*t], REV, store [sp + 8*t] ===
        mov     x17, #0
.LloadA:
        ldr     x12, [x1, x17, lsl #3]
        rev     x12, x12
        str     x12, [sp, x17, lsl #3]
        add     x17, x17, #1
        cmp     x17, #16
        b.ne    .LloadA

        // === Phase B: extend W[16..79] on stack. Base X4 = SP + 8*i. ===
        // Uses x4 as the W-base pointer and x5 as the sigma scratch so that
        // X1 (data pointer) stays live across Phase B in the outer loop.
        mov     x4, sp
        mov     x17, #0
.LextB:
        ldr     x12, [x4]                       // W[i]
        ldr     x13, [x4, #8]                   // W[i+1]
        ldr     x14, [x4, #72]                  // W[i+9]
        ldr     x15, [x4, #112]                 // W[i+14]

        // sigma0(W[i+1]) = ror(w13,1) XOR ror(w13,8) XOR (w13 >> 7)
        ror     x16, x13, #1
        ror     x5,  x13, #8
        eor     x16, x16, x5
        lsr     x5,  x13, #7
        eor     x16, x16, x5                    // x16 = sigma0

        // sigma1(W[i+14]) = ror(w15,19) XOR ror(w15,61) XOR (w15 >> 6)
        ror     x13, x15, #19
        ror     x5,  x15, #61
        eor     x13, x13, x5
        lsr     x5,  x15, #6
        eor     x13, x13, x5                    // x13 = sigma1

        // accumulate W[i+16] = W[i] + sigma0 + W[i+9] + sigma1
        add     x12, x12, x16
        add     x12, x12, x14
        add     x12, x12, x13
        str     x12, [x4, #128]

        add     x4, x4, #8
        add     x17, x17, #1
        cmp     x17, #64
        b.ne    .LextB

        // === Phase C: load initial state into X4-X11 and save to X19-X26 ===
        ldr     x4,  [x0]
        ldr     x5,  [x0, #8]
        ldr     x6,  [x0, #16]
        ldr     x7,  [x0, #24]
        ldr     x8,  [x0, #32]
        ldr     x9,  [x0, #40]
        ldr     x10, [x0, #48]
        ldr     x11, [x0, #56]
        mov     x19, x4
        mov     x20, x5
        mov     x21, x6
        mov     x22, x7
        mov     x23, x8
        mov     x24, x9
        mov     x25, x10
        mov     x26, x11

        // === Phase D: 80-round compression loop (W from SP, K from X3) ===
        mov     x17, #0
.LloopD:
        ldr     x15, [x3, x17, lsl #3]          // K_t
        ldr     x16, [sp, x17, lsl #3]          // W_t

        // Sigma1(e) = ror(e,14) XOR ror(e,18) XOR ror(e,41)
        ror     x12, x8, #41
        ror     x13, x8, #18
        eor     x12, x13, x12
        ror     x13, x8, #14
        eor     x12, x13, x12                   // x12 = Sigma1(e)

        // Ch(e,f,g) = (e AND f) XOR (g AND NOT e)
        and     x13, x8, x9
        bic     x14, x10, x8
        eor     x13, x13, x14                   // x13 = Ch(e,f,g)

        // K + W
        add     x15, x15, x16                   // x15 = K_t + W_t

        // T1 = h + (Sigma1 + (Ch + (K + W)))
        add     x15, x13, x15                   // Ch + (K+W)
        add     x15, x12, x15                   // Sigma1 + (Ch + (K+W))
        add     x12, x11, x15                   // x12 = T1

        // Sigma0(a) = ror(a,28) XOR ror(a,34) XOR ror(a,39)
        ror     x13, x4, #39
        ror     x14, x4, #34
        eor     x13, x14, x13
        ror     x14, x4, #28
        eor     x13, x14, x13                   // x13 = Sigma0(a)

        // Maj(a,b,c) = (a AND b) XOR ((a AND c) XOR (b AND c))
        and     x15, x5, x6                     // b AND c
        and     x14, x4, x6                     // a AND c
        eor     x14, x14, x15
        and     x15, x4, x5                     // a AND b
        eor     x14, x15, x14                   // x14 = Maj

        // T2 = Sigma0(a) + Maj(a,b,c)
        add     x13, x13, x14                   // x13 = T2

        // State rotation (high to low to avoid clobbering)
        mov     x11, x10                        // h <- g
        mov     x10, x9                         // g <- f
        mov     x9, x8                          // f <- e
        add     x8, x7, x12                     // e <- d + T1
        mov     x7, x6                          // d <- c
        mov     x6, x5                          // c <- b
        mov     x5, x4                          // b <- a
        add     x4, x12, x13                    // a <- T1 + T2

        add     x17, x17, #1
        cmp     x17, #80
        b.ne    .LloopD

        // === Phase E: add-back X4..X11 += X19..X26 ===
        add     x4,  x4,  x19
        add     x5,  x5,  x20
        add     x6,  x6,  x21
        add     x7,  x7,  x22
        add     x8,  x8,  x23
        add     x9,  x9,  x24
        add     x10, x10, x25
        add     x11, x11, x26

        // === Phase F: store state back to [X0] ===
        str     x4,  [x0]
        str     x5,  [x0, #8]
        str     x6,  [x0, #16]
        str     x7,  [x0, #24]
        str     x8,  [x0, #32]
        str     x9,  [x0, #40]
        str     x10, [x0, #48]
        str     x11, [x0, #56]

        // === Block-loop post-amble: advance data ptr, decrement counter ===
        add     x1, x1, #128
        sub     x2, x2, #1
        cbnz    x2, .Lblock_loop

        // === Epilogue: restore callee-saved registers, deallocate frame ===
        add     sp, sp, #640
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
