// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// SHA-256 message schedule computation using scalar instructions.
// Loads 16 big-endian message words from [X1], byte-swaps each to
// native form, and extends the schedule to 64 words W[0..63] stored
// at [X0 + 4*t] for t = 0..63.
//
// Input:
//   X0 = pointer to output W[0..63] buffer (256 bytes)
//   X1 = pointer to message block (64 bytes, big-endian)
// Output:
//   (memory at X0) = sha256_message_schedule 48 of bytereversed input
// Clobbers: W2-W3, W12-W16, X17

        .text
        .globl  sha256_schedule_scalar

sha256_schedule_scalar:

        // Phase 1: for t = 0..15, load [x1 + 4*t], byte-swap, store [x0 + 4*t]
        mov     x17, #0
.Lload:
        ldr     w12, [x1, x17, lsl #2]
        rev     w12, w12
        str     w12, [x0, x17, lsl #2]
        add     x17, x17, #1
        cmp     x17, #16
        b.ne    .Lload

        // Phase 2: for i = 0..47, compute W[i+16]
        //   = sigma1(W[i+14]) + W[i+9] + sigma0(W[i+1]) + W[i]
        // Use base pointer X2 = &W[i], advancing by 4 each iter.
        mov     x2, x0
        mov     x17, #0
.Lext:
        ldr     w12, [x2]               // W[i]
        ldr     w13, [x2, #4]           // W[i+1]
        ldr     w14, [x2, #36]          // W[i+9]
        ldr     w15, [x2, #56]          // W[i+14]

        // sigma0(W[i+1]) = ror(w13,7) XOR ror(w13,18) XOR (w13 >> 3)
        ror     w16, w13, #7
        ror     w3,  w13, #18
        eor     w16, w16, w3
        lsr     w3,  w13, #3
        eor     w16, w16, w3            // w16 = sigma0

        // sigma1(W[i+14]) = ror(w15,17) XOR ror(w15,19) XOR (w15 >> 10)
        ror     w13, w15, #17
        ror     w3,  w15, #19
        eor     w13, w13, w3
        lsr     w3,  w15, #10
        eor     w13, w13, w3            // w13 = sigma1

        // Accumulate: w12 = W[i] + sigma0 + W[i+9] + sigma1
        add     w12, w12, w16
        add     w12, w12, w14
        add     w12, w12, w13
        str     w12, [x2, #64]

        add     x2, x2, #4
        add     x17, x17, #1
        cmp     x17, #48
        b.ne    .Lext

        ret
