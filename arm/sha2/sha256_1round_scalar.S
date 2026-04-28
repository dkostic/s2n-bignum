// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// One round of SHA-256 compression using scalar instructions only.
// Input:  W0 = K_t, W1 = W_t, W4-W11 = state [a,b,c,d,e,f,g,h]
// Output: W4-W11 = sha256_compress_round(K_t, W_t, [a,b,c,d,e,f,g,h])
// Clobbers: W12-W15

        .text
        .globl  sha256_1round_scalar

sha256_1round_scalar:

        // Sigma1(e) = ror(e,6) XOR (ror(e,11) XOR ror(e,25))
        ror     w12, w8, #25
        ror     w13, w8, #11
        eor     w12, w13, w12
        ror     w13, w8, #6
        eor     w12, w13, w12           // w12 = Sigma1(e)

        // Ch(e,f,g) = (e AND f) XOR (g AND NOT e)
        and     w13, w8, w9
        bic     w14, w10, w8
        eor     w13, w13, w14           // w13 = Ch(e,f,g)

        // K + W
        add     w15, w0, w1             // w15 = K_t + W_t

        // T1 = h + (Sigma1 + (Ch + (K + W)))
        add     w15, w13, w15           // Ch + (K+W)
        add     w15, w12, w15           // Sigma1 + (Ch + (K+W))
        add     w12, w11, w15           // w12 = T1

        // Sigma0(a) = ror(a,2) XOR (ror(a,13) XOR ror(a,22))
        ror     w13, w4, #22
        ror     w14, w4, #13
        eor     w13, w14, w13
        ror     w14, w4, #2
        eor     w13, w14, w13           // w13 = Sigma0(a)

        // Maj(a,b,c) = (a AND b) XOR ((a AND c) XOR (b AND c))
        and     w15, w5, w6             // b AND c
        and     w14, w4, w6             // a AND c
        eor     w14, w14, w15           // (a AND c) XOR (b AND c)
        and     w15, w4, w5             // a AND b
        eor     w14, w15, w14           // Maj = (a AND b) XOR ((a AND c) XOR (b AND c))

        // T2 = Sigma0(a) + Maj(a,b,c)
        add     w13, w13, w14           // w13 = T2

        // State rotation (high to low to avoid clobbering)
        mov     w11, w10                // h <- g
        mov     w10, w9                 // g <- f
        mov     w9, w8                  // f <- e
        add     w8, w7, w12             // e <- d + T1
        mov     w7, w6                  // d <- c
        mov     w6, w5                  // c <- b
        mov     w5, w4                  // b <- a
        add     w4, w12, w13            // a <- T1 + T2

        ret
