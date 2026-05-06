// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// SHA-512 multi-block processing (hardware-accelerated).
// Uses ARMv8.2 FEAT_SHA512 (SHA512H/SHA512H2/SHA512SU0/SHA512SU1).
// Inputs state[8 x uint64], data[128*num_blocks bytes], num_blocks, K[80];
// output state[8 x uint64].
//
// extern void sha512_block_data_order_hw(uint64_t state[static 8],
//                                        const uint8_t *data,
//                                        uint64_t num_blocks,
//                                        const uint64_t k[static 80]);
//
// Standard ARM ABI: X0 = state, X1 = data, X2 = num_blocks, X3 = K
//
// This is s2n-bignum's straight multi-block wrapper (not aws-lc's
// software-pipelined version). Per-iteration structure:
//   8 LDR schedule (Q16-Q23)
//   advance X1 += 128, decrement X2 -= 1
//   8 REV64 (little-endian memory -> big-endian SHA-512 words)
//   4 MOV save initial state (v28..v31)
//   40 round groups (2 rounds each; groups 0..31 include schedule update,
//                    groups 32..39 omit it)
//   4 vector ADD add-back of saved state
//   CBNZ back to loop top if blocks remain
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha512_block_data_order_hw)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha512_block_data_order_hw)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha512_block_data_order_hw)
        .text
        .balign 4

S2N_BN_SYMBOL(sha512_block_data_order_hw):
        CFI_START

// Load hash state (4 Q loads; instructions 1-4)

        ldr     q0, [x0]
        ldr     q1, [x0, #16]
        ldr     q2, [x0, #32]
        ldr     q3, [x0, #48]

Lsha512_block_data_order_hw_loop:

// Load 8 schedule Q registers from message data (instructions 5-12)

        ldr     q16, [x1]
        ldr     q17, [x1, #16]
        ldr     q18, [x1, #32]
        ldr     q19, [x1, #48]
        ldr     q20, [x1, #64]
        ldr     q21, [x1, #80]
        ldr     q22, [x1, #96]
        ldr     q23, [x1, #112]

// Advance data pointer (instruction 13)

        add     x1, x1, #128

// Decrement block counter (instruction 14)

        sub     x2, x2, #1

// Byte-reverse 64-bit halves of each schedule Q (instructions 15-22).
// Memory is little-endian; SHA-512 treats each 64-bit message word as BE.

        rev64   v16.16b, v16.16b
        rev64   v17.16b, v17.16b
        rev64   v18.16b, v18.16b
        rev64   v19.16b, v19.16b
        rev64   v20.16b, v20.16b
        rev64   v21.16b, v21.16b
        rev64   v22.16b, v22.16b
        rev64   v23.16b, v23.16b

// Save initial state for add-back (instructions 23-26)

        mov     v28.16b, v0.16b
        mov     v29.16b, v1.16b
        mov     v30.16b, v2.16b
        mov     v31.16b, v3.16b

        // === Round Group 0 (rounds 0-1) ===
        ldr     q24, [x3]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 1 (rounds 2-3) ===
        ldr     q24, [x3, #16]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 2 (rounds 4-5) ===
        ldr     q24, [x3, #32]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 3 (rounds 6-7) ===
        ldr     q24, [x3, #48]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 4 (rounds 8-9) ===
        ldr     q24, [x3, #64]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 5 (rounds 10-11) ===
        ldr     q24, [x3, #80]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 6 (rounds 12-13) ===
        ldr     q24, [x3, #96]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 7 (rounds 14-15) ===
        ldr     q24, [x3, #112]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 8 (rounds 16-17) ===
        ldr     q24, [x3, #128]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 9 (rounds 18-19) ===
        ldr     q24, [x3, #144]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 10 (rounds 20-21) ===
        ldr     q24, [x3, #160]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 11 (rounds 22-23) ===
        ldr     q24, [x3, #176]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 12 (rounds 24-25) ===
        ldr     q24, [x3, #192]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 13 (rounds 26-27) ===
        ldr     q24, [x3, #208]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 14 (rounds 28-29) ===
        ldr     q24, [x3, #224]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 15 (rounds 30-31) ===
        ldr     q24, [x3, #240]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 16 (rounds 32-33) ===
        ldr     q24, [x3, #256]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 17 (rounds 34-35) ===
        ldr     q24, [x3, #272]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 18 (rounds 36-37) ===
        ldr     q24, [x3, #288]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 19 (rounds 38-39) ===
        ldr     q24, [x3, #304]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 20 (rounds 40-41) ===
        ldr     q24, [x3, #320]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 21 (rounds 42-43) ===
        ldr     q24, [x3, #336]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 22 (rounds 44-45) ===
        ldr     q24, [x3, #352]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 23 (rounds 46-47) ===
        ldr     q24, [x3, #368]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 24 (rounds 48-49) ===
        ldr     q24, [x3, #384]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 25 (rounds 50-51) ===
        ldr     q24, [x3, #400]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 26 (rounds 52-53) ===
        ldr     q24, [x3, #416]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 27 (rounds 54-55) ===
        ldr     q24, [x3, #432]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 28 (rounds 56-57) ===
        ldr     q24, [x3, #448]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 29 (rounds 58-59) ===
        ldr     q24, [x3, #464]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 30 (rounds 60-61) ===
        ldr     q24, [x3, #480]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 31 (rounds 62-63) ===
        ldr     q24, [x3, #496]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 32 (rounds 64-65) === -- no schedule update
        ldr     q24, [x3, #512]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d

        // === Round Group 33 (rounds 66-67) ===
        ldr     q24, [x3, #528]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d

        // === Round Group 34 (rounds 68-69) ===
        ldr     q24, [x3, #544]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d

        // === Round Group 35 (rounds 70-71) ===
        ldr     q24, [x3, #560]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d

        // === Round Group 36 (rounds 72-73) ===
        ldr     q24, [x3, #576]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d

        // === Round Group 37 (rounds 74-75) ===
        ldr     q24, [x3, #592]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d

        // === Round Group 38 (rounds 76-77) ===
        ldr     q24, [x3, #608]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d

        // === Round Group 39 (rounds 78-79) ===
        ldr     q24, [x3, #624]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d

// State add-back: v0..v3 += saved v28..v31

        add     v0.2d, v0.2d, v28.2d
        add     v1.2d, v1.2d, v29.2d
        add     v2.2d, v2.2d, v30.2d
        add     v3.2d, v3.2d, v31.2d

// Loop if more blocks

        cbnz    x2, Lsha512_block_data_order_hw_loop

// Store result

        str     q0, [x0]
        str     q1, [x0, #16]
        str     q2, [x0, #32]
        str     q3, [x0, #48]

// Return

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha512_block_data_order_hw)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
