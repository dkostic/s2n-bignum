// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// SHA-256 multi-block processing (hardware-accelerated).
// Inputs state[8], data[64*num_blocks], num_blocks, K[64]; output state[8]
//
// extern void sha256_block_data_order_hw(uint32_t state[static 8],
//                                        const uint8_t *data,
//                                        uint64_t num_blocks,
//                                        const uint32_t k[static 64]);
//
// Standard ARM ABI: X0 = state, X1 = data, X2 = num_blocks, X3 = K
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha256_block_data_order_hw)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha256_block_data_order_hw)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha256_block_data_order_hw)
        .text
        .balign 4

S2N_BN_SYMBOL(sha256_block_data_order_hw):
        CFI_START

// Load hash state (instructions 1-2)

        ldr     q0, [x0]
        ldr     q1, [x0, #16]

Lsha256_block_data_order_hw_loop:

// Load message data (instructions 3-6)

        ldr     q4, [x1]
        ldr     q5, [x1, #16]
        ldr     q6, [x1, #32]
        ldr     q7, [x1, #48]

// Advance data pointer (instruction 7)

        add     x1, x1, #64

// Decrement block counter (instruction 8)

        sub     x2, x2, #1

// Byte-swap message words: LE memory -> BE SHA-256 (instructions 9-12)

        rev32   v4.16b, v4.16b
        rev32   v5.16b, v5.16b
        rev32   v6.16b, v6.16b
        rev32   v7.16b, v7.16b

// Save initial state for add-back (instructions 13-14)

        mov     v18.16b, v0.16b
        mov     v19.16b, v1.16b

// === Round Group 0 (rounds 0-3): use Q4, update Q4 === (instructions 15-21)

        ldr     q16, [x3]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v4.4s, v5.4s
        sha256su1 v4.4s, v6.4s, v7.4s

// === Round Group 1 (rounds 4-7): use Q5, update Q5 === (instructions 22-28)

        ldr     q16, [x3, #16]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v5.4s, v6.4s
        sha256su1 v5.4s, v7.4s, v4.4s

// === Round Group 2 (rounds 8-11): use Q6, update Q6 === (instructions 29-35)

        ldr     q16, [x3, #32]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v6.4s, v7.4s
        sha256su1 v6.4s, v4.4s, v5.4s

// === Round Group 3 (rounds 12-15): use Q7, update Q7 === (instructions 36-42)

        ldr     q16, [x3, #48]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v7.4s, v4.4s
        sha256su1 v7.4s, v5.4s, v6.4s

// === Round Group 4 (rounds 16-19): use Q4, update Q4 === (instructions 43-49)

        ldr     q16, [x3, #64]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v4.4s, v5.4s
        sha256su1 v4.4s, v6.4s, v7.4s

// === Round Group 5 (rounds 20-23): use Q5, update Q5 === (instructions 50-56)

        ldr     q16, [x3, #80]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v5.4s, v6.4s
        sha256su1 v5.4s, v7.4s, v4.4s

// === Round Group 6 (rounds 24-27): use Q6, update Q6 === (instructions 57-63)

        ldr     q16, [x3, #96]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v6.4s, v7.4s
        sha256su1 v6.4s, v4.4s, v5.4s

// === Round Group 7 (rounds 28-31): use Q7, update Q7 === (instructions 64-70)

        ldr     q16, [x3, #112]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v7.4s, v4.4s
        sha256su1 v7.4s, v5.4s, v6.4s

// === Round Group 8 (rounds 32-35): use Q4, update Q4 === (instructions 71-77)

        ldr     q16, [x3, #128]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v4.4s, v5.4s
        sha256su1 v4.4s, v6.4s, v7.4s

// === Round Group 9 (rounds 36-39): use Q5, update Q5 === (instructions 78-84)

        ldr     q16, [x3, #144]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v5.4s, v6.4s
        sha256su1 v5.4s, v7.4s, v4.4s

// === Round Group 10 (rounds 40-43): use Q6, update Q6 === (instructions 85-91)

        ldr     q16, [x3, #160]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v6.4s, v7.4s
        sha256su1 v6.4s, v4.4s, v5.4s

// === Round Group 11 (rounds 44-47): use Q7, update Q7 === (instructions 92-98)

        ldr     q16, [x3, #176]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v7.4s, v4.4s
        sha256su1 v7.4s, v5.4s, v6.4s

// === Round Group 12 (rounds 48-51): use Q4, NO schedule === (instructions 99-103)

        ldr     q16, [x3, #192]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

// === Round Group 13 (rounds 52-55): use Q5, NO schedule === (instructions 104-108)

        ldr     q16, [x3, #208]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

// === Round Group 14 (rounds 56-59): use Q6, NO schedule === (instructions 109-113)

        ldr     q16, [x3, #224]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

// === Round Group 15 (rounds 60-63): use Q7, NO schedule === (instructions 114-118)

        ldr     q16, [x3, #240]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

// Add back initial state (instructions 119-120)

        add     v0.4s, v0.4s, v18.4s
        add     v1.4s, v1.4s, v19.4s

// Loop if more blocks (instruction 121)

        cbnz    x2, Lsha256_block_data_order_hw_loop

// Store result (instructions 122-123)

        str     q0, [x0]
        str     q1, [x0, #16]

// Return (instruction 124)

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha256_block_data_order_hw)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
