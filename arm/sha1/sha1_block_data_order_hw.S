// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// SHA-1 multi-block processing (hardware-accelerated).
// Inputs state[5], data[64*num_blocks], num_blocks, K[16]; output state[5]
//
//    extern void sha1_block_data_order_hw(uint32_t state[static 5],
//                                         const uint8_t *data,
//                                         uint64_t num_blocks,
//                                         const uint32_t k[static 16]);
//
// Standard ARM ABI: X0 = state, X1 = data, X2 = num_blocks, X3 = K
//
// The K table at X3 is 16 32-bit words: four lanes each of the SHA-1
// K constants in order:
//   K[0..3]   = 0x5a827999 (rounds  0..19)
//   K[4..7]   = 0x6ed9eba1 (rounds 20..39)
//   K[8..11]  = 0x8f1bbcdc (rounds 40..59)
//   K[12..15] = 0xca62c1d6 (rounds 60..79)
//
// Modelled on aws-lc's sha1_block_data_order_hw at
// generated-src/linux-aarch64/crypto/fipsmodule/sha1-armv8.S, but with
// the K constants taken as a register-loaded table rather than as ADRP-
// relative-addressed read-only data, mirroring the SHA-256 hw pilot's
// choice on this branch.
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha1_block_data_order_hw)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha1_block_data_order_hw)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha1_block_data_order_hw)
        .text
        .balign 4

S2N_BN_SYMBOL(sha1_block_data_order_hw):
        CFI_START

// Load hash state h0..h3 into V0, h4 into V1 lane 0
// (V1's other lanes will be overwritten by the first SHA1H/SHA1C in the loop)

        ldr     q0, [x0]
        ldr     w4, [x0, #16]
        mov     v1.s[0], w4

// Load K table: K0=v16, K1=v17, K2=v18, K3=v19 (each broadcast 4-lane)

        ldr     q16, [x3]
        ldr     q17, [x3, #16]
        ldr     q18, [x3, #32]
        ldr     q19, [x3, #48]

Lsha1_block_data_order_hw_loop:

// Load 64-byte message data and advance pointer

        ldr     q4, [x1]
        ldr     q5, [x1, #16]
        ldr     q6, [x1, #32]
        ldr     q7, [x1, #48]
        add     x1, x1, #64

// Decrement block counter

        sub     x2, x2, #1

// Byte-swap message words: LE memory -> BE SHA-1

        rev32   v4.16b, v4.16b
        rev32   v5.16b, v5.16b
        rev32   v6.16b, v6.16b
        rev32   v7.16b, v7.16b

// Save initial state for add-back at end of block

        mov     v22.16b, v0.16b

// Pre-add K0 to schedule words 0..3 and 4..7

        add     v20.4s, v16.4s, v4.4s
        add     v21.4s, v16.4s, v5.4s

// === Round group 0 (rounds  0.. 3): SHA1C, K0, schedule update on V4 ===

        sha1h   s3, s0
        sha1c   q0, s1, v20.4s
        add     v20.4s, v16.4s, v6.4s
        sha1su0 v4.4s, v5.4s, v6.4s

// === Round group 1 (rounds  4.. 7): SHA1C, K0, schedule update on V5 ===

        sha1h   s2, s0
        sha1c   q0, s3, v21.4s
        add     v21.4s, v16.4s, v7.4s
        sha1su1 v4.4s, v7.4s
        sha1su0 v5.4s, v6.4s, v7.4s

// === Round group 2 (rounds  8..11): SHA1C, K0, schedule update on V6 ===

        sha1h   s3, s0
        sha1c   q0, s2, v20.4s
        add     v20.4s, v16.4s, v4.4s
        sha1su1 v5.4s, v4.4s
        sha1su0 v6.4s, v7.4s, v4.4s

// === Round group 3 (rounds 12..15): SHA1C, K0, schedule update on V7 ===

        sha1h   s2, s0
        sha1c   q0, s3, v21.4s
        add     v21.4s, v17.4s, v5.4s
        sha1su1 v6.4s, v5.4s
        sha1su0 v7.4s, v4.4s, v5.4s

// === Round group 4 (rounds 16..19): SHA1C, K1 (last C-band), schedule on V4 ===

        sha1h   s3, s0
        sha1c   q0, s2, v20.4s
        add     v20.4s, v17.4s, v6.4s
        sha1su1 v7.4s, v6.4s
        sha1su0 v4.4s, v5.4s, v6.4s

// === Round group 5 (rounds 20..23): SHA1P, K1, schedule on V5 ===

        sha1h   s2, s0
        sha1p   q0, s3, v21.4s
        add     v21.4s, v17.4s, v7.4s
        sha1su1 v4.4s, v7.4s
        sha1su0 v5.4s, v6.4s, v7.4s

// === Round group 6 (rounds 24..27): SHA1P, K1, schedule on V6 ===

        sha1h   s3, s0
        sha1p   q0, s2, v20.4s
        add     v20.4s, v17.4s, v4.4s
        sha1su1 v5.4s, v4.4s
        sha1su0 v6.4s, v7.4s, v4.4s

// === Round group 7 (rounds 28..31): SHA1P, K1, schedule on V7 ===

        sha1h   s2, s0
        sha1p   q0, s3, v21.4s
        add     v21.4s, v17.4s, v5.4s
        sha1su1 v6.4s, v5.4s
        sha1su0 v7.4s, v4.4s, v5.4s

// === Round group 8 (rounds 32..35): SHA1P, K2 (last P band of first half), schedule on V4 ===

        sha1h   s3, s0
        sha1p   q0, s2, v20.4s
        add     v20.4s, v18.4s, v6.4s
        sha1su1 v7.4s, v6.4s
        sha1su0 v4.4s, v5.4s, v6.4s

// === Round group 9 (rounds 36..39): SHA1P, K2, schedule on V5 ===

        sha1h   s2, s0
        sha1p   q0, s3, v21.4s
        add     v21.4s, v18.4s, v7.4s
        sha1su1 v4.4s, v7.4s
        sha1su0 v5.4s, v6.4s, v7.4s

// === Round group 10 (rounds 40..43): SHA1M, K2, schedule on V6 ===

        sha1h   s3, s0
        sha1m   q0, s2, v20.4s
        add     v20.4s, v18.4s, v4.4s
        sha1su1 v5.4s, v4.4s
        sha1su0 v6.4s, v7.4s, v4.4s

// === Round group 11 (rounds 44..47): SHA1M, K2, schedule on V7 ===

        sha1h   s2, s0
        sha1m   q0, s3, v21.4s
        add     v21.4s, v18.4s, v5.4s
        sha1su1 v6.4s, v5.4s
        sha1su0 v7.4s, v4.4s, v5.4s

// === Round group 12 (rounds 48..51): SHA1M, K2, schedule on V4 ===

        sha1h   s3, s0
        sha1m   q0, s2, v20.4s
        add     v20.4s, v18.4s, v6.4s
        sha1su1 v7.4s, v6.4s
        sha1su0 v4.4s, v5.4s, v6.4s

// === Round group 13 (rounds 52..55): SHA1M, K3 (last M band), schedule on V5 ===

        sha1h   s2, s0
        sha1m   q0, s3, v21.4s
        add     v21.4s, v19.4s, v7.4s
        sha1su1 v4.4s, v7.4s
        sha1su0 v5.4s, v6.4s, v7.4s

// === Round group 14 (rounds 56..59): SHA1P, K3, schedule on V6 ===

        sha1h   s3, s0
        sha1m   q0, s2, v20.4s
        add     v20.4s, v19.4s, v4.4s
        sha1su1 v5.4s, v4.4s
        sha1su0 v6.4s, v7.4s, v4.4s

// === Round group 15 (rounds 60..63): SHA1P, K3, schedule on V7 ===

        sha1h   s2, s0
        sha1p   q0, s3, v21.4s
        add     v21.4s, v19.4s, v5.4s
        sha1su1 v6.4s, v5.4s
        sha1su0 v7.4s, v4.4s, v5.4s

// === Round group 16 (rounds 64..67): SHA1P, K3, no schedule on V4 ===

        sha1h   s3, s0
        sha1p   q0, s2, v20.4s
        add     v20.4s, v19.4s, v6.4s
        sha1su1 v7.4s, v6.4s

// === Round group 17 (rounds 68..71): SHA1P, K3, no schedule on V5 ===

        sha1h   s2, s0
        sha1p   q0, s3, v21.4s
        add     v21.4s, v19.4s, v7.4s

// === Round group 18 (rounds 72..75): SHA1P, K3, no schedule on V6 ===

        sha1h   s3, s0
        sha1p   q0, s2, v20.4s

// === Round group 19 (rounds 76..79): SHA1P, K3, no schedule on V7 ===

        sha1h   s2, s0
        sha1p   q0, s3, v21.4s

// Add e back into V1[0] (the SHA1H output for round 80 is sitting in V2[0]),
// and add the saved initial v0 back into v0

        add     v1.4s, v1.4s, v2.4s
        add     v0.4s, v0.4s, v22.4s

// Loop if more blocks

        cbnz    x2, Lsha1_block_data_order_hw_loop

// Store result: h0..h3 in V0, h4 in V1 lane 0

        str     q0, [x0]
        umov    w4, v1.s[0]
        str     w4, [x0, #16]

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha1_block_data_order_hw)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
