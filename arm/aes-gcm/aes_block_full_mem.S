// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Full single-block AES-128 encryption with memory I/O — Phase 7a sub-pilot.
//
// This is NOT a deployable function (no callable signature, no return).
// It composes:
//   - LDR Q0, [X0]   -- load 16-byte plaintext from memory
//   - 9 × (AESE+AESMC) for rounds 0..8 with rk0..rk8 in V18..V26
//   - AESE for round 9 (rk9 in V27, no AESMC)
//   - EOR with rk10 in V28 (round-10 key absorption)
//   - STR Q0, [X2]   -- store 16-byte ciphertext to memory
//
// Total: 23 instructions.  Validates that the full AES-128 cipher with
// memory plaintext load + memory ciphertext store composes against
// `aes128_cipher_arm`.  No GHASH, no loop.
//
// Byte image:
//   0x3dc00000  ldr   q0, [x0]
//   0x4e284a40  aese  v0.16b, v18.16b
//   0x4e286800  aesmc v0.16b, v0.16b
//   ... rest of cipher 19 instructions ...
//   0x3d800040  str   q0, [x2]
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes_block_full_mem)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes_block_full_mem)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes_block_full_mem)
.align  4
aes_block_full_mem:
        ldr     q0, [x0]
        // 9 rounds of AESE+AESMC with rk0..rk8 in V18..V26
        aese    v0.16b, v18.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v19.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v20.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v21.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v22.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v23.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v24.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v25.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        // round 9: aese with rk9 in V27, no aesmc
        aese    v0.16b, v27.16b
        // round 10: xor with rk10 in V28
        eor     v0.16b, v0.16b, v28.16b
        str     q0, [x2]
