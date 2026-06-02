// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Full AES-128 single-block cipher — Phase 7a register-only sub-pilot.
//
// This is NOT a deployable function (no callable signature, no return).
// It is a free-standing 21-instruction block whose byte image is consumed
// by `arm/proofs/aes_gcm_enc_kernel.ml` to validate that the full
// `aes128_cipher_arm` (9 rounds + 1 final + 1 round-key XOR) composes
// cleanly via repeated `AESMC_AESE_AS_ARM_ROUND` rewrites without term
// explosion across all 10 rounds.
//
// The kernel uses the AES-NI / s2n-bignum convention where the round key
// is XOR'd in *before* the SubBytes/ShiftRows step (absorbed into the
// previous AESE).  That's why `aes_arm_round s rk = MixColumns(SubBytes
// (ShiftRows(s ⊕ rk)))` (see aes_arm_round in aes_gcm_bridge.ml).
//
// The 21 instructions are 9 × (aese + aesmc) for rounds 0..8 with round
// keys V18..V26, then 1 × aese for round 9 with V27 (no aesmc), then
// 1 × eor with V28 to absorb the round-10 key.
//
// Byte image (matching `aes_block_full_mc` in the proof file):
//   round 0..8 (rk0..rk8 in V18..V26):
//     0x4e284a40  aese  v0.16b, v18.16b
//     0x4e286800  aesmc v0.16b, v0.16b
//     ... etc, 18 instructions ...
//   round 9 (rk9 in V27, no aesmc):
//     0x4e284b60  aese  v0.16b, v27.16b
//   round 10 (xor with rk10 in V28):
//     0x6e3c1c00  eor   v0.16b, v0.16b, v28.16b
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes_block_full)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes_block_full)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes_block_full)
.align  4
aes_block_full:
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
