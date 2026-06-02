// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// 4-way 2-round AES chain — Phase 7a register-only sub-pilot for AES-GCM
// proof.
//
// This is NOT a deployable function (no callable signature, no return).  It
// is a free-standing 16-instruction block whose byte image is consumed by
// `arm/proofs/aes_gcm_enc_kernel.ml` to validate that AES round chains
// compose cleanly via repeated `AESMC_AESE_AS_ARM_ROUND` rewrites without
// term explosion.
//
// The 16 instructions are an exact copy of the round-4 and round-5 4-way
// step in `aes_gcm_enc_kernel_aes128.S` (kernel offsets 0x16c..0x1a8): each
// pair `aese Qi, V_K ; aesmc Qi, Qi` performs one AES round on state
// register Qi with the round key in V_K.  The kernel emits round 4 in the
// order 2, 0, 1, 3 and round 5 in the order 0, 1, 3, 2.
//
// Byte image (matching `aes4way_2rounds_mc` in the proof file):
//   round 4 (key in V22):
//     0x4e284ac2  aese  v2.16b, v22.16b
//     0x4e286842  aesmc v2.16b, v2.16b
//     0x4e284ac0  aese  v0.16b, v22.16b
//     0x4e286800  aesmc v0.16b, v0.16b
//     0x4e284ac1  aese  v1.16b, v22.16b
//     0x4e286821  aesmc v1.16b, v1.16b
//     0x4e284ac3  aese  v3.16b, v22.16b
//     0x4e286863  aesmc v3.16b, v3.16b
//   round 5 (key in V23):
//     0x4e284ae0  aese  v0.16b, v23.16b
//     0x4e286800  aesmc v0.16b, v0.16b
//     0x4e284ae1  aese  v1.16b, v23.16b
//     0x4e286821  aesmc v1.16b, v1.16b
//     0x4e284ae3  aese  v3.16b, v23.16b
//     0x4e286863  aesmc v3.16b, v3.16b
//     0x4e284ae2  aese  v2.16b, v23.16b
//     0x4e286842  aesmc v2.16b, v2.16b
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes4way_2rounds)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes4way_2rounds)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes4way_2rounds)
.align  4
aes4way_2rounds:
        // round 4 (rk4 in V22), block order 2, 0, 1, 3
        aese    v2.16b, v22.16b
        aesmc   v2.16b, v2.16b
        aese    v0.16b, v22.16b
        aesmc   v0.16b, v0.16b
        aese    v1.16b, v22.16b
        aesmc   v1.16b, v1.16b
        aese    v3.16b, v22.16b
        aesmc   v3.16b, v3.16b
        // round 5 (rk5 in V23), block order 0, 1, 3, 2
        aese    v0.16b, v23.16b
        aesmc   v0.16b, v0.16b
        aese    v1.16b, v23.16b
        aesmc   v1.16b, v1.16b
        aese    v3.16b, v23.16b
        aesmc   v3.16b, v3.16b
        aese    v2.16b, v23.16b
        aesmc   v2.16b, v2.16b
