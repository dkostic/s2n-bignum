// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// 4-way AES round step — Phase 4 register-only pilot for AES-GCM proof.
//
// This is NOT a deployable function (no callable signature, no return).  It
// is a free-standing 8-instruction block whose byte image is consumed by
// `arm/proofs/aes_gcm_enc_kernel.ml` to validate the AES bridging-lemma
// pattern in isolation, before the proof is promoted to use the full
// AES-128-GCM kernel mc in Phase 5+.
//
// The 8 instructions are an exact copy of the round-5 4-way step in
// `aes_gcm_enc_kernel_aes128.S` (kernel offsets 0x18c..0x1a8): each pair
// `aese Qi, V23 ; aesmc Qi, Qi` performs one AES round on state register
// Qi with the round key in Q23.  The kernel emits the four blocks in the
// order 0, 1, 3, 2.
//
// Byte image (matching `aes4way_round_mc` in the proof file):
//   0x4e284ae0  aese  v0.16b, v23.16b
//   0x4e286800  aesmc v0.16b, v0.16b
//   0x4e284ae1  aese  v1.16b, v23.16b
//   0x4e286821  aesmc v1.16b, v1.16b
//   0x4e284ae3  aese  v3.16b, v23.16b
//   0x4e286863  aesmc v3.16b, v3.16b
//   0x4e284ae2  aese  v2.16b, v23.16b
//   0x4e286842  aesmc v2.16b, v2.16b
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes4way_round)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes4way_round)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes4way_round)
.align  4
aes4way_round:
        aese    v0.16b, v23.16b
        aesmc   v0.16b, v0.16b
        aese    v1.16b, v23.16b
        aesmc   v1.16b, v1.16b
        aese    v3.16b, v23.16b
        aesmc   v3.16b, v3.16b
        aese    v2.16b, v23.16b
        aesmc   v2.16b, v2.16b
