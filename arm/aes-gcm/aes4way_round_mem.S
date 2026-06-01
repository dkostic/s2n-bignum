// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Phase 5 freestanding pilot: round-key memory load + 4-way AES round step
// + ciphertext memory store.
//
// This is NOT a deployable function (no callable signature, no return).  It
// is a free-standing 11-instruction block whose byte image is consumed by
// `arm/proofs/aes_gcm_enc_kernel.ml` to validate the memory-I/O bridging
// pattern in isolation, before the proof is promoted to use the full
// AES-128-GCM kernel mc once the s2n-arm checkpoint is refreshed (Phase
// 0b additions are not present in the current checkpoint, so a slice of
// the full kernel mc would fail to decode).
//
// The 11 instructions extend `aes4way_round.S` with:
//   * one round-key memory load (`ldr q23, [x8, #80]`, rk5 in the kernel)
//   * one ciphertext memory store (`st1 {v0.16b}, [x2]`)
// They are *not* an exact slice of the kernel — the kernel interleaves
// multiple loads, stores, and AES round steps for instruction-level
// scheduling.  This pilot extracts the dependency-essential subset to
// validate the proof skeleton.
//
// Byte image (matching `aes4way_round_mem_mc` in the proof file):
//   ldr   q23, [x8, #80]        // round-key load
//   aese  v0.16b, v23.16b
//   aesmc v0.16b, v0.16b
//   aese  v1.16b, v23.16b
//   aesmc v1.16b, v1.16b
//   aese  v3.16b, v23.16b
//   aesmc v3.16b, v3.16b
//   aese  v2.16b, v23.16b
//   aesmc v2.16b, v2.16b
//   st1   { v0.16b}, [x2]       // ciphertext store
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes4way_round_mem)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes4way_round_mem)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes4way_round_mem)
.align  4
aes4way_round_mem:
        ldr     q23, [x8, #80]
        aese    v0.16b, v23.16b
        aesmc   v0.16b, v0.16b
        aese    v1.16b, v23.16b
        aesmc   v1.16b, v1.16b
        aese    v3.16b, v23.16b
        aesmc   v3.16b, v3.16b
        aese    v2.16b, v23.16b
        aesmc   v2.16b, v2.16b
        st1     { v0.16b}, [x2]
