// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Phase 6 freestanding pilot: GHASH MODULO reduction step.
//
// This is NOT a deployable function (no callable signature, no return).  It
// is a free-standing 12-instruction block whose byte image is consumed by
// `arm/proofs/aes_gcm_enc_kernel.ml` to validate the Phase 6 GHASH MODULO
// reduction bridge in isolation, before the proof is promoted to the full
// 4-block GHASH chain (Phase 7+).
//
// The 12 instructions match the kernel's MODULO chain at
// `arm/aes-gcm/aes_gcm_enc_kernel_aes128.S` lines 356-414 (filtered to the
// pure GHASH-MODULO ops, no interleaved AES/CTR work).  Inputs:
//
//   v9  = h-component (high 64-bit Karatsuba product accumulator)
//   v10 = m-component (mid 64-bit Karatsuba product accumulator)
//   v11 = l-component (low 64-bit Karatsuba product accumulator)
//
// Output:
//
//   v11 = polyval_reduce_prop3(karatsuba_combine v11 v9 v10)
//       = kernel_modulo v9 v11 v10                       (per the bridge file)
//
// This pilot exercises the Phase 0b scalar-SHL D-form decoder addition
// (`shl d8, d8, #56`).  All other instructions in the chain (movi, pmull,
// ext, eor) are pre-existing decoder rows.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(ghash_modulo)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(ghash_modulo)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(ghash_modulo)
.align  4
ghash_modulo:
        movi    v8.8b, #0xc2
        shl     d8, d8, #56
        eor     v4.16b, v11.16b, v9.16b
        pmull   v7.1q, v9.1d, v8.1d
        ext     v9.16b, v9.16b, v9.16b, #8
        eor     v10.16b, v10.16b, v4.16b
        eor     v7.16b, v9.16b, v7.16b
        eor     v10.16b, v10.16b, v7.16b
        pmull   v9.1q, v10.1d, v8.1d
        ext     v10.16b, v10.16b, v10.16b, #8
        eor     v11.16b, v11.16b, v9.16b
        eor     v11.16b, v11.16b, v10.16b
