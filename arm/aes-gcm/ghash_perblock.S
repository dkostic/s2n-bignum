// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Phase 6 freestanding pilot: per-block Karatsuba decomposition.
//
// This is NOT a deployable function (no callable signature, no return).  It
// is a free-standing 5-instruction block whose byte image is consumed by
// `arm/proofs/aes_gcm_enc_kernel.ml` to validate the per-block Karatsuba
// decomposition pattern in isolation.
//
// The kernel computes (h, l, m) = karatsuba_components c H per block, with
// the karatsuba_mid of the H power supplied separately (precomputed at
// htable-init time and stored in v17 / v16 with two k's joined).  The
// 5-instruction sequence here:
//
//   pmull2 v9.1q,  v4.2d,  v15.2d         // v9 = pmul(high64 c, high64 H)
//   pmull  v11.1q, v4.1d,  v15.1d         // v11 = pmul(low64 c, low64 H)
//   mov    d8,     v4.d[1]                // d8 = high64 c
//   eor    v8.8b,  v8.8b,  v4.8b          // d8 = high64 c XOR low64 c
//   pmull  v10.1q, v8.1d,  v17.1d         // v10 = pmul(mid_c, kmid_H)
//
// produces
//
//   v9  = pmul(high64 c, high64 H)               -- h-component
//   v11 = pmul(low64 c, low64 H)                 -- l-component
//   v10 = pmul(low64 c XOR high64 c, kmid_H)     -- m-component (using precomputed kmid_H)
//
// where v4 = c, v15 = H, v17.lo64 = kmid_H = karatsuba_mid H.
//
// The pilot exercises the Phase 0b DUP-from-element decoder addition
// (`mov d8, v4.d[1]` decodes to `arm_DUP_GEN_FROM_ELEM Q8 Q4 64 64 1`).
// pmull2/pmull/eor are pre-existing decoder rows.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(ghash_perblock)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(ghash_perblock)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(ghash_perblock)
.align  4
ghash_perblock:
        pmull2  v9.1q,  v4.2d,  v15.2d
        pmull   v11.1q, v4.1d,  v15.1d
        mov     d8,     v4.d[1]
        eor     v8.8b,  v8.8b,  v4.8b
        pmull   v10.1q, v8.1d,  v17.1d
