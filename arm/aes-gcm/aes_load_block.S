// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Phase 5 freestanding pilot 2: plaintext load via ldp + fmov to Q register.
//
// This is the kernel's recurring pattern for routing plaintext blocks from
// memory into Q registers without a Q-form load (the kernel uses scalar
// loads so it can XOR the round-N key in scalar form before assembling).
//
// Byte image (matching `aes_load_block_mc` in the proof file):
//   ldp     x6, x7, [x0]        // load 16-byte plaintext as two int64
//   fmov    d4, x6               // x6 → Q4 low 64 bits (upper bits zero)
//   fmov    v4.d[1], x7          // x7 → Q4 high 64 bits (Q4 is now 128 bits)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes_load_block)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes_load_block)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes_load_block)
.align  4
aes_load_block:
        ldp     x6, x7, [x0]
        fmov    d4, x6
        fmov    v4.d[1], x7
