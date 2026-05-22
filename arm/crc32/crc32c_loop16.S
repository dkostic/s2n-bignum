// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multi-iteration loop16 kernel for crc32c_octo_zerofill_xor (Phase 8 of the
// crc32c_octo_zerofill_xor plan). One iteration of the body matches the
// Phase 7 33-instruction kernel (8 LDP+CRC+CRC+STP slices + sub x19,x19,#16);
// the closing pair `cmp x19, #16; b.ge .Lloop16` makes this a real loop.
//
// The loop is entered with x19 already known to be >= 16 (the entry guard
// `cmp x19,#16; b.lt Lxzf_tail` is part of the surrounding kernel, not this
// fragment). Execution continues to fall through the b.ge once x19 < 16.
//
// Inputs at loop entry:
//   x0..x7   : pointers to len-byte buffers (read+written, advance 16/iter)
//   w8..w15  : 8 CRC accumulators
//   x19      : remaining-byte counter, multiple-of-16 part already arranged
//
// Effects after loop completes (x19 < 16):
//   x0..x7 advanced by 16 * (initial_iters)
//   the prefix of (16 * initial_iters) bytes at each buffer zeroed
//   w8..w15 fold the consumed prefix bytes (LSB-first, 8 bytes per CRC32CX)
//   x19 = initial_x19 - 16 * initial_iters
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        .arch   armv8-a+crc
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(crc32c_loop16)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(crc32c_loop16)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(crc32c_loop16)
        .text
        .balign 4

S2N_BN_SYMBOL(crc32c_loop16):
        CFI_START

Lloop16:
        ldp     x16, x17, [x0]
        crc32cx w8,  w8,  x16
        crc32cx w8,  w8,  x17
        stp     xzr, xzr, [x0], #16

        ldp     x16, x17, [x1]
        crc32cx w9,  w9,  x16
        crc32cx w9,  w9,  x17
        stp     xzr, xzr, [x1], #16

        ldp     x16, x17, [x2]
        crc32cx w10, w10, x16
        crc32cx w10, w10, x17
        stp     xzr, xzr, [x2], #16

        ldp     x16, x17, [x3]
        crc32cx w11, w11, x16
        crc32cx w11, w11, x17
        stp     xzr, xzr, [x3], #16

        ldp     x16, x17, [x4]
        crc32cx w12, w12, x16
        crc32cx w12, w12, x17
        stp     xzr, xzr, [x4], #16

        ldp     x16, x17, [x5]
        crc32cx w13, w13, x16
        crc32cx w13, w13, x17
        stp     xzr, xzr, [x5], #16

        ldp     x16, x17, [x6]
        crc32cx w14, w14, x16
        crc32cx w14, w14, x17
        stp     xzr, xzr, [x6], #16

        ldp     x16, x17, [x7]
        crc32cx w15, w15, x16
        crc32cx w15, w15, x17
        stp     xzr, xzr, [x7], #16

        sub     x19, x19, #16
        cmp     x19, #16
        b.ge    Lloop16

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(crc32c_loop16)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
