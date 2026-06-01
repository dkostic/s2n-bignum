// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// 8-buffer single-iteration loop16 body for crc32c_octo_zerofill_xor (Phase
// 7 of the crc32c_octo_zerofill_xor plan). This is one full iteration of
// the .Lxzf_loop16 body in crc32c_octo_zerofill_xor.S: 8 copies of the
// (LDP+CRC+CRC+STP) slice from Phase 6, one per buffer/accumulator pair
// (X0,W8)..(X7,W15), followed by `sub x19, x19, #16` to decrement the
// remaining-byte counter. The cmp/b.ge live in Phase 8 (loop tactic).
//
// Inputs:
//   x0..x7   : pointers to 16-byte buffers (read+write)
//   w8..w15  : initial CRC accumulators
//   x19      : remaining-byte counter (decremented by 16)
//   x16, x17 : caller-saved scratch (overwritten)
//
// Effects:
//   x0..x7 each advanced by 16
//   16 bytes at original x0..x7 zeroed
//   w8..w15 = crc32c_bytes (initial) (16 LE bytes from corresponding buffer)
//   x19 decremented by 16
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        .arch   armv8-a+crc
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(crc32c_loop16_body)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(crc32c_loop16_body)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(crc32c_loop16_body)
        .text
        .balign 4

S2N_BN_SYMBOL(crc32c_loop16_body):
        CFI_START

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
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(crc32c_loop16_body)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
