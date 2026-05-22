// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// One-buffer LDP+CRC+CRC+STP block-of-16 unit: validates the bridge in a
// memory-touching context. Mirrors the SHA-256 pilot's "add memory I/O"
// step (Phase 6 of the crc32c_octo_zerofill_xor plan). This is exactly
// one slice of the main loop body in crc32c_octo_zerofill_xor.S
// (`Lxzf_loop16`); the 8-buffer body is 8 such slices in sequence.
//
// Inputs:
//   x0   : pointer to a 16-byte buffer (read+write)
//   w8   : initial CRC accumulator (w8 in the canonical kernel, X8 used
//          here as a 64-bit container; only the bottom 32 bits matter)
//   x16, x17 : caller-saved scratch (overwritten)
//
// Effects:
//   x0 advanced by 16
//   16 bytes at original x0 zeroed
//   w8 = crc32c_bytes (initial w8) (16 LE bytes from the buffer)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        .arch   armv8-a+crc
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(crc32c_block16_one)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(crc32c_block16_one)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(crc32c_block16_one)
        .text
        .balign 4

S2N_BN_SYMBOL(crc32c_block16_one):
        CFI_START

        ldp     x16, x17, [x0]
        crc32cx w8,  w8,  x16
        crc32cx w8,  w8,  x17
        stp     xzr, xzr, [x0], #16
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(crc32c_block16_one)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
