// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Tiny register-only CRC32CX kernel: validates the CRC32CX_BRIDGE in a
// real proof context. Mirrors the SHA-256 pilot's "smallest meaningful
// register-only fragment" step (Phase 5 of the crc32c_octo_zerofill_xor
// plan).
//
// Inputs:
//   x1 : an arbitrary 64-bit value v
// Outputs:
//   w0 : crc32c_bytes (word 0xFFFFFFFF)
//        [byte 0 of v; byte 1 of v; ...; byte 7 of v]   (little-endian)
//
// extern uint32_t crc32c_step_reg(uint32_t /*unused*/, uint64_t v);
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        .arch   armv8-a+crc
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(crc32c_step_reg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(crc32c_step_reg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(crc32c_step_reg)
        .text
        .balign 4

S2N_BN_SYMBOL(crc32c_step_reg):
        CFI_START

        mov     w0, #-1                 // w0 = 0xFFFFFFFF
        crc32cx w0, w0, x1              // 8-byte CRC32C step on x1
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(crc32c_step_reg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
