// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// 8-chain CRC32C kernel that:
//   1. Computes CRC32C on 8 input buffers
//   2. Zeros each buffer as it reads (kernel-side zerofill via
//      STP xzr, xzr interleaved with the load/CRC ops)
//   3. Returns the XOR-reduction of all 8 CRCs as a SINGLE uint32_t
//
// extern uint32_t crc32c_octo_zerofill_xor(uint8_t *a, uint8_t *b,
//                                          uint8_t *c, uint8_t *d,
//                                          uint8_t *e, uint8_t *f,
//                                          uint8_t *g, uint8_t *h,
//                                          size_t len);
//
// The 8 MVNs that the canonical CRC32C finalisation would need are
// elided, because XOR'ing 8 values each with 0xFFFFFFFF cancels the
// ones-mask -- the XOR-reduction at the end is bit-equivalent to
// finalising each chain and XORing.
//
// Register allocation:
//   x0..x7   : buffer pointers (in/out)
//   x19      : len (callee-save; saved/restored at prologue/epilogue)
//   w8..w15  : 8 CRC accumulators
//   x16, x17 : LDP scratch
//   w0       : return value (written at end of epilogue)
//
// Standard ARM ABI: X0..X7 = a..h, len passed on the stack; returns W0
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        .arch   armv8-a+crc
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(crc32c_octo_zerofill_xor)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(crc32c_octo_zerofill_xor)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(crc32c_octo_zerofill_xor)
        .text
        .balign 4

S2N_BN_SYMBOL(crc32c_octo_zerofill_xor):
        CFI_START

// Prologue: save x19.

        str     x19, [sp, #-16]!

// Load len (9th arg, on the stack at [sp, #16] after the 16-byte push).

        ldr     x19, [sp, #16]

// Initialize 8 accumulators.

        mov     w8,  #-1
        mov     w9,  #-1
        mov     w10, #-1
        mov     w11, #-1
        mov     w12, #-1
        mov     w13, #-1
        mov     w14, #-1
        mov     w15, #-1

        cmp     x19, #16
        b.lt    Lxzf_tail

        .balign 16
Lxzf_loop16:
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
        b.ge    Lxzf_loop16

Lxzf_tail:
        tbz     x19, #3, Lxzf_tail_no8
        ldr     x16, [x0]
        crc32cx w8,  w8,  x16
        str     xzr, [x0], #8
        ldr     x17, [x1]
        crc32cx w9,  w9,  x17
        str     xzr, [x1], #8
        ldr     x16, [x2]
        crc32cx w10, w10, x16
        str     xzr, [x2], #8
        ldr     x17, [x3]
        crc32cx w11, w11, x17
        str     xzr, [x3], #8
        ldr     x16, [x4]
        crc32cx w12, w12, x16
        str     xzr, [x4], #8
        ldr     x17, [x5]
        crc32cx w13, w13, x17
        str     xzr, [x5], #8
        ldr     x16, [x6]
        crc32cx w14, w14, x16
        str     xzr, [x6], #8
        ldr     x17, [x7]
        crc32cx w15, w15, x17
        str     xzr, [x7], #8
Lxzf_tail_no8:
        tbz     x19, #2, Lxzf_tail_no4
        ldr     w16, [x0]
        crc32cw w8,  w8,  w16
        str     wzr, [x0], #4
        ldr     w17, [x1]
        crc32cw w9,  w9,  w17
        str     wzr, [x1], #4
        ldr     w16, [x2]
        crc32cw w10, w10, w16
        str     wzr, [x2], #4
        ldr     w17, [x3]
        crc32cw w11, w11, w17
        str     wzr, [x3], #4
        ldr     w16, [x4]
        crc32cw w12, w12, w16
        str     wzr, [x4], #4
        ldr     w17, [x5]
        crc32cw w13, w13, w17
        str     wzr, [x5], #4
        ldr     w16, [x6]
        crc32cw w14, w14, w16
        str     wzr, [x6], #4
        ldr     w17, [x7]
        crc32cw w15, w15, w17
        str     wzr, [x7], #4
Lxzf_tail_no4:
        tbz     x19, #1, Lxzf_tail_no2
        ldrh    w16, [x0]
        crc32ch w8,  w8,  w16
        strh    wzr, [x0], #2
        ldrh    w17, [x1]
        crc32ch w9,  w9,  w17
        strh    wzr, [x1], #2
        ldrh    w16, [x2]
        crc32ch w10, w10, w16
        strh    wzr, [x2], #2
        ldrh    w17, [x3]
        crc32ch w11, w11, w17
        strh    wzr, [x3], #2
        ldrh    w16, [x4]
        crc32ch w12, w12, w16
        strh    wzr, [x4], #2
        ldrh    w17, [x5]
        crc32ch w13, w13, w17
        strh    wzr, [x5], #2
        ldrh    w16, [x6]
        crc32ch w14, w14, w16
        strh    wzr, [x6], #2
        ldrh    w17, [x7]
        crc32ch w15, w15, w17
        strh    wzr, [x7], #2
Lxzf_tail_no2:
        tbz     x19, #0, Lxzf_tail_no1
        ldrb    w16, [x0]
        crc32cb w8,  w8,  w16
        strb    wzr, [x0]
        ldrb    w17, [x1]
        crc32cb w9,  w9,  w17
        strb    wzr, [x1]
        ldrb    w16, [x2]
        crc32cb w10, w10, w16
        strb    wzr, [x2]
        ldrb    w17, [x3]
        crc32cb w11, w11, w17
        strb    wzr, [x3]
        ldrb    w16, [x4]
        crc32cb w12, w12, w16
        strb    wzr, [x4]
        ldrb    w17, [x5]
        crc32cb w13, w13, w17
        strb    wzr, [x5]
        ldrb    w16, [x6]
        crc32cb w14, w14, w16
        strb    wzr, [x6]
        ldrb    w17, [x7]
        crc32cb w15, w15, w17
        strb    wzr, [x7]
Lxzf_tail_no1:

// XOR-reduce all 8 accumulators (in w8..w15).
// Note: final spec requires `result_i = ~crc_i` for each chain
// (per CRC32C definition). But we're XORing 8 of them:
//   (~a) ^ (~b) ^ ... ^ (~h) = a ^ b ^ ... ^ h
// because 8 copies of 0xFFFFFFFF XOR to zero.
// So we can skip the 8 MVNs entirely.

        eor     w8, w8, w9
        eor     w10, w10, w11
        eor     w12, w12, w13
        eor     w14, w14, w15
        eor     w8, w8, w10
        eor     w12, w12, w14
        eor     w0, w8, w12

// Epilogue: restore x19 and return.

        ldr     x19, [sp], #16
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(crc32c_octo_zerofill_xor)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
