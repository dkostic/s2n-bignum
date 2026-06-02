// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// EXPERIMENTAL / UNVERIFIED variant of crc32c_octo_zerofill_xor.
//
// Same C ABI and semantics as the verified kernel
// (arm/crc32/crc32c_octo_zerofill_xor.S, locked at HEAD bf133f62), but the
// inner 128-byte loop body interleaves the 16 CRC32CX issues across the 8
// chains so consecutive CRC32CX instructions never share a destination
// accumulator. On Neoverse-N1 (Graviton 2) — one CRC pipe, ~3-cycle latency
// for CRC32CX, 1/cycle throughput — the verified kernel's
// `crc32cx wA,wA,x16; crc32cx wA,wA,x17` pattern stalls 2 cycles per pair
// (the 2nd CRC waits on the 1st). This variant arranges the inner-loop CRC
// issues so each chain's two CRC32CXs are at least 4 issue slots apart,
// well past the 3-cycle latency, letting the single CRC pipe issue at
// 1/cycle.
//
// Schedule: pair of 4-wide round-robin groups. Per 128-byte iteration:
//   group A (buffers 0..3): LDP x4 ; CRC[0] CRC[1] CRC[2] CRC[3] CRC[0] CRC[1] CRC[2] CRC[3] ; STP x4
//   group B (buffers 4..7): LDP x4 ; CRC[4] CRC[5] CRC[6] CRC[7] CRC[4] CRC[5] CRC[6] CRC[7] ; STP x4
// Within each group, the two CRC ops on the same chain are 4 cycles apart.
//
// Register allocation:
//   x0..x7   : buffer pointers (in/out)
//   x19      : len (callee-save; saved/restored at prologue/epilogue)
//   x20..x25 : extra LDP scratch (callee-save; saved/restored at prologue/epilogue)
//   w8..w15  : 8 CRC accumulators
//   x16, x17 : LDP scratch
//   w0       : return value (written at end of epilogue)
//
// Standard ARM ABI: X0..X7 = a..h, len passed on the stack; returns W0.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        .arch   armv8-a+crc
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(crc32c_octo_zerofill_xor_v2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(crc32c_octo_zerofill_xor_v2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(crc32c_octo_zerofill_xor_v2)
        .text
        .balign 4

S2N_BN_SYMBOL(crc32c_octo_zerofill_xor_v2):
        CFI_START

// Prologue: save x19..x25 (callee-save scratch) and x30 alignment.
// We push 4 pairs = 64 bytes (16-byte aligned).

        stp     x19, x20, [sp, #-64]!
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        str     x25,      [sp, #48]
        // [sp, #56] reserved for 16-byte alignment (8 bytes pad)

// Load len (9th arg, on the stack at [sp, #64+0] after the 64-byte push).

        ldr     x19, [sp, #64]

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
        b.lt    Lxzfv2_tail

        .balign 16
Lxzfv2_loop16:
        // ---- group A: buffers 0..3 ----
        ldp     x16, x17, [x0]
        ldp     x20, x21, [x1]
        ldp     x22, x23, [x2]
        ldp     x24, x25, [x3]
        crc32cx w8,  w8,  x16
        crc32cx w9,  w9,  x20
        crc32cx w10, w10, x22
        crc32cx w11, w11, x24
        crc32cx w8,  w8,  x17
        crc32cx w9,  w9,  x21
        crc32cx w10, w10, x23
        crc32cx w11, w11, x25
        stp     xzr, xzr, [x0], #16
        stp     xzr, xzr, [x1], #16
        stp     xzr, xzr, [x2], #16
        stp     xzr, xzr, [x3], #16

        // ---- group B: buffers 4..7 ----
        ldp     x16, x17, [x4]
        ldp     x20, x21, [x5]
        ldp     x22, x23, [x6]
        ldp     x24, x25, [x7]
        crc32cx w12, w12, x16
        crc32cx w13, w13, x20
        crc32cx w14, w14, x22
        crc32cx w15, w15, x24
        crc32cx w12, w12, x17
        crc32cx w13, w13, x21
        crc32cx w14, w14, x23
        crc32cx w15, w15, x25
        stp     xzr, xzr, [x4], #16
        stp     xzr, xzr, [x5], #16
        stp     xzr, xzr, [x6], #16
        stp     xzr, xzr, [x7], #16

        sub     x19, x19, #16
        cmp     x19, #16
        b.ge    Lxzfv2_loop16

Lxzfv2_tail:
        tbz     x19, #3, Lxzfv2_tail_no8
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
Lxzfv2_tail_no8:
        tbz     x19, #2, Lxzfv2_tail_no4
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
Lxzfv2_tail_no4:
        tbz     x19, #1, Lxzfv2_tail_no2
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
Lxzfv2_tail_no2:
        tbz     x19, #0, Lxzfv2_tail_no1
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
Lxzfv2_tail_no1:

// XOR-reduce all 8 accumulators (in w8..w15).

        eor     w8, w8, w9
        eor     w10, w10, w11
        eor     w12, w12, w13
        eor     w14, w14, w15
        eor     w8, w8, w10
        eor     w12, w12, w14
        eor     w0, w8, w12

// Epilogue: restore x19..x25 and return.

        ldr     x25,      [sp, #48]
        ldp     x23, x24, [sp, #32]
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(crc32c_octo_zerofill_xor_v2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
