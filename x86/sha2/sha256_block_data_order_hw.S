// Copyright (c) The OpenSSL Project Authors. All Rights Reserved.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Adapted for s2n-bignum from
// aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/sha256-x86_64.S
// (Andy Polyakov's SHA-NI implementation), with the following changes:
//   * K is passed as a 4th argument in %rcx instead of loaded from
//     rodata via `leaq K256+128(%rip), %rcx`. The upstream table is
//     stored with stride 32 (each round constant quartet duplicated);
//     here K has stride 16 so offsets are halved (N-128(%rcx) becomes
//     (N/2)(%rcx) relative to K[0]).
//   * The SSSE3 pshufb mask that upstream stored at K256+512 is now
//     passed as the final 4 words of K, i.e. at offset 256 relative to
//     K[0]. The caller must provide K as a 68-entry array: the standard
//     64 SHA-256 round constants followed by the 4-word mask
//     0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f.
//   * Intel syntax and the s2n-bignum visibility / CFI / CET macros.
//   * The BORINGSSL_DISPATCH_TEST block and the upstream K256 / size
//     directives are dropped.

// ----------------------------------------------------------------------------
// SHA-256 multi-block processing (hardware-accelerated, SHA-NI).
// Inputs state[8], data[64*num_blocks], num_blocks, K[68]; output state[8]
//
// extern void sha256_block_data_order_hw(uint32_t state[static 8],
//                                        const uint8_t *data,
//                                        uint64_t num_blocks,
//                                        const uint32_t k[static 68]);
//
// Standard x86-64 ABI: RDI = state, RSI = data, RDX = num_blocks, RCX = K
// Requires: num_blocks >= 1.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha256_block_data_order_hw)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha256_block_data_order_hw)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha256_block_data_order_hw)
        .text
        .balign 64

S2N_BN_SYMBOL(sha256_block_data_order_hw):
        CFI_START
        _CET_ENDBR

        movdqu   xmm1, XMMWORD PTR [rdi]
        movdqu   xmm2, XMMWORD PTR [rdi+16]
        movdqa   xmm7, XMMWORD PTR [rcx+256]

        pshufd   xmm0, xmm1, 0x1b
        pshufd   xmm1, xmm1, 0xb1
        pshufd   xmm2, xmm2, 0x1b
        movdqa   xmm8, xmm7
        palignr  xmm1, xmm2, 8
        punpcklqdq xmm2, xmm0
        jmp      Lsha256_block_data_order_hw_loop

        .balign 16
Lsha256_block_data_order_hw_loop:
        movdqu   xmm3, XMMWORD PTR [rsi]
        movdqu   xmm4, XMMWORD PTR [rsi+16]
        movdqu   xmm5, XMMWORD PTR [rsi+32]
        pshufb   xmm3, xmm7
        movdqu   xmm6, XMMWORD PTR [rsi+48]

        movdqa   xmm0, XMMWORD PTR [rcx+0]
        paddd    xmm0, xmm3
        pshufb   xmm4, xmm7
        movdqa   xmm10, xmm2
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        nop
        movdqa   xmm9, xmm1
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+16]
        paddd    xmm0, xmm4
        pshufb   xmm5, xmm7
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        lea      rsi, [rsi+64]
        sha256msg1 xmm3, xmm4
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+32]
        paddd    xmm0, xmm5
        pshufb   xmm6, xmm7
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm6
        palignr  xmm7, xmm5, 4
        nop
        paddd    xmm3, xmm7
        sha256msg1 xmm4, xmm5
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+48]
        paddd    xmm0, xmm6
        sha256msg2 xmm3, xmm6
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm3
        palignr  xmm7, xmm6, 4
        nop
        paddd    xmm4, xmm7
        sha256msg1 xmm5, xmm6
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+64]
        paddd    xmm0, xmm3
        sha256msg2 xmm4, xmm3
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm4
        palignr  xmm7, xmm3, 4
        nop
        paddd    xmm5, xmm7
        sha256msg1 xmm6, xmm3
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+80]
        paddd    xmm0, xmm4
        sha256msg2 xmm5, xmm4
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm5
        palignr  xmm7, xmm4, 4
        nop
        paddd    xmm6, xmm7
        sha256msg1 xmm3, xmm4
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+96]
        paddd    xmm0, xmm5
        sha256msg2 xmm6, xmm5
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm6
        palignr  xmm7, xmm5, 4
        nop
        paddd    xmm3, xmm7
        sha256msg1 xmm4, xmm5
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+112]
        paddd    xmm0, xmm6
        sha256msg2 xmm3, xmm6
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm3
        palignr  xmm7, xmm6, 4
        nop
        paddd    xmm4, xmm7
        sha256msg1 xmm5, xmm6
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+128]
        paddd    xmm0, xmm3
        sha256msg2 xmm4, xmm3
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm4
        palignr  xmm7, xmm3, 4
        nop
        paddd    xmm5, xmm7
        sha256msg1 xmm6, xmm3
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+144]
        paddd    xmm0, xmm4
        sha256msg2 xmm5, xmm4
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm5
        palignr  xmm7, xmm4, 4
        nop
        paddd    xmm6, xmm7
        sha256msg1 xmm3, xmm4
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+160]
        paddd    xmm0, xmm5
        sha256msg2 xmm6, xmm5
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm6
        palignr  xmm7, xmm5, 4
        nop
        paddd    xmm3, xmm7
        sha256msg1 xmm4, xmm5
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+176]
        paddd    xmm0, xmm6
        sha256msg2 xmm3, xmm6
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm3
        palignr  xmm7, xmm6, 4
        nop
        paddd    xmm4, xmm7
        sha256msg1 xmm5, xmm6
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+192]
        paddd    xmm0, xmm3
        sha256msg2 xmm4, xmm3
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm4
        palignr  xmm7, xmm3, 4
        nop
        paddd    xmm5, xmm7
        sha256msg1 xmm6, xmm3
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+208]
        paddd    xmm0, xmm4
        sha256msg2 xmm5, xmm4
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        movdqa   xmm7, xmm5
        palignr  xmm7, xmm4, 4
        sha256rnds2 xmm1, xmm2
        paddd    xmm6, xmm7

        movdqa   xmm0, XMMWORD PTR [rcx+224]
        paddd    xmm0, xmm5
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        sha256msg2 xmm6, xmm5
        movdqa   xmm7, xmm8
        sha256rnds2 xmm1, xmm2

        movdqa   xmm0, XMMWORD PTR [rcx+240]
        paddd    xmm0, xmm6
        nop
        sha256rnds2 xmm2, xmm1
        pshufd   xmm0, xmm0, 0x0e
        dec      rdx
        nop
        sha256rnds2 xmm1, xmm2

        paddd    xmm2, xmm10
        paddd    xmm1, xmm9
        jnz      Lsha256_block_data_order_hw_loop

        pshufd   xmm2, xmm2, 0xb1
        pshufd   xmm7, xmm1, 0x1b
        pshufd   xmm1, xmm1, 0xb1
        punpckhqdq xmm1, xmm2
        palignr  xmm2, xmm7, 8

        movdqu   XMMWORD PTR [rdi], xmm1
        movdqu   XMMWORD PTR [rdi+16], xmm2
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha256_block_data_order_hw)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
