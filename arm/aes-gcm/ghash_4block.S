// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Phase 6 freestanding pilot: 4-block GHASH update (Karatsuba per-block,
// XOR-accumulator across 4 blocks, single MODULO at the end).
//
// This is NOT a deployable function (no callable signature, no return).  It
// is a free-standing 43-instruction sequence whose byte image is consumed by
// `arm/proofs/aes_gcm_enc_kernel.ml` to validate the Phase 6 4-block GHASH
// bridge (`KERNEL_4BLOCK_NIST_BRIDGE`) on the ARM ISA.
//
// The 43 instructions are extracted in kernel order from the GHASH-tagged
// (and MODULO-tagged) ops in `Lenc_main_loop` of
// `arm/aes-gcm/aes_gcm_enc_kernel_aes128.S` (lines 270 - 414, filtered to
// the pure GHASH/MODULO ops, no interleaved AES/CTR work).  The kernel's
// `rev64`+`ext`+`eor` PRE step (which composes the pre-byteswap input
// blocks plus prev_tag into the byteswap128'd Karatsuba operands) is NOT
// included here; the pilot's precondition takes the inputs in the form
// `KERNEL_4BLOCK_NIST_BRIDGE` directly expects:
//
//   v4 = byteswap128 (prev_tag XOR ct0)
//   v5 = byteswap128 ct1
//   v6 = byteswap128 ct2
//   v7 = byteswap128 ct3
//
// Per the H-table layout (`htable_mem` from `common/polyval_ghash.ml`):
//
//   v15 = byteswap128 (h_power h 3)        (the H^4 power, "byteswapped"
//                                            per htable_mem)
//   v14 = byteswap128 (h_power h 2)        (H^3)
//   v13 = byteswap128 (h_power h 1)        (H^2)
//   v12 = byteswap128 (h_power h 0)        (H^1)
//   v17 = (km h2) || (km h3)               (low 64 || high 64)
//                                            i.e. v17 = word_join (km h3) (km h2)
//   v16 = (km h0) || (km h1)               (low 64 || high 64)
//                                            i.e. v16 = word_join (km h1) (km h0)
//   where km H = karatsuba_mid H = (H.lo XOR H.hi : 64 word).
//
// Output: v11 = nist_ghash h prev_tag [ct0; ct1; ct2; ct3]
//             = kernel_modulo (XOR of h's) (XOR of l's) (XOR of m's)
//                  via KERNEL_4BLOCK_NIST_BRIDGE.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

.arch armv8-a+crypto
.text
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(ghash_4block)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(ghash_4block)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(ghash_4block)
.align  4
ghash_4block:
        // Block 4k (uses H^3 → v15):
        mov     d10,    v17.d[1]                         // d10 = km h3 (high 64 of v17)
        pmull2  v9.1q,  v4.2d,   v15.2d                  // v9  = pmul(c0.hi, H3.hi)
        mov     d8,     v4.d[1]                          // d8  = c0.hi
        pmull   v11.1q, v4.1d,   v15.1d                  // v11 = pmul(c0.lo, H3.lo)
        eor     v8.8b,  v8.8b,   v4.8b                   // d8  = c0.hi XOR c0.lo
        // Block 4k+1 (uses H^2 → v14, km h2 in v17.lo):
        pmull2  v4.1q,  v5.2d,   v14.2d                  // v4  = pmul(c1.hi, H2.hi)
        pmull   v10.1q, v8.1d,   v10.1d                  // v10 = pmul(c0.mid, km h3)
        pmull   v8.1q,  v5.1d,   v14.1d                  // v8  = pmul(c1.lo, H2.lo)
        eor     v9.16b, v9.16b,  v4.16b                  // accumulate h += pmul(c1.hi,H2.hi)
        mov     d4,     v5.d[1]                          // d4  = c1.hi
        eor     v11.16b,v11.16b, v8.16b                  // accumulate l += pmul(c1.lo,H2.lo)
        mov     d8,     v6.d[1]                          // d8  = c2.hi  (start of block 4k+2)
        eor     v4.8b,  v4.8b,   v5.8b                   // d4  = c1.hi XOR c1.lo
        eor     v8.8b,  v8.8b,   v6.8b                   // d8  = c2.hi XOR c2.lo (block 4k+2 mid)
        pmull   v4.1q,  v4.1d,   v17.1d                  // v4  = pmul(c1.mid, km h2)
        ins     v8.d[1],v8.d[0]                          // broadcast c2.mid into v8.hi
        eor     v10.16b,v10.16b, v4.16b                  // accumulate m += pmul(c1.mid, km h2)
        // Block 4k+2 (uses H^1 → v13, km h1 in v16.hi):
        pmull2  v4.1q,  v6.2d,   v13.2d                  // v4  = pmul(c2.hi, H1.hi)
        pmull   v5.1q,  v6.1d,   v13.1d                  // v5  = pmul(c2.lo, H1.lo)
        // Block 4k+3 (uses H^0 → v12, km h0 in v16.lo):
        pmull   v6.1q,  v7.1d,   v12.1d                  // v6  = pmul(c3.lo, H0.lo)
        eor     v9.16b, v9.16b,  v4.16b                  // accumulate h += pmul(c2.hi,H1.hi)
        mov     d4,     v7.d[1]                          // d4  = c3.hi
        eor     v11.16b,v11.16b, v5.16b                  // accumulate l += pmul(c2.lo,H1.lo)
        pmull2  v8.1q,  v8.2d,   v16.2d                  // v8  = pmul(c2.mid, km h1)  via pmull2
        pmull2  v5.1q,  v7.2d,   v12.2d                  // v5  = pmul(c3.hi, H0.hi)
        eor     v4.8b,  v4.8b,   v7.8b                   // d4  = c3.hi XOR c3.lo
        eor     v10.16b,v10.16b, v8.16b                  // accumulate m += pmul(c2.mid, km h1)
        // MODULO chain start:
        movi    v8.8b,  #0xc2                            // mod_constant prep (low byte)
        pmull   v4.1q,  v4.1d,   v16.1d                  // v4  = pmul(c3.mid, km h0)
        eor     v9.16b, v9.16b,  v5.16b                  // FINAL h: accumulate += pmul(c3.hi,H0.hi)
        shl     d8,     d8,      #56                     // mod_constant = 0xC2..0
        eor     v11.16b,v11.16b, v6.16b                  // FINAL l: accumulate += pmul(c3.lo,H0.lo)
        eor     v10.16b,v10.16b, v4.16b                  // FINAL m: accumulate += pmul(c3.mid,km h0)
        eor     v4.16b, v11.16b, v9.16b                  // MODULO - karatsuba tidy up (v4 = l XOR h)
        pmull   v7.1q,  v9.1d,   v8.1d                   // MODULO - top 64b align with mid
        ext     v9.16b, v9.16b,  v9.16b,  #8             // MODULO - h_swap = byteswap128 h
        eor     v10.16b,v10.16b, v4.16b                  // MODULO - karatsuba tidy up
        eor     v7.16b, v9.16b,  v7.16b                  // MODULO - fold into mid
        eor     v10.16b,v10.16b, v7.16b                  // MODULO - fold into mid
        pmull   v9.1q,  v10.1d,  v8.1d                   // MODULO - mid 64b align with low
        eor     v11.16b,v11.16b, v9.16b                  // MODULO - fold into low
        ext     v10.16b,v10.16b, v10.16b, #8             // MODULO - other mid alignment
        eor     v11.16b,v11.16b, v10.16b                 // MODULO - final fold
