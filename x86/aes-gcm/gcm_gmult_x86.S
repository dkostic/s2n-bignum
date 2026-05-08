// ===========================================================================
// Single-block GHASH multiply, standalone artefact form (Milestone 6).
//
// This file provides a single-entry `gcm_gmult_x86` that mirrors aws-lc's
// `gcm_gmult_clmul` from `ghash-x86_64.S` (commit 2ddb1c333f25f0288e8413d32b
// 30260da3802157), VEX-encoded and packaged as a proof artefact:
//
//   - The `pshufd $78, ...` half-swap is replaced by the byte-for-byte-
//     equivalent `vpalignr $8, src, src, dst` (VPSHUFD is not in
//     s2n-bignum's decoder; VPALIGNR is).
//   - The Karatsuba middle-term for H (which aws-lc loads from the
//     `Htable[2]` slot populated by `gcm_init_clmul`) is recomputed
//     in-register via `vpalignr $8` + `vpxor`, so the Htable precondition
//     simplifies to a single 16-byte `H` load.
//   - bswap_mask is passed as a pointer argument rather than living in
//     `.rodata`: a constant `.section .rodata` block would introduce
//     a second loaded-bytes precondition for the .S artefact, which
//     is cleaner to keep as a caller responsibility.
//   - All non-VEX SSE mnemonics (movdqu, movdqa, pshufb, psllq, psrlq,
//     pslldq, psrldq, pxor, pclmulqdq) become their VEX counterparts;
//     this matches the Milestone 5 convention and keeps the artefact
//     inside the vex-aes + pre-existing s2n-bignum decoder surface.
//
// System V ABI:
//     rdi = Xi pointer        (16 bytes, read + write)
//     rsi = H pointer         (16 bytes, read;
//                               value expected to be the "twisted +
//                               byte-reversed" H that aws-lc's
//                               `gcm_init_clmul` writes to its output
//                               slot 0)
//     rdx = bswap_mask pointer (16 bytes, read;
//                                value = byte-reverse permutation
//                                0F 0E 0D 0C 0B 0A 09 08
//                                07 06 05 04 03 02 01 00)
//
// Correctness (spec-side statement in `x86/proofs/gcm_gmult_x86.ml`):
//     new_Xi = byteswap128 ( polyval_dot (byteswap128 Xi) H )
// where `Xi` here denotes the in-memory 16-byte value at `rdi`, and
// `H` denotes the 16-byte value at `rsi` (both viewed as int128 /
// little-endian-in-memory, matching `read (memory :> bytes128 p)`).
// The byte-reversals bridge the hardware XMM layout to the POLYVAL
// dot operation (cf. aes_fips197_bridge.ml for the analogous AES
// bridge; this is the GHASH side of plan §4.3).
//
// ===========================================================================

        .text
        .globl  gcm_gmult_x86
        .type   gcm_gmult_x86,@function
        .align  16
gcm_gmult_x86:

        // --- Load inputs ---------------------------------------------------
        vmovdqu   (%rdx),%xmm5               // bswap_mask
        vmovdqu   (%rsi),%xmm2               // H (twisted + byte-reversed)
        vmovdqu   (%rdi),%xmm0               // Xi (hardware XMM layout)

        // --- Bring Xi into GHASH polyval-orientation via byte-reversal -----
        vpshufb   %xmm5,%xmm0,%xmm0

        // --- Karatsuba set-up ---------------------------------------------
        // xmm0 = Xi, xmm2 = H, and we need:
        //   xmm1 = Xi  (for the hi*hi multiply)
        //   xmm3 = karatsuba_mid(Xi) : lo half = lo(Xi)^hi(Xi)
        //   xmm4 = karatsuba_mid(H)  : lo half = lo(H)^hi(H)
        vmovdqa   %xmm0,%xmm1                // save Xi for hi*hi
        vpalignr  $8,%xmm0,%xmm0,%xmm3       // swap 64-bit halves of Xi
        vpxor     %xmm0,%xmm3,%xmm3          // xmm3 = Xi XOR swap(Xi)
        vpalignr  $8,%xmm2,%xmm2,%xmm4       // swap 64-bit halves of H
        vpxor     %xmm2,%xmm4,%xmm4          // xmm4 = H  XOR swap(H)

        // --- Schoolbook Karatsuba: 3 64x64 multiplies ----------------------
        vpclmulqdq $0x00,%xmm2,%xmm0,%xmm0   // xmm0 = lo(Xi) * lo(H)
        vpclmulqdq $0x11,%xmm2,%xmm1,%xmm1   // xmm1 = hi(Xi) * hi(H)
        vpclmulqdq $0x00,%xmm4,%xmm3,%xmm3   // xmm3 = lo_mid(Xi) * lo_mid(H)
        vpxor     %xmm0,%xmm3,%xmm3          // xmm3 -= lo*lo
        vpxor     %xmm1,%xmm3,%xmm3          // xmm3 -= hi*hi
                                             // (so xmm3 now holds the
                                             //  middle cross-term
                                             //  lo*hi XOR hi*lo)

        // --- Karatsuba recombine: place xmm3 halves back into xmm1:xmm0 ---
        vmovdqa   %xmm3,%xmm4
        vpsrldq   $8,%xmm3,%xmm3             // hi half of xmm3 shifted low
        vpslldq   $8,%xmm4,%xmm4             // lo half of xmm3 shifted high
        vpxor     %xmm3,%xmm1,%xmm1          // xmm1 ^= hi half of mid
        vpxor     %xmm4,%xmm0,%xmm0          // xmm0 ^= lo half of mid
        //    now xmm1:xmm0 = 256-bit product Xi*H (carryless, polynomial)

        // --- Lazy reduction mod Q(x) = x^128 + x^127 + x^126 + x^121 + 1,
        //     step 1: fold the low 128 bits back into xmm1.
        vmovdqa   %xmm0,%xmm4                // save xmm0
        vmovdqa   %xmm0,%xmm3
        vpsllq    $5,%xmm0,%xmm0
        vpxor     %xmm0,%xmm3,%xmm3
        vpsllq    $1,%xmm0,%xmm0
        vpxor     %xmm3,%xmm0,%xmm0
        vpsllq    $57,%xmm0,%xmm0
        vmovdqa   %xmm0,%xmm3
        vpslldq   $8,%xmm0,%xmm0
        vpsrldq   $8,%xmm3,%xmm3
        vpxor     %xmm4,%xmm0,%xmm0
        vpxor     %xmm3,%xmm1,%xmm1

        // --- Lazy reduction step 2: fold again to get a 128-bit result ----
        vmovdqa   %xmm0,%xmm4
        vpsrlq    $1,%xmm0,%xmm0
        vpxor     %xmm4,%xmm1,%xmm1
        vpxor     %xmm0,%xmm4,%xmm4
        vpsrlq    $5,%xmm0,%xmm0
        vpxor     %xmm4,%xmm0,%xmm0
        vpsrlq    $1,%xmm0,%xmm0
        vpxor     %xmm1,%xmm0,%xmm0          // xmm0 = polyval_dot(Xi, H)
                                             //   in GHASH orientation

        // --- Bring back to hardware XMM layout and store -------------------
        vpshufb   %xmm5,%xmm0,%xmm0
        vmovdqu   %xmm0,(%rdi)

        ret
        .size   gcm_gmult_x86,.-gcm_gmult_x86
