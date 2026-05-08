// ===========================================================================
// 6-way AES-128-CTR body as a standalone, single-entry routine.
//
// Milestone 5 of the AES-GCM x86 verification plan.  This is the AES round
// chain of aws-lc's `_aesni_ctr32_6x` helper, packaged as a proof artefact:
//
//   - The CTR-IV setup and byte-reversal have been lifted to the caller,
//     which hands in 6 already-byte-reversed counter lanes in a 96-byte
//     buffer (each lane is a 16-byte counter block in hardware XMM order,
//     i.e. low 96 bits = nonce, high 32 bits = little-endian image of the
//     big-endian wire counter, matching how `.Loop_ctr32` sees the state
//     after the leading `vpaddb .Ltwo_lsb` / `vpshufb .Lbswap_mask` chain).
//   - The "carry in the low-32-bits" path (`.Lhandle_ctr32_2`) is omitted:
//     the caller guarantees the CTR32 sequence it supplies does not wrap.
//     For the GCM encrypt path this is justified by the 100663296 probe
//     check (aws-lc uses `addl $100663296,%ebx ; jc .Lhandle_ctr32_2`).
//   - Key size is fixed to AES-128 (10 rounds) and the middle-round loop
//     is fully unrolled.  AES-256 is a later-milestone generalisation.
//
// System V ABI:
//     rdi = input pointer  (96 bytes, 6 plaintext blocks)
//     rsi = output pointer (96 bytes, 6 ciphertext blocks)
//     rdx = key-schedule pointer (176 bytes, 11 round keys k0..k10
//                                 in natural ascending order)
//     rcx = counter-lanes pointer (96 bytes, 6 pre-shuffled counter
//                                  blocks icb0..icb5 in hardware
//                                  XMM byte order)
//
// Correctness: for each lane i in {0,...,5},
//     output[i*16..i*16+16] = aes128_cipher(icb_i, k0..k10) XOR input[i*16..]
// (modulo the standard `word_reversefields 8` endianness bridge between
// `fips197`-spec and XMM-native layouts — see aes_fips197_bridge.ml).
//
// Extracted from aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/
// aesni-gcm-x86_64.S  (commit 2ddb1c333f25f0288e8413d32b30260da3802157),
// procedure `_aesni_ctr32_6x`, fast-path only.
// ===========================================================================

        .text
        .globl  aesni_ctr32_6x_core
        .type   aesni_ctr32_6x_core,@function
        .align  16
aesni_ctr32_6x_core:

        // --- Counter-lane setup (initial AddRoundKey = XOR with k0) --------
        vmovdqu   0(%rdx),%xmm4                // k0
        vmovdqu   0(%rcx),%xmm9                // icb0
        vpxor     %xmm4,%xmm9,%xmm9            // icb0 ^ k0
        vmovdqu   16(%rcx),%xmm10              // icb1
        vpxor     %xmm4,%xmm10,%xmm10
        vmovdqu   32(%rcx),%xmm11              // icb2
        vpxor     %xmm4,%xmm11,%xmm11
        vmovdqu   48(%rcx),%xmm12              // icb3
        vpxor     %xmm4,%xmm12,%xmm12
        vmovdqu   64(%rcx),%xmm13              // icb4
        vpxor     %xmm4,%xmm13,%xmm13
        vmovdqu   80(%rcx),%xmm14              // icb5
        vpxor     %xmm4,%xmm14,%xmm14

        // --- 9 middle rounds: vaesenc with k1..k9 --------------------------
        vmovdqu   16(%rdx),%xmm15              // k1
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   32(%rdx),%xmm15              // k2
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   48(%rdx),%xmm15              // k3
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   64(%rdx),%xmm15              // k4
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   80(%rdx),%xmm15              // k5
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   96(%rdx),%xmm15              // k6
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   112(%rdx),%xmm15             // k7
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   128(%rdx),%xmm15             // k8
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        vmovdqu   144(%rdx),%xmm15             // k9
        vaesenc   %xmm15,%xmm9,%xmm9
        vaesenc   %xmm15,%xmm10,%xmm10
        vaesenc   %xmm15,%xmm11,%xmm11
        vaesenc   %xmm15,%xmm12,%xmm12
        vaesenc   %xmm15,%xmm13,%xmm13
        vaesenc   %xmm15,%xmm14,%xmm14

        // --- Final round: vaesenclast folds in the CTR-mode input XOR -----
        vmovdqu   160(%rdx),%xmm3              // k10
        vpxor     0(%rdi),%xmm3,%xmm4          // k10 ^ in0
        vpxor     16(%rdi),%xmm3,%xmm5
        vpxor     32(%rdi),%xmm3,%xmm6
        vpxor     48(%rdi),%xmm3,%xmm8
        vpxor     64(%rdi),%xmm3,%xmm2
        vpxor     80(%rdi),%xmm3,%xmm3
        vaesenclast %xmm4,%xmm9,%xmm9          // aes_out0 XOR k10 XOR in0
        vaesenclast %xmm5,%xmm10,%xmm10
        vaesenclast %xmm6,%xmm11,%xmm11
        vaesenclast %xmm8,%xmm12,%xmm12
        vaesenclast %xmm2,%xmm13,%xmm13
        vaesenclast %xmm3,%xmm14,%xmm14

        // --- Store 6 ciphertext blocks ------------------------------------
        vmovdqu   %xmm9,0(%rsi)
        vmovdqu   %xmm10,16(%rsi)
        vmovdqu   %xmm11,32(%rsi)
        vmovdqu   %xmm12,48(%rsi)
        vmovdqu   %xmm13,64(%rsi)
        vmovdqu   %xmm14,80(%rsi)

        ret
        .size   aesni_ctr32_6x_core,.-aesni_ctr32_6x_core
