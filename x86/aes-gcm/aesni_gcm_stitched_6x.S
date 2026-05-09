// ===========================================================================
// Stitched 6-way AES-128-CTR + GHASH loop body, standalone-artefact form.
//
// Milestone 7 of the AES-GCM x86 verification plan.  Produced from the
// `.Loop6x__aesni_gcm_encrypt_aesni_ctr32_ghash_6x_0` body of
// `aesni_gcm_encrypt.S` by `tools/extract_stitched_6x.py`: retain every VEX
// SIMD instruction on the fast path (AES-128, no CTR32 wrap, more-blocks
// remain), drop the interleaved scalar plumbing that only updates state for
// the NEXT iteration, and rewrite the post-leaq rsi-offsets to positive form.
//
// ABI (System V):
//   %rdi  plaintext pointer       (6 blocks at rdi+{0,16,..,80})
//   %rsi  ciphertext pointer      (6 blocks at rsi+{0,16,..,80})
//   %rcx  key schedule - 128      (k_i at (16*i - 128)(%rcx))
//   %r9   Htable + 32             (H-power i at (16*i - 32)(%r9))
//   %r8   counter-block output    (16 bytes, inc32^6 icb after body)
//   %r11  constants pointer       (16(%r11)=reduction poly, 32(%r11)=+1)
//
// Entry register state (per the original `.Loop6x` entry fan-out):
//   xmm9  = k0 XOR counter lane 0
//   xmm10..xmm14 = counter lanes 1..5 (pre-AddRoundKey)
//   xmm15 = k0 (round-0 key)
//   xmm7  = GHASH high-half accumulator (prior iter)
//   xmm8  = GHASH low-half accumulator  (prior iter)
//   xmm4  = prior-iter reduction residue
//   xmm2  = +1 constant for counter increment
//   stack 16..112(%rsp) = prior-iter ciphertext blocks for GHASH
//
// Exit state (after the 6 ciphertext stores):
//   memory at rsi+{0,16,..,80} = 6 ciphertext blocks
//   memory at (%r8)            = inc32^6 icb (new counter block)
//   xmm4..xmm8                 = new GHASH register halves
// ===========================================================================

        .text
        .globl  aesni_gcm_stitched_6x_core
        .type   aesni_gcm_stitched_6x_core,@function
        .align  16
aesni_gcm_stitched_6x_core:

        // --- region pre-resume : source lines 313-316 ---
        vmovdqu	0-32(%r9),%xmm3
        vpaddb	%xmm2,%xmm14,%xmm1
        vpxor	%xmm15,%xmm10,%xmm10
        vpxor	%xmm15,%xmm11,%xmm11

        // --- region resume-body : source lines 319-499 ---
        vmovdqu	%xmm1,(%r8)
        vpclmulqdq	$0x10,%xmm3,%xmm7,%xmm5
        vpxor	%xmm15,%xmm12,%xmm12
        vmovdqu	16-128(%rcx),%xmm2
        vpclmulqdq	$0x01,%xmm3,%xmm7,%xmm6
        vaesenc	%xmm2,%xmm9,%xmm9
        vmovdqu	48(%rsp),%xmm0
        vpxor	%xmm15,%xmm13,%xmm13
        vpclmulqdq	$0x00,%xmm3,%xmm7,%xmm1
        vaesenc	%xmm2,%xmm10,%xmm10
        vpxor	%xmm15,%xmm14,%xmm14
        vpclmulqdq	$0x11,%xmm3,%xmm7,%xmm7
        vaesenc	%xmm2,%xmm11,%xmm11
        vmovdqu	16-32(%r9),%xmm3
        vaesenc	%xmm2,%xmm12,%xmm12
        vpxor	%xmm5,%xmm6,%xmm6
        vpclmulqdq	$0x00,%xmm3,%xmm0,%xmm5
        vpxor	%xmm4,%xmm8,%xmm8
        vaesenc	%xmm2,%xmm13,%xmm13
        vpxor	%xmm5,%xmm1,%xmm4
        vmovdqu	32-128(%rcx),%xmm15
        vpclmulqdq	$0x10,%xmm3,%xmm0,%xmm1
        vaesenc	%xmm2,%xmm14,%xmm14
        vpclmulqdq	$0x01,%xmm3,%xmm0,%xmm2
        vaesenc	%xmm15,%xmm9,%xmm9
        vpxor	16(%rsp),%xmm8,%xmm8
        vpclmulqdq	$0x11,%xmm3,%xmm0,%xmm3
        vmovdqu	64(%rsp),%xmm0
        vaesenc	%xmm15,%xmm10,%xmm10
        vaesenc	%xmm15,%xmm11,%xmm11
        vaesenc	%xmm15,%xmm12,%xmm12
        vaesenc	%xmm15,%xmm13,%xmm13
        vmovdqu	48-32(%r9),%xmm5
        vaesenc	%xmm15,%xmm14,%xmm14
        vmovdqu	48-128(%rcx),%xmm15
        vpxor	%xmm1,%xmm6,%xmm6
        vpclmulqdq	$0x00,%xmm5,%xmm0,%xmm1
        vaesenc	%xmm15,%xmm9,%xmm9
        vpxor	%xmm2,%xmm6,%xmm6
        vpclmulqdq	$0x10,%xmm5,%xmm0,%xmm2
        vaesenc	%xmm15,%xmm10,%xmm10
        vpxor	%xmm3,%xmm7,%xmm7
        vpclmulqdq	$0x01,%xmm5,%xmm0,%xmm3
        vaesenc	%xmm15,%xmm11,%xmm11
        vpclmulqdq	$0x11,%xmm5,%xmm0,%xmm5
        vmovdqu	80(%rsp),%xmm0
        vaesenc	%xmm15,%xmm12,%xmm12
        vaesenc	%xmm15,%xmm13,%xmm13
        vpxor	%xmm1,%xmm4,%xmm4
        vmovdqu	64-32(%r9),%xmm1
        vaesenc	%xmm15,%xmm14,%xmm14
        vmovdqu	64-128(%rcx),%xmm15
        vpxor	%xmm2,%xmm6,%xmm6
        vpclmulqdq	$0x00,%xmm1,%xmm0,%xmm2
        vaesenc	%xmm15,%xmm9,%xmm9
        vpxor	%xmm3,%xmm6,%xmm6
        vpclmulqdq	$0x10,%xmm1,%xmm0,%xmm3
        vaesenc	%xmm15,%xmm10,%xmm10
        vpxor	%xmm5,%xmm7,%xmm7
        vpclmulqdq	$0x01,%xmm1,%xmm0,%xmm5
        vaesenc	%xmm15,%xmm11,%xmm11
        vpclmulqdq	$0x11,%xmm1,%xmm0,%xmm1
        vmovdqu	96(%rsp),%xmm0
        vaesenc	%xmm15,%xmm12,%xmm12
        vaesenc	%xmm15,%xmm13,%xmm13
        vpxor	%xmm2,%xmm4,%xmm4
        vmovdqu	96-32(%r9),%xmm2
        vaesenc	%xmm15,%xmm14,%xmm14
        vmovdqu	80-128(%rcx),%xmm15
        vpxor	%xmm3,%xmm6,%xmm6
        vpclmulqdq	$0x00,%xmm2,%xmm0,%xmm3
        vaesenc	%xmm15,%xmm9,%xmm9
        vpxor	%xmm5,%xmm6,%xmm6
        vpclmulqdq	$0x10,%xmm2,%xmm0,%xmm5
        vaesenc	%xmm15,%xmm10,%xmm10
        vpxor	%xmm1,%xmm7,%xmm7
        vpclmulqdq	$0x01,%xmm2,%xmm0,%xmm1
        vpxor	112(%rsp),%xmm8,%xmm8
        vaesenc	%xmm15,%xmm11,%xmm11
        vpclmulqdq	$0x11,%xmm2,%xmm0,%xmm2
        vaesenc	%xmm15,%xmm12,%xmm12
        vaesenc	%xmm15,%xmm13,%xmm13
        vpxor	%xmm3,%xmm4,%xmm4
        vmovdqu	112-32(%r9),%xmm3
        vaesenc	%xmm15,%xmm14,%xmm14
        vmovdqu	96-128(%rcx),%xmm15
        vpxor	%xmm5,%xmm6,%xmm6
        vpclmulqdq	$0x10,%xmm3,%xmm8,%xmm5
        vaesenc	%xmm15,%xmm9,%xmm9
        vpxor	%xmm1,%xmm6,%xmm6
        vpclmulqdq	$0x01,%xmm3,%xmm8,%xmm1
        vaesenc	%xmm15,%xmm10,%xmm10
        vpxor	%xmm2,%xmm7,%xmm7
        vpclmulqdq	$0x00,%xmm3,%xmm8,%xmm2
        vaesenc	%xmm15,%xmm11,%xmm11
        vpclmulqdq	$0x11,%xmm3,%xmm8,%xmm8
        vaesenc	%xmm15,%xmm12,%xmm12
        vaesenc	%xmm15,%xmm13,%xmm13
        vpxor	%xmm5,%xmm6,%xmm6
        vaesenc	%xmm15,%xmm14,%xmm14
        vpxor	%xmm1,%xmm6,%xmm6
        vmovdqu	112-128(%rcx),%xmm15
        vpslldq	$8,%xmm6,%xmm5
        vpxor	%xmm2,%xmm4,%xmm4
        vmovdqu	16(%r11),%xmm3
        vaesenc	%xmm15,%xmm9,%xmm9
        vpxor	%xmm8,%xmm7,%xmm7
        vaesenc	%xmm15,%xmm10,%xmm10
        vpxor	%xmm5,%xmm4,%xmm4
        vaesenc	%xmm15,%xmm11,%xmm11
        vpalignr	$8,%xmm4,%xmm4,%xmm0
        vpclmulqdq	$0x10,%xmm3,%xmm4,%xmm4
        vaesenc	%xmm15,%xmm12,%xmm12
        vaesenc	%xmm15,%xmm13,%xmm13
        vmovdqu	128-128(%rcx),%xmm1
        vaesenc	%xmm15,%xmm14,%xmm14
        vaesenc	%xmm1,%xmm9,%xmm9
        vmovdqu	144-128(%rcx),%xmm15
        vaesenc	%xmm1,%xmm10,%xmm10
        vpsrldq	$8,%xmm6,%xmm6
        vaesenc	%xmm1,%xmm11,%xmm11
        vpxor	%xmm6,%xmm7,%xmm7
        vaesenc	%xmm1,%xmm12,%xmm12
        vpxor	%xmm0,%xmm4,%xmm4
        vaesenc	%xmm1,%xmm13,%xmm13
        vaesenc	%xmm1,%xmm14,%xmm14
        vmovdqu	160-128(%rcx),%xmm1

        // --- region enc-tail : source lines 561-597 ---
        vaesenc	%xmm15,%xmm9,%xmm9
        vmovdqu	%xmm7,16(%rsp)
        vpalignr	$8,%xmm4,%xmm4,%xmm8
        vaesenc	%xmm15,%xmm10,%xmm10
        vpclmulqdq	$0x10,%xmm3,%xmm4,%xmm4
        vpxor	0(%rdi),%xmm1,%xmm2
        vaesenc	%xmm15,%xmm11,%xmm11
        vpxor	16(%rdi),%xmm1,%xmm0
        vaesenc	%xmm15,%xmm12,%xmm12
        vpxor	32(%rdi),%xmm1,%xmm5
        vaesenc	%xmm15,%xmm13,%xmm13
        vpxor	48(%rdi),%xmm1,%xmm6
        vaesenc	%xmm15,%xmm14,%xmm14
        vpxor	64(%rdi),%xmm1,%xmm7
        vpxor	80(%rdi),%xmm1,%xmm3
        vmovdqu	(%r8),%xmm1
        vaesenclast	%xmm2,%xmm9,%xmm9
        vmovdqu	32(%r11),%xmm2
        vaesenclast	%xmm0,%xmm10,%xmm10
        vpaddb	%xmm2,%xmm1,%xmm0
        leaq	96(%rdi),%rdi
        vaesenclast	%xmm5,%xmm11,%xmm11
        vpaddb	%xmm2,%xmm0,%xmm5
        leaq	96(%rsi),%rsi
        vmovdqu	0-128(%rcx),%xmm15
        vaesenclast	%xmm6,%xmm12,%xmm12
        vpaddb	%xmm2,%xmm5,%xmm6
        vaesenclast	%xmm7,%xmm13,%xmm13
        vpaddb	%xmm2,%xmm6,%xmm7
        vaesenclast	%xmm3,%xmm14,%xmm14
        vpaddb	%xmm2,%xmm7,%xmm3

        // --- region ciphertext-stores : source lines 603-613 ---
        vmovdqu	%xmm9,-96(%rsi)
        vmovdqu	%xmm10,-80(%rsi)
        vmovdqu	%xmm11,-64(%rsi)
        vmovdqu	%xmm12,-48(%rsi)
        vmovdqu	%xmm13,-32(%rsi)
        vmovdqu	%xmm14,-16(%rsi)

        ret
        .size   aesni_gcm_stitched_6x_core,.-aesni_gcm_stitched_6x_core
