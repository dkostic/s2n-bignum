// ===========================================================================
// Stitched 6-way AES-128-CTR + GHASH bulk loop, standalone-artefact form.
//
// Milestone 8 of the AES-GCM x86 verification plan.  Wraps Milestone 7's
// `aesni_gcm_stitched_6x_core` body in the `.Loop6x` back-edge of aws-lc's
// aesni_gcm_encrypt.  Produced by `tools/extract_stitched_6x_loop.py`:
// takes M7's 166-instruction filtered fast-path body verbatim, then
// appends the loop-count test (subq/jc), 7 counter-rotation/stash-reload
// instructions, and an unconditional back-edge (jmp).  The body byte
// layout [0, 0x348) is byte-for-byte identical with M7, so M7's theorem
// composes via X86_BIGSTEP_TAC.  The loop-count convention is descending
// by 6 on each iteration, exits on CF set (underflow).
//
// ABI (System V):
//   %rdi  plaintext pointer          (advances by 96 per iter externally;
//                                     in this artefact, plaintext is held
//                                     constant across the loop invariant —
//                                     see M8 proof for the encode of the
//                                     per-iteration pointer offset)
//   %rsi  ciphertext pointer         (same)
//   %rcx  key schedule - 128
//   %r9   Htable + 32
//   %r8   counter-block output
//   %r11  constants pointer
//   %rdx  remaining 16-byte blocks (decremented by 6 each iter, exit on CF)
// ===========================================================================

        .text
        .globl  aesni_gcm_stitched_6x_loop_core
        .type   aesni_gcm_stitched_6x_loop_core,@function
        .align  16
aesni_gcm_stitched_6x_loop_core:


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
        vaesenclast	%xmm5,%xmm11,%xmm11
        vpaddb	%xmm2,%xmm0,%xmm5
        vmovdqu	0-128(%rcx),%xmm15
        vaesenclast	%xmm6,%xmm12,%xmm12
        vpaddb	%xmm2,%xmm5,%xmm6
        vaesenclast	%xmm7,%xmm13,%xmm13
        vpaddb	%xmm2,%xmm6,%xmm7
        vaesenclast	%xmm3,%xmm14,%xmm14
        vpaddb	%xmm2,%xmm7,%xmm3

        // --- region ciphertext-stores : source lines 603-613 ---
        vmovdqu	%xmm9,0(%rsi)
        vmovdqu	%xmm10,16(%rsi)
        vmovdqu	%xmm11,32(%rsi)
        vmovdqu	%xmm12,48(%rsi)
        vmovdqu	%xmm13,64(%rsi)
        vmovdqu	%xmm14,80(%rsi)

        // --- region back-edge : loop plumbing ---
        subq    $0x6, %rdx
        jc      .Ldone_exit
        vpxor   %xmm15,%xmm1,%xmm9
        vmovdqa %xmm0,%xmm10
        vmovdqa %xmm5,%xmm11
        vmovdqa %xmm6,%xmm12
        vmovdqa %xmm7,%xmm13
        vmovdqa %xmm3,%xmm14
        vmovdqu 0x20(%rsp),%xmm7
        jmp     aesni_gcm_stitched_6x_loop_core

.Ldone_exit:
        ret
        .size   aesni_gcm_stitched_6x_loop_core,.-aesni_gcm_stitched_6x_loop_core
