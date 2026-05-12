// ===========================================================================
// Stitched 6-way GHASH finalisation tail, standalone-artefact form.
//
// Milestone 9 of the AES-GCM x86 verification plan.  Extracted from the
// .L6x_done__...  .Lexit__... blocks of aesni_gcm_encrypt.S (source lines
// 618-799) by tools/extract_stitched_tail.py: keep every SIMD instruction
// + the movq 16(%rbp),%r12 that loads the tag-output pointer.  The
// `jmp .Lexit` at line 622 is elided (fall-through into the same code).
//
// ABI at entry (inherited from the bulk loop's exit):
//   %rdi  = iptr + 96*iter_count         (unused by tail, consumed by
//                                         the enclosing function's
//                                         epilogue)
//   %rsi  = optr + 96*iter_count         (the 6 vmovdqu %xmmK,-N(%rsi)
//                                         stores write the last iter's
//                                         ciphertext lanes)
//   %rcx  = key schedule - 128
//   %r9   = Htable + 32
//   %r8   = counter-block output
//   %r11  = constants ptr (bswap/reduction/+1)
//   %rbp  = saved frame ptr; 16(%rbp) = tag-output pointer
//   %rsp  = sptr                         (16(%rsp) = ghash-lo stash;
//                                         32..112(%rsp) = last-iter
//                                         plaintext stash)
//   xmm4  = last-iter Karatsuba residue
//   xmm7  = last-iter Karatsuba accumulator high
//   xmm8  = last-iter Karatsuba accumulator low
//   xmm9..xmm14 = last-iter 6 ciphertext lanes (post-vaesenclast)
//   xmm15 = k0 (round-0 key)
//
// Exit state:
//   mem at 16(%rbp)-resolved tag ptr = final GHASH tag
//   mem at -96(%rsi)..-16(%rsi) = 6 ciphertext lanes (also subsumed by
//                                  the outer ct_preserved invariant)
// ===========================================================================

        .text
        .globl  aesni_gcm_stitched_tail_core
        .type   aesni_gcm_stitched_tail_core,@function
        .align  16
aesni_gcm_stitched_tail_core:

        vpxor	16(%rsp),%xmm8,%xmm8
        vpxor	%xmm4,%xmm8,%xmm8
        vmovdqu	32(%rsp),%xmm7
        vmovdqu	(%r11),%xmm0
        vmovdqu	0-32(%r9),%xmm3
        vpunpckhqdq	%xmm7,%xmm7,%xmm1
        vmovdqu	32-32(%r9),%xmm15
        vmovdqu	%xmm9,-96(%rsi)
        vpshufb	%xmm0,%xmm9,%xmm9
        vpxor	%xmm7,%xmm1,%xmm1
        vmovdqu	%xmm10,-80(%rsi)
        vpshufb	%xmm0,%xmm10,%xmm10
        vmovdqu	%xmm11,-64(%rsi)
        vpshufb	%xmm0,%xmm11,%xmm11
        vmovdqu	%xmm12,-48(%rsi)
        vpshufb	%xmm0,%xmm12,%xmm12
        vmovdqu	%xmm13,-32(%rsi)
        vpshufb	%xmm0,%xmm13,%xmm13
        vmovdqu	%xmm14,-16(%rsi)
        vpshufb	%xmm0,%xmm14,%xmm14
        vmovdqu	%xmm9,16(%rsp)
        vmovdqu	48(%rsp),%xmm6
        vmovdqu	16-32(%r9),%xmm0
        vpunpckhqdq	%xmm6,%xmm6,%xmm2
        vpclmulqdq	$0x00,%xmm3,%xmm7,%xmm5
        vpxor	%xmm6,%xmm2,%xmm2
        vpclmulqdq	$0x11,%xmm3,%xmm7,%xmm7
        vpclmulqdq	$0x00,%xmm15,%xmm1,%xmm1
        vmovdqu	64(%rsp),%xmm9
        vpclmulqdq	$0x00,%xmm0,%xmm6,%xmm4
        vmovdqu	48-32(%r9),%xmm3
        vpxor	%xmm5,%xmm4,%xmm4
        vpunpckhqdq	%xmm9,%xmm9,%xmm5
        vpclmulqdq	$0x11,%xmm0,%xmm6,%xmm6
        vpxor	%xmm9,%xmm5,%xmm5
        vpxor	%xmm7,%xmm6,%xmm6
        vpclmulqdq	$0x10,%xmm15,%xmm2,%xmm2
        vmovdqu	80-32(%r9),%xmm15
        vpxor	%xmm1,%xmm2,%xmm2
        vmovdqu	80(%rsp),%xmm1
        vpclmulqdq	$0x00,%xmm3,%xmm9,%xmm7
        vmovdqu	64-32(%r9),%xmm0
        vpxor	%xmm4,%xmm7,%xmm7
        vpunpckhqdq	%xmm1,%xmm1,%xmm4
        vpclmulqdq	$0x11,%xmm3,%xmm9,%xmm9
        vpxor	%xmm1,%xmm4,%xmm4
        vpxor	%xmm6,%xmm9,%xmm9
        vpclmulqdq	$0x00,%xmm15,%xmm5,%xmm5
        vpxor	%xmm2,%xmm5,%xmm5
        vmovdqu	96(%rsp),%xmm2
        vpclmulqdq	$0x00,%xmm0,%xmm1,%xmm6
        vmovdqu	96-32(%r9),%xmm3
        vpxor	%xmm7,%xmm6,%xmm6
        vpunpckhqdq	%xmm2,%xmm2,%xmm7
        vpclmulqdq	$0x11,%xmm0,%xmm1,%xmm1
        vpxor	%xmm2,%xmm7,%xmm7
        vpxor	%xmm9,%xmm1,%xmm1
        vpclmulqdq	$0x10,%xmm15,%xmm4,%xmm4
        vmovdqu	128-32(%r9),%xmm15
        vpxor	%xmm5,%xmm4,%xmm4
        vpxor	112(%rsp),%xmm8,%xmm8
        vpclmulqdq	$0x00,%xmm3,%xmm2,%xmm5
        vmovdqu	112-32(%r9),%xmm0
        vpunpckhqdq	%xmm8,%xmm8,%xmm9
        vpxor	%xmm6,%xmm5,%xmm5
        vpclmulqdq	$0x11,%xmm3,%xmm2,%xmm2
        vpxor	%xmm8,%xmm9,%xmm9
        vpxor	%xmm1,%xmm2,%xmm2
        vpclmulqdq	$0x00,%xmm15,%xmm7,%xmm7
        vpxor	%xmm4,%xmm7,%xmm4
        vpclmulqdq	$0x00,%xmm0,%xmm8,%xmm6
        vmovdqu	0-32(%r9),%xmm3
        vpunpckhqdq	%xmm14,%xmm14,%xmm1
        vpclmulqdq	$0x11,%xmm0,%xmm8,%xmm8
        vpxor	%xmm14,%xmm1,%xmm1
        vpxor	%xmm5,%xmm6,%xmm5
        vpclmulqdq	$0x10,%xmm15,%xmm9,%xmm9
        vmovdqu	32-32(%r9),%xmm15
        vpxor	%xmm2,%xmm8,%xmm7
        vpxor	%xmm4,%xmm9,%xmm6
        vmovdqu	16-32(%r9),%xmm0
        vpxor	%xmm5,%xmm7,%xmm9
        vpclmulqdq	$0x00,%xmm3,%xmm14,%xmm4
        vpxor	%xmm9,%xmm6,%xmm6
        vpunpckhqdq	%xmm13,%xmm13,%xmm2
        vpclmulqdq	$0x11,%xmm3,%xmm14,%xmm14
        vpxor	%xmm13,%xmm2,%xmm2
        vpslldq	$8,%xmm6,%xmm9
        vpclmulqdq	$0x00,%xmm15,%xmm1,%xmm1
        vpxor	%xmm9,%xmm5,%xmm8
        vpsrldq	$8,%xmm6,%xmm6
        vpxor	%xmm6,%xmm7,%xmm7
        vpclmulqdq	$0x00,%xmm0,%xmm13,%xmm5
        vmovdqu	48-32(%r9),%xmm3
        vpxor	%xmm4,%xmm5,%xmm5
        vpunpckhqdq	%xmm12,%xmm12,%xmm9
        vpclmulqdq	$0x11,%xmm0,%xmm13,%xmm13
        vpxor	%xmm12,%xmm9,%xmm9
        vpxor	%xmm14,%xmm13,%xmm13
        vpalignr	$8,%xmm8,%xmm8,%xmm14
        vpclmulqdq	$0x10,%xmm15,%xmm2,%xmm2
        vmovdqu	80-32(%r9),%xmm15
        vpxor	%xmm1,%xmm2,%xmm2
        vpclmulqdq	$0x00,%xmm3,%xmm12,%xmm4
        vmovdqu	64-32(%r9),%xmm0
        vpxor	%xmm5,%xmm4,%xmm4
        vpunpckhqdq	%xmm11,%xmm11,%xmm1
        vpclmulqdq	$0x11,%xmm3,%xmm12,%xmm12
        vpxor	%xmm11,%xmm1,%xmm1
        vpxor	%xmm13,%xmm12,%xmm12
        vpxor	16(%rsp),%xmm7,%xmm7
        vpclmulqdq	$0x00,%xmm15,%xmm9,%xmm9
        vpxor	%xmm2,%xmm9,%xmm9
        vpclmulqdq	$0x10,16(%r11),%xmm8,%xmm8
        vpxor	%xmm14,%xmm8,%xmm8
        vpclmulqdq	$0x00,%xmm0,%xmm11,%xmm5
        vmovdqu	96-32(%r9),%xmm3
        vpxor	%xmm4,%xmm5,%xmm5
        vpunpckhqdq	%xmm10,%xmm10,%xmm2
        vpclmulqdq	$0x11,%xmm0,%xmm11,%xmm11
        vpxor	%xmm10,%xmm2,%xmm2
        vpalignr	$8,%xmm8,%xmm8,%xmm14
        vpxor	%xmm12,%xmm11,%xmm11
        vpclmulqdq	$0x10,%xmm15,%xmm1,%xmm1
        vmovdqu	128-32(%r9),%xmm15
        vpxor	%xmm9,%xmm1,%xmm1
        vpxor	%xmm7,%xmm14,%xmm14
        vpclmulqdq	$0x10,16(%r11),%xmm8,%xmm8
        vpxor	%xmm14,%xmm8,%xmm8
        vpclmulqdq	$0x00,%xmm3,%xmm10,%xmm4
        vmovdqu	112-32(%r9),%xmm0
        vpxor	%xmm5,%xmm4,%xmm4
        vpunpckhqdq	%xmm8,%xmm8,%xmm9
        vpclmulqdq	$0x11,%xmm3,%xmm10,%xmm10
        vpxor	%xmm8,%xmm9,%xmm9
        vpxor	%xmm11,%xmm10,%xmm10
        vpclmulqdq	$0x00,%xmm15,%xmm2,%xmm2
        vpxor	%xmm1,%xmm2,%xmm2
        vpclmulqdq	$0x00,%xmm0,%xmm8,%xmm5
        vpclmulqdq	$0x11,%xmm0,%xmm8,%xmm7
        vpxor	%xmm4,%xmm5,%xmm5
        vpclmulqdq	$0x10,%xmm15,%xmm9,%xmm6
        vpxor	%xmm10,%xmm7,%xmm7
        vpxor	%xmm2,%xmm6,%xmm6
        vpxor	%xmm5,%xmm7,%xmm4
        vpxor	%xmm4,%xmm6,%xmm6
        vpslldq	$8,%xmm6,%xmm1
        vmovdqu	16(%r11),%xmm3
        vpsrldq	$8,%xmm6,%xmm6
        vpxor	%xmm1,%xmm5,%xmm8
        vpxor	%xmm6,%xmm7,%xmm7
        vpalignr	$8,%xmm8,%xmm8,%xmm2
        vpclmulqdq	$0x10,%xmm3,%xmm8,%xmm8
        vpxor	%xmm2,%xmm8,%xmm8
        vpalignr	$8,%xmm8,%xmm8,%xmm2
        vpclmulqdq	$0x10,%xmm3,%xmm8,%xmm8
        vpxor	%xmm7,%xmm2,%xmm2
        vpxor	%xmm2,%xmm8,%xmm8
        movq	16(%rbp),%r12
        vpshufb	(%r11),%xmm8,%xmm8
        vmovdqu	%xmm8,(%r12)

        ret
        .size   aesni_gcm_stitched_tail_core,.-aesni_gcm_stitched_tail_core
