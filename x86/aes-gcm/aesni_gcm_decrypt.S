// This file is generated from a similarly-named Perl script in the BoringSSL
// source tree. Do not edit by hand.

#include <openssl/asm_base.h>

#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_X86_64) && defined(__ELF__)
.text	

// --------------------------------------------------------------------------
// aesni_gcm_decrypt: monolithic, single-entry form.
//
// Produced by tools/inline_x86_calls.py from the aws-lc source at
// crypto/fipsmodule/aesni-gcm-x86_64.S.  Semantics preserved; the
// private helpers _aesni_ctr32_ghash_6x / _aesni_ctr32_6x have been
// spliced inline at each call site with per-site label renaming, and
// every legacy-SSE-domain 128-bit unaligned move rewritten to vmovdqu
// (functionally equivalent; see aes-gcm-x86-plan.md §§2.3, 3.1).
// --------------------------------------------------------------------------

.globl	aesni_gcm_decrypt
.hidden aesni_gcm_decrypt
.type	aesni_gcm_decrypt,@function
.align	32
aesni_gcm_decrypt:
.cfi_startproc	

_CET_ENDBR
	xorq	%rax,%rax



	cmpq	$0x60,%rdx
	jb	.Lgcm_dec_abort

	pushq	%rbp
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbp,-16

	movq	%rsp,%rbp
.cfi_def_cfa_register	%rbp
	pushq	%rbx
.cfi_offset	%rbx,-24

	pushq	%r12
.cfi_offset	%r12,-32

	pushq	%r13
.cfi_offset	%r13,-40

	pushq	%r14
.cfi_offset	%r14,-48

	pushq	%r15
.cfi_offset	%r15,-56

	vzeroupper

	movq	16(%rbp),%r12
	vmovdqu	(%r8),%xmm1
	addq	$-128,%rsp
	movl	12(%r8),%ebx
	leaq	.Lbswap_mask(%rip),%r11
	leaq	-128(%rcx),%r14
	movq	$0xf80,%r15
	vmovdqu	(%r12),%xmm8
	andq	$-128,%rsp
	vmovdqu	(%r11),%xmm0
	leaq	128(%rcx),%rcx
	leaq	32(%r9),%r9
	movl	240-128(%rcx),%r10d
	vpshufb	%xmm0,%xmm8,%xmm8

	andq	%r15,%r14
	andq	%rsp,%r15
	subq	%r14,%r15
	jc	.Ldec_no_key_aliasing
	cmpq	$768,%r15
	jnc	.Ldec_no_key_aliasing
	subq	%r15,%rsp
.Ldec_no_key_aliasing:

	vmovdqu	80(%rdi),%xmm7
	movq	%rdi,%r14
	vmovdqu	64(%rdi),%xmm4







	leaq	-192(%rdi,%rdx,1),%r15

	vmovdqu	48(%rdi),%xmm5
	shrq	$4,%rdx
	xorq	%rax,%rax
	vmovdqu	32(%rdi),%xmm6
	vpshufb	%xmm0,%xmm7,%xmm7
	vmovdqu	16(%rdi),%xmm2
	vpshufb	%xmm0,%xmm4,%xmm4
	vmovdqu	(%rdi),%xmm3
	vpshufb	%xmm0,%xmm5,%xmm5
	vmovdqu	%xmm4,48(%rsp)
	vpshufb	%xmm0,%xmm6,%xmm6
	vmovdqu	%xmm5,64(%rsp)
	vpshufb	%xmm0,%xmm2,%xmm2
	vmovdqu	%xmm6,80(%rsp)
	vpshufb	%xmm0,%xmm3,%xmm3
	vmovdqu	%xmm2,96(%rsp)
	vmovdqu	%xmm3,112(%rsp)

	// ===== inlined _aesni_ctr32_ghash_6x call #0 =====
	vmovdqu	32(%r11),%xmm2
	subq	$6,%rdx
	vpxor	%xmm4,%xmm4,%xmm4
	vmovdqu	0-128(%rcx),%xmm15
	vpaddb	%xmm2,%xmm1,%xmm10
	vpaddb	%xmm2,%xmm10,%xmm11
	vpaddb	%xmm2,%xmm11,%xmm12
	vpaddb	%xmm2,%xmm12,%xmm13
	vpaddb	%xmm2,%xmm13,%xmm14
	vpxor	%xmm15,%xmm1,%xmm9
	vmovdqu	%xmm4,16(%rsp)
	jmp	.Loop6x__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0

.align	32
.Loop6x__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0:
	addl	$100663296,%ebx
	jc	.Lhandle_ctr32__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0
	vmovdqu	0-32(%r9),%xmm3
	vpaddb	%xmm2,%xmm14,%xmm1
	vpxor	%xmm15,%xmm10,%xmm10
	vpxor	%xmm15,%xmm11,%xmm11

.Lresume_ctr32__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0:
	vmovdqu	%xmm1,(%r8)
	vpclmulqdq	$0x10,%xmm3,%xmm7,%xmm5
	vpxor	%xmm15,%xmm12,%xmm12
	vmovdqu	16-128(%rcx),%xmm2
	vpclmulqdq	$0x01,%xmm3,%xmm7,%xmm6

















	xorq	%r12,%r12
	cmpq	%r14,%r15

	vaesenc	%xmm2,%xmm9,%xmm9
	vmovdqu	48(%rsp),%xmm0
	vpxor	%xmm15,%xmm13,%xmm13
	vpclmulqdq	$0x00,%xmm3,%xmm7,%xmm1
	vaesenc	%xmm2,%xmm10,%xmm10
	vpxor	%xmm15,%xmm14,%xmm14
	setnc	%r12b
	vpclmulqdq	$0x11,%xmm3,%xmm7,%xmm7
	vaesenc	%xmm2,%xmm11,%xmm11
	vmovdqu	16-32(%r9),%xmm3
	negq	%r12
	vaesenc	%xmm2,%xmm12,%xmm12
	vpxor	%xmm5,%xmm6,%xmm6
	vpclmulqdq	$0x00,%xmm3,%xmm0,%xmm5
	vpxor	%xmm4,%xmm8,%xmm8
	vaesenc	%xmm2,%xmm13,%xmm13
	vpxor	%xmm5,%xmm1,%xmm4
	andq	$0x60,%r12
	vmovdqu	32-128(%rcx),%xmm15
	vpclmulqdq	$0x10,%xmm3,%xmm0,%xmm1
	vaesenc	%xmm2,%xmm14,%xmm14

	vpclmulqdq	$0x01,%xmm3,%xmm0,%xmm2
	leaq	(%r14,%r12,1),%r14
	vaesenc	%xmm15,%xmm9,%xmm9
	vpxor	16(%rsp),%xmm8,%xmm8
	vpclmulqdq	$0x11,%xmm3,%xmm0,%xmm3
	vmovdqu	64(%rsp),%xmm0
	vaesenc	%xmm15,%xmm10,%xmm10
	movbeq	88(%r14),%r13
	vaesenc	%xmm15,%xmm11,%xmm11
	movbeq	80(%r14),%r12
	vaesenc	%xmm15,%xmm12,%xmm12
	movq	%r13,32(%rsp)
	vaesenc	%xmm15,%xmm13,%xmm13
	movq	%r12,40(%rsp)
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
	movbeq	72(%r14),%r13
	vpxor	%xmm5,%xmm7,%xmm7
	vpclmulqdq	$0x01,%xmm1,%xmm0,%xmm5
	vaesenc	%xmm15,%xmm11,%xmm11
	movbeq	64(%r14),%r12
	vpclmulqdq	$0x11,%xmm1,%xmm0,%xmm1
	vmovdqu	96(%rsp),%xmm0
	vaesenc	%xmm15,%xmm12,%xmm12
	movq	%r13,48(%rsp)
	vaesenc	%xmm15,%xmm13,%xmm13
	movq	%r12,56(%rsp)
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
	movbeq	56(%r14),%r13
	vpxor	%xmm1,%xmm7,%xmm7
	vpclmulqdq	$0x01,%xmm2,%xmm0,%xmm1
	vpxor	112(%rsp),%xmm8,%xmm8
	vaesenc	%xmm15,%xmm11,%xmm11
	movbeq	48(%r14),%r12
	vpclmulqdq	$0x11,%xmm2,%xmm0,%xmm2
	vaesenc	%xmm15,%xmm12,%xmm12
	movq	%r13,64(%rsp)
	vaesenc	%xmm15,%xmm13,%xmm13
	movq	%r12,72(%rsp)
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
	movbeq	40(%r14),%r13
	vpxor	%xmm2,%xmm7,%xmm7
	vpclmulqdq	$0x00,%xmm3,%xmm8,%xmm2
	vaesenc	%xmm15,%xmm11,%xmm11
	movbeq	32(%r14),%r12
	vpclmulqdq	$0x11,%xmm3,%xmm8,%xmm8
	vaesenc	%xmm15,%xmm12,%xmm12
	movq	%r13,80(%rsp)
	vaesenc	%xmm15,%xmm13,%xmm13
	movq	%r12,88(%rsp)
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
	movbeq	24(%r14),%r13
	vaesenc	%xmm15,%xmm11,%xmm11
	movbeq	16(%r14),%r12
	vpalignr	$8,%xmm4,%xmm4,%xmm0
	vpclmulqdq	$0x10,%xmm3,%xmm4,%xmm4
	movq	%r13,96(%rsp)
	vaesenc	%xmm15,%xmm12,%xmm12
	movq	%r12,104(%rsp)
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
	movbeq	8(%r14),%r13
	vaesenc	%xmm1,%xmm13,%xmm13
	movbeq	0(%r14),%r12
	vaesenc	%xmm1,%xmm14,%xmm14
	vmovdqu	160-128(%rcx),%xmm1
	cmpl	$11,%r10d
	jb	.Lenc_tail__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0

	vaesenc	%xmm15,%xmm9,%xmm9
	vaesenc	%xmm15,%xmm10,%xmm10
	vaesenc	%xmm15,%xmm11,%xmm11
	vaesenc	%xmm15,%xmm12,%xmm12
	vaesenc	%xmm15,%xmm13,%xmm13
	vaesenc	%xmm15,%xmm14,%xmm14

	vaesenc	%xmm1,%xmm9,%xmm9
	vaesenc	%xmm1,%xmm10,%xmm10
	vaesenc	%xmm1,%xmm11,%xmm11
	vaesenc	%xmm1,%xmm12,%xmm12
	vaesenc	%xmm1,%xmm13,%xmm13
	vmovdqu	176-128(%rcx),%xmm15
	vaesenc	%xmm1,%xmm14,%xmm14
	vmovdqu	192-128(%rcx),%xmm1
	je	.Lenc_tail__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0

	vaesenc	%xmm15,%xmm9,%xmm9
	vaesenc	%xmm15,%xmm10,%xmm10
	vaesenc	%xmm15,%xmm11,%xmm11
	vaesenc	%xmm15,%xmm12,%xmm12
	vaesenc	%xmm15,%xmm13,%xmm13
	vaesenc	%xmm15,%xmm14,%xmm14

	vaesenc	%xmm1,%xmm9,%xmm9
	vaesenc	%xmm1,%xmm10,%xmm10
	vaesenc	%xmm1,%xmm11,%xmm11
	vaesenc	%xmm1,%xmm12,%xmm12
	vaesenc	%xmm1,%xmm13,%xmm13
	vmovdqu	208-128(%rcx),%xmm15
	vaesenc	%xmm1,%xmm14,%xmm14
	vmovdqu	224-128(%rcx),%xmm1
	jmp	.Lenc_tail__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0

.align	32
.Lhandle_ctr32__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0:
	vmovdqu	(%r11),%xmm0
	vpshufb	%xmm0,%xmm1,%xmm6
	vmovdqu	48(%r11),%xmm5
	vpaddd	64(%r11),%xmm6,%xmm10
	vpaddd	%xmm5,%xmm6,%xmm11
	vmovdqu	0-32(%r9),%xmm3
	vpaddd	%xmm5,%xmm10,%xmm12
	vpshufb	%xmm0,%xmm10,%xmm10
	vpaddd	%xmm5,%xmm11,%xmm13
	vpshufb	%xmm0,%xmm11,%xmm11
	vpxor	%xmm15,%xmm10,%xmm10
	vpaddd	%xmm5,%xmm12,%xmm14
	vpshufb	%xmm0,%xmm12,%xmm12
	vpxor	%xmm15,%xmm11,%xmm11
	vpaddd	%xmm5,%xmm13,%xmm1
	vpshufb	%xmm0,%xmm13,%xmm13
	vpshufb	%xmm0,%xmm14,%xmm14
	vpshufb	%xmm0,%xmm1,%xmm1
	jmp	.Lresume_ctr32__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0

.align	32
.Lenc_tail__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0:
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
	movq	%r13,112(%rsp)
	leaq	96(%rdi),%rdi

	prefetcht0	512(%rdi)
	prefetcht0	576(%rdi)
	vaesenclast	%xmm5,%xmm11,%xmm11
	vpaddb	%xmm2,%xmm0,%xmm5
	movq	%r12,120(%rsp)
	leaq	96(%rsi),%rsi
	vmovdqu	0-128(%rcx),%xmm15
	vaesenclast	%xmm6,%xmm12,%xmm12
	vpaddb	%xmm2,%xmm5,%xmm6
	vaesenclast	%xmm7,%xmm13,%xmm13
	vpaddb	%xmm2,%xmm6,%xmm7
	vaesenclast	%xmm3,%xmm14,%xmm14
	vpaddb	%xmm2,%xmm7,%xmm3

	addq	$0x60,%rax
	subq	$0x6,%rdx
	jc	.L6x_done__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0

	vmovdqu	%xmm9,-96(%rsi)
	vpxor	%xmm15,%xmm1,%xmm9
	vmovdqu	%xmm10,-80(%rsi)
	vmovdqa	%xmm0,%xmm10
	vmovdqu	%xmm11,-64(%rsi)
	vmovdqa	%xmm5,%xmm11
	vmovdqu	%xmm12,-48(%rsi)
	vmovdqa	%xmm6,%xmm12
	vmovdqu	%xmm13,-32(%rsi)
	vmovdqa	%xmm7,%xmm13
	vmovdqu	%xmm14,-16(%rsi)
	vmovdqa	%xmm3,%xmm14
	vmovdqu	32(%rsp),%xmm7
	jmp	.Loop6x__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0

.L6x_done__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0:
	vpxor	16(%rsp),%xmm8,%xmm8
	vpxor	%xmm4,%xmm8,%xmm8

	jmp	.Lexit__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0
.Lexit__aesni_gcm_decrypt_aesni_ctr32_ghash_6x_0:
	// ===== end inlined _aesni_ctr32_ghash_6x #0 =====

	movq	16(%rbp),%r12
	vmovdqu	%xmm9,-96(%rsi)
	vmovdqu	%xmm10,-80(%rsi)
	vmovdqu	%xmm11,-64(%rsi)
	vmovdqu	%xmm12,-48(%rsi)
	vmovdqu	%xmm13,-32(%rsi)
	vmovdqu	%xmm14,-16(%rsi)

	vpshufb	(%r11),%xmm8,%xmm8
	vmovdqu	%xmm8,(%r12)

	vzeroupper
	leaq	-40(%rbp),%rsp
.cfi_def_cfa	%rsp, 0x38
	popq	%r15
.cfi_adjust_cfa_offset	-8
.cfi_restore	%r15
	popq	%r14
.cfi_adjust_cfa_offset	-8
.cfi_restore	%r14
	popq	%r13
.cfi_adjust_cfa_offset	-8
.cfi_restore	%r13
	popq	%r12
.cfi_adjust_cfa_offset	-8
.cfi_restore	%r12
	popq	%rbx
.cfi_adjust_cfa_offset	-8
.cfi_restore	%rbx
	popq	%rbp
.cfi_adjust_cfa_offset	-8
.cfi_restore	%rbp
.Lgcm_dec_abort:
	.byte	0xf3,0xc3

.cfi_endproc	
.size	aesni_gcm_decrypt,.-aesni_gcm_decrypt
.section	.rodata
.align	64
.Lbswap_mask:
.byte	15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0
.Lpoly:
.byte	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0xc2
.Lone_msb:
.byte	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1
.Ltwo_lsb:
.byte	2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
.Lone_lsb:
.byte	1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
.byte	65,69,83,45,78,73,32,71,67,77,32,109,111,100,117,108,101,32,102,111,114,32,120,56,54,95,54,52,44,32,67,82,89,80,84,79,71,65,77,83,32,98,121,32,60,97,112,112,114,111,64,111,112,101,110,115,115,108,46,111,114,103,62,0
.align	64
.text	
#endif
