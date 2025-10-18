#include "_internal_s2n_bignum_x86.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_basemul_k2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_basemul_k2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_basemul_k2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_basemul_k2):
        CFI_START
        _CET_ENDBR

        movl	$0xd010d01, %eax        # imm = 0xD010D01
        movd	%eax, %xmm0
        vpbroadcastd	%xmm0, %ymm0
        movl	$0xf301f301, %eax       # imm = 0xF301F301
        movd	%eax, %xmm1
        vpbroadcastd	%xmm1, %ymm1

        vmovdqa	(%rsi), %ymm2
        vmovdqa	0x20(%rsi), %ymm3
        vmovdqa	(%rdx), %ymm4
        vmovdqa	0x20(%rdx), %ymm5
        vmovdqa	(%rcx), %ymm6

        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9

        vmovdqa	%ymm7, (%rdi)
        vmovdqa	%ymm9, 0x20(%rdi)


        vmovdqa	0x40(%rsi), %ymm2
        vmovdqa	0x60(%rsi), %ymm3
        vmovdqa	0x40(%rdx), %ymm4
        vmovdqa	0x60(%rdx), %ymm5
        vmovdqa	0x20(%rcx), %ymm6

        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9

        vmovdqa	%ymm7, 0x40(%rdi)
        vmovdqa	%ymm9, 0x60(%rdi)

        CFI_RET

  S2N_BN_SIZE_DIRECTIVE(mlkem_basemul_k2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
