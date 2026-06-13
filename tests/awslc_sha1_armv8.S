// Standalone copy of aws-lc's sha1_block_data_order_hw, extracted from
// aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/sha1-armv8.S.
// Symbol renamed to awslc_sha1_block_data_order_hw so it can link beside
// s2n-bignum's sha1_block_data_order_hw for head-to-head benchmarking.
// ABI matches upstream aws-lc: (uint32_t state[5], const uint8_t *data,
// uint64_t num_blocks). K table is loaded ADRP-relative from .Lconst.

#if defined(__aarch64__) && defined(__ELF__)

.text

.globl	awslc_sha1_block_data_order_hw
.type	awslc_sha1_block_data_order_hw,%function
.align	6
awslc_sha1_block_data_order_hw:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	adrp	x4,.Lconst_awslc
	add	x4,x4,:lo12:.Lconst_awslc
	eor	v1.16b,v1.16b,v1.16b
	ld1	{v0.4s},[x0],#16
	ld1	{v1.s}[0],[x0]
	sub	x0,x0,#16
	ld1	{v16.4s,v17.4s,v18.4s,v19.4s},[x4]

.Loop_hw_awslc:
	ld1	{v4.16b,v5.16b,v6.16b,v7.16b},[x1],#64
	sub	x2,x2,#1
	rev32	v4.16b,v4.16b
	rev32	v5.16b,v5.16b

	add	v20.4s,v16.4s,v4.4s
	rev32	v6.16b,v6.16b
	orr	v22.16b,v0.16b,v0.16b	// offload

	add	v21.4s,v16.4s,v5.4s
	rev32	v7.16b,v7.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b
.inst	0x5e140020	//sha1c v0.16b,v1.16b,v20.4s		// 0
	add	v20.4s,v16.4s,v6.4s
.inst	0x5e0630a4	//sha1su0 v4.16b,v5.16b,v6.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 1
.inst	0x5e150060	//sha1c v0.16b,v3.16b,v21.4s
	add	v21.4s,v16.4s,v7.4s
.inst	0x5e2818e4	//sha1su1 v4.16b,v7.16b
.inst	0x5e0730c5	//sha1su0 v5.16b,v6.16b,v7.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 2
.inst	0x5e140040	//sha1c v0.16b,v2.16b,v20.4s
	add	v20.4s,v16.4s,v4.4s
.inst	0x5e281885	//sha1su1 v5.16b,v4.16b
.inst	0x5e0430e6	//sha1su0 v6.16b,v7.16b,v4.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 3
.inst	0x5e150060	//sha1c v0.16b,v3.16b,v21.4s
	add	v21.4s,v17.4s,v5.4s
.inst	0x5e2818a6	//sha1su1 v6.16b,v5.16b
.inst	0x5e053087	//sha1su0 v7.16b,v4.16b,v5.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 4
.inst	0x5e140040	//sha1c v0.16b,v2.16b,v20.4s
	add	v20.4s,v17.4s,v6.4s
.inst	0x5e2818c7	//sha1su1 v7.16b,v6.16b
.inst	0x5e0630a4	//sha1su0 v4.16b,v5.16b,v6.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 5
.inst	0x5e151060	//sha1p v0.16b,v3.16b,v21.4s
	add	v21.4s,v17.4s,v7.4s
.inst	0x5e2818e4	//sha1su1 v4.16b,v7.16b
.inst	0x5e0730c5	//sha1su0 v5.16b,v6.16b,v7.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 6
.inst	0x5e141040	//sha1p v0.16b,v2.16b,v20.4s
	add	v20.4s,v17.4s,v4.4s
.inst	0x5e281885	//sha1su1 v5.16b,v4.16b
.inst	0x5e0430e6	//sha1su0 v6.16b,v7.16b,v4.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 7
.inst	0x5e151060	//sha1p v0.16b,v3.16b,v21.4s
	add	v21.4s,v17.4s,v5.4s
.inst	0x5e2818a6	//sha1su1 v6.16b,v5.16b
.inst	0x5e053087	//sha1su0 v7.16b,v4.16b,v5.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 8
.inst	0x5e141040	//sha1p v0.16b,v2.16b,v20.4s
	add	v20.4s,v18.4s,v6.4s
.inst	0x5e2818c7	//sha1su1 v7.16b,v6.16b
.inst	0x5e0630a4	//sha1su0 v4.16b,v5.16b,v6.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 9
.inst	0x5e151060	//sha1p v0.16b,v3.16b,v21.4s
	add	v21.4s,v18.4s,v7.4s
.inst	0x5e2818e4	//sha1su1 v4.16b,v7.16b
.inst	0x5e0730c5	//sha1su0 v5.16b,v6.16b,v7.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 10
.inst	0x5e142040	//sha1m v0.16b,v2.16b,v20.4s
	add	v20.4s,v18.4s,v4.4s
.inst	0x5e281885	//sha1su1 v5.16b,v4.16b
.inst	0x5e0430e6	//sha1su0 v6.16b,v7.16b,v4.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 11
.inst	0x5e152060	//sha1m v0.16b,v3.16b,v21.4s
	add	v21.4s,v18.4s,v5.4s
.inst	0x5e2818a6	//sha1su1 v6.16b,v5.16b
.inst	0x5e053087	//sha1su0 v7.16b,v4.16b,v5.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 12
.inst	0x5e142040	//sha1m v0.16b,v2.16b,v20.4s
	add	v20.4s,v18.4s,v6.4s
.inst	0x5e2818c7	//sha1su1 v7.16b,v6.16b
.inst	0x5e0630a4	//sha1su0 v4.16b,v5.16b,v6.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 13
.inst	0x5e152060	//sha1m v0.16b,v3.16b,v21.4s
	add	v21.4s,v19.4s,v7.4s
.inst	0x5e2818e4	//sha1su1 v4.16b,v7.16b
.inst	0x5e0730c5	//sha1su0 v5.16b,v6.16b,v7.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 14
.inst	0x5e142040	//sha1m v0.16b,v2.16b,v20.4s
	add	v20.4s,v19.4s,v4.4s
.inst	0x5e281885	//sha1su1 v5.16b,v4.16b
.inst	0x5e0430e6	//sha1su0 v6.16b,v7.16b,v4.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 15
.inst	0x5e151060	//sha1p v0.16b,v3.16b,v21.4s
	add	v21.4s,v19.4s,v5.4s
.inst	0x5e2818a6	//sha1su1 v6.16b,v5.16b
.inst	0x5e053087	//sha1su0 v7.16b,v4.16b,v5.16b
.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 16
.inst	0x5e141040	//sha1p v0.16b,v2.16b,v20.4s
	add	v20.4s,v19.4s,v6.4s
.inst	0x5e2818c7	//sha1su1 v7.16b,v6.16b
.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 17
.inst	0x5e151060	//sha1p v0.16b,v3.16b,v21.4s
	add	v21.4s,v19.4s,v7.4s

.inst	0x5e280803	//sha1h v3.16b,v0.16b		// 18
.inst	0x5e141040	//sha1p v0.16b,v2.16b,v20.4s

.inst	0x5e280802	//sha1h v2.16b,v0.16b		// 19
.inst	0x5e151060	//sha1p v0.16b,v3.16b,v21.4s

	add	v1.4s,v1.4s,v2.4s
	add	v0.4s,v0.4s,v22.4s

	cbnz	x2,.Loop_hw_awslc

	st1	{v0.4s},[x0],#16
	st1	{v1.s}[0],[x0]

	ldr	x29,[sp],#16
	ret
.size	awslc_sha1_block_data_order_hw,.-awslc_sha1_block_data_order_hw

.section	.rodata
.align	6
.Lconst_awslc:
.long	0x5a827999,0x5a827999,0x5a827999,0x5a827999	//K_00_19
.long	0x6ed9eba1,0x6ed9eba1,0x6ed9eba1,0x6ed9eba1	//K_20_39
.long	0x8f1bbcdc,0x8f1bbcdc,0x8f1bbcdc,0x8f1bbcdc	//K_40_59
.long	0xca62c1d6,0xca62c1d6,0xca62c1d6,0xca62c1d6	//K_60_79

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

#endif  /* __aarch64__ && __ELF__ */
