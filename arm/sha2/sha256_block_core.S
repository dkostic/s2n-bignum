// SHA-256 single-block compression core: 64 rounds + state add-back.
//
// Inputs (all in registers, no memory loads for state/data):
//   Q0 = ABCD state, Q1 = EFGH state
//   Q4 = M[0..3], Q5 = M[4..7], Q6 = M[8..11], Q7 = M[12..15]
//         (message words, already byte-swapped to big-endian)
//   x1 = pointer to K constant table (64 x int32 = 256 bytes)
//
// Output (in registers):
//   Q0 = new ABCD = compressed ABCD + initial ABCD
//   Q1 = new EFGH = compressed EFGH + initial EFGH
//
// Structure: 16 round groups of 4 rounds each.
//   Groups 0-11: LDR K + ADD K+W + MOV + SHA256H + SHA256H2 + SHA256SU0 + SHA256SU1
//   Groups 12-15: LDR K + ADD K+W + MOV + SHA256H + SHA256H2 (no schedule update)
//   Then: ADD state add-back + RET

        .text
        .globl sha256_block_core
        .type sha256_block_core, %function
        .align 4

sha256_block_core:
        // Save initial state for final add-back
        mov     v18.16b, v0.16b
        mov     v19.16b, v1.16b

        // === Round Group 0 (rounds 0-3): use Q4, update Q4 ===
        ldr     q16, [x1]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v4.4s, v5.4s
        sha256su1 v4.4s, v6.4s, v7.4s

        // === Round Group 1 (rounds 4-7): use Q5, update Q5 ===
        ldr     q16, [x1, #16]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v5.4s, v6.4s
        sha256su1 v5.4s, v7.4s, v4.4s

        // === Round Group 2 (rounds 8-11): use Q6, update Q6 ===
        ldr     q16, [x1, #32]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v6.4s, v7.4s
        sha256su1 v6.4s, v4.4s, v5.4s

        // === Round Group 3 (rounds 12-15): use Q7, update Q7 ===
        ldr     q16, [x1, #48]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v7.4s, v4.4s
        sha256su1 v7.4s, v5.4s, v6.4s

        // === Round Group 4 (rounds 16-19): use Q4, update Q4 ===
        ldr     q16, [x1, #64]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v4.4s, v5.4s
        sha256su1 v4.4s, v6.4s, v7.4s

        // === Round Group 5 (rounds 20-23): use Q5, update Q5 ===
        ldr     q16, [x1, #80]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v5.4s, v6.4s
        sha256su1 v5.4s, v7.4s, v4.4s

        // === Round Group 6 (rounds 24-27): use Q6, update Q6 ===
        ldr     q16, [x1, #96]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v6.4s, v7.4s
        sha256su1 v6.4s, v4.4s, v5.4s

        // === Round Group 7 (rounds 28-31): use Q7, update Q7 ===
        ldr     q16, [x1, #112]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v7.4s, v4.4s
        sha256su1 v7.4s, v5.4s, v6.4s

        // === Round Group 8 (rounds 32-35): use Q4, update Q4 ===
        ldr     q16, [x1, #128]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v4.4s, v5.4s
        sha256su1 v4.4s, v6.4s, v7.4s

        // === Round Group 9 (rounds 36-39): use Q5, update Q5 ===
        ldr     q16, [x1, #144]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v5.4s, v6.4s
        sha256su1 v5.4s, v7.4s, v4.4s

        // === Round Group 10 (rounds 40-43): use Q6, update Q6 ===
        ldr     q16, [x1, #160]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v6.4s, v7.4s
        sha256su1 v6.4s, v4.4s, v5.4s

        // === Round Group 11 (rounds 44-47): use Q7, update Q7 ===
        ldr     q16, [x1, #176]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        sha256su0 v7.4s, v4.4s
        sha256su1 v7.4s, v5.4s, v6.4s

        // === Round Group 12 (rounds 48-51): use Q4, NO schedule update ===
        ldr     q16, [x1, #192]
        add     v2.4s, v4.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

        // === Round Group 13 (rounds 52-55): use Q5, NO schedule update ===
        ldr     q16, [x1, #208]
        add     v2.4s, v5.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

        // === Round Group 14 (rounds 56-59): use Q6, NO schedule update ===
        ldr     q16, [x1, #224]
        add     v2.4s, v6.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

        // === Round Group 15 (rounds 60-63): use Q7, NO schedule update ===
        ldr     q16, [x1, #240]
        add     v2.4s, v7.4s, v16.4s
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s

        // === Add back initial state ===
        add     v0.4s, v0.4s, v18.4s
        add     v1.4s, v1.4s, v19.4s

        ret

        .size sha256_block_core, .-sha256_block_core
