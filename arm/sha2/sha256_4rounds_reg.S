// 4 rounds of SHA-256 compression, register-only.
// Input:  Q0 = ABCD state, Q1 = EFGH state, Q2 = pre-added K[t]+W[t]
// Output: Q0 = new ABCD, Q1 = new EFGH

        .text
        .globl sha256_4rounds_reg
        .type sha256_4rounds_reg, %function
        .align 4

sha256_4rounds_reg:
        mov     v3.16b, v0.16b
        sha256h q0, q1, v2.4s
        sha256h2 q1, q3, v2.4s
        ret

        .size sha256_4rounds_reg, .-sha256_4rounds_reg
