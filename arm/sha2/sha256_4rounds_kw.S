// 4 rounds of SHA-256 with K-constant loading and pre-addition.
// Inputs:
//   Q0 = state ABCD, Q1 = state EFGH (already in registers)
//   Q5 = message words W[0..3] (already in register)
//   x1 = pointer to 4 K constants (16 bytes)
//
// Loads K[0..3] from memory, computes K+W, then does 4 rounds.

        .text
        .globl sha256_4rounds_kw
        .type sha256_4rounds_kw, %function
        .align 4

sha256_4rounds_kw:
        ldr     q4, [x1]               // Q4 = K[0..3]
        add     v2.4s, v4.4s, v5.4s    // Q2 = K[0..3] + W[0..3]
        mov     v3.16b, v0.16b         // Save ABCD
        sha256h q0, q1, v2.4s          // Q0 = new ABCD
        sha256h2 q1, q3, v2.4s         // Q1 = new EFGH
        ret

        .size sha256_4rounds_kw, .-sha256_4rounds_kw
