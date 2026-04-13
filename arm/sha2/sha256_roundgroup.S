// One complete SHA-256 round group: 4 compression rounds + schedule update.
//
// Inputs:
//   Q0 = state ABCD, Q1 = state EFGH
//   Q4 = W[0..3], Q5 = W[4..7], Q6 = W[8..11], Q7 = W[12..15]
//   x1 = pointer to K[0..3] constants (16 bytes)
//
// Outputs:
//   Q0 = new ABCD after 4 rounds
//   Q1 = new EFGH after 4 rounds
//   Q4 = W[16..19] (4 new message schedule words)

        .text
        .globl sha256_roundgroup
        .type sha256_roundgroup, %function
        .align 4

sha256_roundgroup:
        ldr     q16, [x1]              // Q16 = K[0..3]
        add     v2.4s, v4.4s, v16.4s   // Q2 = W[0..3] + K[0..3]
        mov     v3.16b, v0.16b         // Save ABCD
        sha256h q0, q1, v2.4s          // New ABCD (4 rounds)
        sha256h2 q1, q3, v2.4s         // New EFGH (4 rounds)
        sha256su0 v4.4s, v5.4s         // Partial schedule update
        sha256su1 v4.4s, v6.4s, v7.4s  // Complete: Q4 = W[16..19]
        ret

        .size sha256_roundgroup, .-sha256_roundgroup
