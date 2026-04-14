// SHA-256 single-block processing with memory load/store.
//
// void sha256_block_simple(uint32_t state[8], const uint8_t data[64],
//                          const uint32_t K[64])
//
// Inputs:
//   x0 = pointer to state (8 x uint32 = 32 bytes, read and written)
//   x1 = pointer to message data (64 bytes, read-only)
//   x2 = pointer to K constant table (64 x uint32 = 256 bytes, read-only)
//
// Output:
//   state[0..7] = sha256_block(byte-swapped message, input state)
//
// This wraps sha256_block_core with memory load/store:
//   1. Load state from [x0] into Q0, Q1
//   2. Load message from [x1] into Q4-Q7 + REV32 byte-swap
//   3. Run the 109-instruction block core (K constants from [x2])
//   4. Store result from Q0, Q1 back to [x0]

        .text
        .globl sha256_block_simple
        .type sha256_block_simple, %function
        .align 4

sha256_block_simple:
        // Load hash state: Q0 = ABCD, Q1 = EFGH
        ldr     q0, [x0]
        ldr     q1, [x0, #16]

        // Load message data: Q4-Q7 = 64 bytes of message
        ldr     q4, [x1]
        ldr     q5, [x1, #16]
        ldr     q6, [x1, #32]
        ldr     q7, [x1, #48]

        // Byte-swap message words from little-endian to big-endian
        rev32   v4.16b, v4.16b
        rev32   v5.16b, v5.16b
        rev32   v6.16b, v6.16b
        rev32   v7.16b, v7.16b

        // x1 is no longer needed for data; reuse x2 as K pointer
        // (sha256_block_core expects K pointer in x1)
        mov     x1, x2

        // ======== Begin sha256_block_core (inlined) ========
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
        // ======== End sha256_block_core ========

        // Store result back to state
        str     q0, [x0]
        str     q1, [x0, #16]

        ret

        .size sha256_block_simple, .-sha256_block_simple
