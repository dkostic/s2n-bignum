// 4 rounds of SHA-256 compression with state load/store.
// void sha256_4rounds_mem(uint32_t state[8], int128 kw_in_q2)
//   x0 = pointer to 8-word state (read and written)
//   Q2 = pre-added K[t]+W[t] values (4 x 32-bit, caller provides)
//
// Loads state from [x0], performs 4 SHA-256 compression rounds,
// stores updated state back to [x0].

        .text
        .globl sha256_4rounds_mem
        .type sha256_4rounds_mem, %function
        .align 4

sha256_4rounds_mem:
        ldr     q0, [x0]               // Load ABCD from state[0..3]
        ldr     q1, [x0, #16]          // Load EFGH from state[4..7]
        mov     v3.16b, v0.16b         // Save ABCD for sha256h2
        sha256h q0, q1, v2.4s          // Q0 = new ABCD (4 rounds)
        sha256h2 q1, q3, v2.4s         // Q1 = new EFGH (4 rounds)
        str     q0, [x0]               // Store new ABCD
        str     q1, [x0, #16]          // Store new EFGH
        ret

        .size sha256_4rounds_mem, .-sha256_4rounds_mem
