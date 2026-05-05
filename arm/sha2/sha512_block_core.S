// SHA-512 block core: 80 rounds of compression + state add-back.
// Register-only (no memory I/O for state/data): state & schedule live in Q regs.
//
// Inputs:
//   Q0 = word_join b a       (state {b,a}, hi=b, lo=a)
//   Q1 = word_join d c       (state {d,c})
//   Q2 = word_join f e       (state {f,e})
//   Q3 = word_join h g       (state {h,g})
//   Q16..Q23 = schedule words, each Q16+j = word_join w(2j+1) w(2j),
//              already byte-reversed from memory order.
//   X3 = pointer to K table: 80 x int64 = 640 bytes. Each 128-bit chunk
//        at X3+16*k holds word_join (EL (2*k+1) sha512_K) (EL (2*k) sha512_K).
//        (The in-kernel `ext v24, v24, v24, #8` after each K load swaps the
//        two 64-bit halves so the following add/sha512h see the pairing
//        K[2k]+w[2k] in the hi half and K[2k+1]+w[2k+1] in the lo half.)
//
// Outputs:
//   Q0..Q3 = final state after sha512_block computation (initial + compressed).
//
// Structure: 40 round groups; groups 0..31 do SHA512SU0/SU1 schedule update
// in-place on v16..v23, groups 32..39 omit it. Final v0..v3 += saved v28..v31.

        .text
        .globl sha512_block_core
        .type sha512_block_core, %function
        .align 4

sha512_block_core:

        // Save initial state for final add-back
        mov     v28.16b, v0.16b
        mov     v29.16b, v1.16b
        mov     v30.16b, v2.16b
        mov     v31.16b, v3.16b

        // === Round Group 0 (rounds 0-1) ===
        ldr     q24, [x3]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 1 (rounds 2-3) ===
        ldr     q24, [x3, #16]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 2 (rounds 4-5) ===
        ldr     q24, [x3, #32]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 3 (rounds 6-7) ===
        ldr     q24, [x3, #48]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 4 (rounds 8-9) ===
        ldr     q24, [x3, #64]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 5 (rounds 10-11) ===
        ldr     q24, [x3, #80]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 6 (rounds 12-13) ===
        ldr     q24, [x3, #96]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 7 (rounds 14-15) ===
        ldr     q24, [x3, #112]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 8 (rounds 16-17) ===
        ldr     q24, [x3, #128]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 9 (rounds 18-19) ===
        ldr     q24, [x3, #144]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 10 (rounds 20-21) ===
        ldr     q24, [x3, #160]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 11 (rounds 22-23) ===
        ldr     q24, [x3, #176]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 12 (rounds 24-25) ===
        ldr     q24, [x3, #192]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 13 (rounds 26-27) ===
        ldr     q24, [x3, #208]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 14 (rounds 28-29) ===
        ldr     q24, [x3, #224]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 15 (rounds 30-31) ===
        ldr     q24, [x3, #240]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 16 (rounds 32-33) ===
        ldr     q24, [x3, #256]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 17 (rounds 34-35) ===
        ldr     q24, [x3, #272]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 18 (rounds 36-37) ===
        ldr     q24, [x3, #288]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 19 (rounds 38-39) ===
        ldr     q24, [x3, #304]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 20 (rounds 40-41) ===
        ldr     q24, [x3, #320]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 21 (rounds 42-43) ===
        ldr     q24, [x3, #336]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 22 (rounds 44-45) ===
        ldr     q24, [x3, #352]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 23 (rounds 46-47) ===
        ldr     q24, [x3, #368]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 24 (rounds 48-49) ===
        ldr     q24, [x3, #384]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v16.2d, v17.2d
        ext     v7.16b, v20.16b, v21.16b, #8
        sha512su1 v16.2d, v23.2d, v7.2d

        // === Round Group 25 (rounds 50-51) ===
        ldr     q24, [x3, #400]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v17.2d, v18.2d
        ext     v7.16b, v21.16b, v22.16b, #8
        sha512su1 v17.2d, v16.2d, v7.2d

        // === Round Group 26 (rounds 52-53) ===
        ldr     q24, [x3, #416]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v18.2d, v19.2d
        ext     v7.16b, v22.16b, v23.16b, #8
        sha512su1 v18.2d, v17.2d, v7.2d

        // === Round Group 27 (rounds 54-55) ===
        ldr     q24, [x3, #432]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d
        sha512su0 v19.2d, v20.2d
        ext     v7.16b, v23.16b, v16.16b, #8
        sha512su1 v19.2d, v18.2d, v7.2d

        // === Round Group 28 (rounds 56-57) ===
        ldr     q24, [x3, #448]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d
        sha512su0 v20.2d, v21.2d
        ext     v7.16b, v16.16b, v17.16b, #8
        sha512su1 v20.2d, v19.2d, v7.2d

        // === Round Group 29 (rounds 58-59) ===
        ldr     q24, [x3, #464]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d
        sha512su0 v21.2d, v22.2d
        ext     v7.16b, v17.16b, v18.16b, #8
        sha512su1 v21.2d, v20.2d, v7.2d

        // === Round Group 30 (rounds 60-61) ===
        ldr     q24, [x3, #480]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d
        sha512su0 v22.2d, v23.2d
        ext     v7.16b, v18.16b, v19.16b, #8
        sha512su1 v22.2d, v21.2d, v7.2d

        // === Round Group 31 (rounds 62-63) ===
        ldr     q24, [x3, #496]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d
        sha512su0 v23.2d, v16.2d
        ext     v7.16b, v19.16b, v20.16b, #8
        sha512su1 v23.2d, v22.2d, v7.2d

        // === Round Group 32 (rounds 64-65) ===
        ldr     q24, [x3, #512]
        add     v24.2d, v24.2d, v16.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d

        // === Round Group 33 (rounds 66-67) ===
        ldr     q24, [x3, #528]
        add     v24.2d, v24.2d, v17.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d

        // === Round Group 34 (rounds 68-69) ===
        ldr     q24, [x3, #544]
        add     v24.2d, v24.2d, v18.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d

        // === Round Group 35 (rounds 70-71) ===
        ldr     q24, [x3, #560]
        add     v24.2d, v24.2d, v19.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v2.16b, v3.16b, #8
        ext     v6.16b, v1.16b, v2.16b, #8
        add     v3.2d, v3.2d, v24.2d
        sha512h q3, q5, v6.2d
        add     v4.2d, v1.2d, v3.2d
        sha512h2 q3, q1, v0.2d

        // === Round Group 36 (rounds 72-73) ===
        ldr     q24, [x3, #576]
        add     v24.2d, v24.2d, v20.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v4.16b, v2.16b, #8
        ext     v6.16b, v0.16b, v4.16b, #8
        add     v2.2d, v2.2d, v24.2d
        sha512h q2, q5, v6.2d
        add     v1.2d, v0.2d, v2.2d
        sha512h2 q2, q0, v3.2d

        // === Round Group 37 (rounds 74-75) ===
        ldr     q24, [x3, #592]
        add     v24.2d, v24.2d, v21.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v1.16b, v4.16b, #8
        ext     v6.16b, v3.16b, v1.16b, #8
        add     v4.2d, v4.2d, v24.2d
        sha512h q4, q5, v6.2d
        add     v0.2d, v3.2d, v4.2d
        sha512h2 q4, q3, v2.2d

        // === Round Group 38 (rounds 76-77) ===
        ldr     q24, [x3, #608]
        add     v24.2d, v24.2d, v22.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v0.16b, v1.16b, #8
        ext     v6.16b, v2.16b, v0.16b, #8
        add     v1.2d, v1.2d, v24.2d
        sha512h q1, q5, v6.2d
        add     v3.2d, v2.2d, v1.2d
        sha512h2 q1, q2, v4.2d

        // === Round Group 39 (rounds 78-79) ===
        ldr     q24, [x3, #624]
        add     v24.2d, v24.2d, v23.2d
        ext     v24.16b, v24.16b, v24.16b, #8
        ext     v5.16b, v3.16b, v0.16b, #8
        ext     v6.16b, v4.16b, v3.16b, #8
        add     v0.2d, v0.2d, v24.2d
        sha512h q0, q5, v6.2d
        add     v2.2d, v4.2d, v0.2d
        sha512h2 q0, q4, v1.2d

        // State add-back: v0..v3 += saved initial state v28..v31
        add     v0.2d, v0.2d, v28.2d
        add     v1.2d, v1.2d, v29.2d
        add     v2.2d, v2.2d, v30.2d
        add     v3.2d, v3.2d, v31.2d

        ret

        .size sha512_block_core, .-sha512_block_core

