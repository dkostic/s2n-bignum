// 2 rounds of SHA-512 compression, register-only (no memory ops).
// Mirrors the inner pattern of aws-lc's sha512_block_data_order_hw (.Loop_hw)
// for a single SHA512H + SHA512H2 group.
//
// Input:
//   V0  = word_join b a        (state {b, a} packed: hi=b, lo=a)
//   V1  = word_join d c        (state {d, c})
//   V2  = word_join f e        (state {f, e})
//   V3  = word_join h g        (state {h, g})
//   V24 = word_join kw0 kw1    (pre-packed K+W for these two rounds)
//
// Output (before ret):
//   V3 = word_join (EL 1 s2) (EL 0 s2)    // new {b', a'} half of state
//   V4 = word_join (EL 5 s2) (EL 4 s2)    // new {d', c'} half of state
// where  s1 = sha512_compress_round kw0 0 [a;b;c;d;e;f;g;h]
//        s2 = sha512_compress_round kw1 0 s1

        .text
        .globl sha512_2rounds_reg
        .type sha512_2rounds_reg, %function
        .align 4

sha512_2rounds_reg:
        ext     v5.16b, v2.16b, v3.16b, #8      // v5 = word_join g f
        ext     v6.16b, v1.16b, v2.16b, #8      // v6 = word_join e d
        add     v3.2d, v3.2d, v24.2d            // v3 = word_join (h+kw0) (g+kw1)
        sha512h q3, q5, v6.2d                   // v3 = word_join T1_0 T1_1
        add     v4.2d, v1.2d, v3.2d             // v4 = word_join (d+T1_0) (c+T1_1)
        sha512h2 q3, q1, v0.2d                  // v3 = word_join a'' a'
        ret

        .size sha512_2rounds_reg, .-sha512_2rounds_reg
