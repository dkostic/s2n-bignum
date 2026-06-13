// Head-to-head microbenchmark: s2n-bignum's sha1_block_data_order_hw vs
// aws-lc's sha1_block_data_order_hw (renamed awslc_sha1_block_data_order_hw
// in tests/awslc_sha1_armv8.S so the two symbols can co-link).
//
// Build (from s2n-bignum repo root):
//   gcc -O2 -march=armv8-a+crypto -o tests/sha1_hw_bench \
//       tests/sha1_hw_bench.c tests/awslc_sha1_armv8.S \
//       arm/libs2nbignum.a
//
// Sanity:  the two implementations are run on identical (state,data) inputs
// for each block-count, and their final 5-word states are compared before
// any timing is reported.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern void sha1_block_data_order_hw(uint32_t state[5],
                                     const uint8_t *data,
                                     uint64_t num_blocks,
                                     const uint32_t k[16]);

extern void awslc_sha1_block_data_order_hw(uint32_t state[5],
                                           const uint8_t *data,
                                           uint64_t num);

static const uint32_t SHA1_K[16] = {
    0x5a827999u, 0x5a827999u, 0x5a827999u, 0x5a827999u,
    0x6ed9eba1u, 0x6ed9eba1u, 0x6ed9eba1u, 0x6ed9eba1u,
    0x8f1bbcdcu, 0x8f1bbcdcu, 0x8f1bbcdcu, 0x8f1bbcdcu,
    0xca62c1d6u, 0xca62c1d6u, 0xca62c1d6u, 0xca62c1d6u
};

static const uint32_t SHA1_INIT[5] = {
    0x67452301u, 0xefcdab89u, 0x98badcfeu, 0x10325476u, 0xc3d2e1f0u
};

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

static uint64_t read_cycles(void) {
    uint64_t v;
    __asm__ volatile("mrs %0, cntvct_el0" : "=r"(v));
    return v;
}

static uint64_t cycle_freq_hz(void) {
    uint64_t v;
    __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(v));
    return v;
}

static int verify_match(size_t num_blocks) {
    uint8_t *data = aligned_alloc(64, num_blocks * 64);
    if (!data) return 0;
    for (size_t i = 0; i < num_blocks * 64; i++) data[i] = (uint8_t)(i * 37u + 11u);
    uint32_t s_bn[5], s_aw[5];
    memcpy(s_bn, SHA1_INIT, sizeof s_bn);
    memcpy(s_aw, SHA1_INIT, sizeof s_aw);
    sha1_block_data_order_hw(s_bn, data, (uint64_t)num_blocks, SHA1_K);
    awslc_sha1_block_data_order_hw(s_aw, data, (uint64_t)num_blocks);
    int ok = (memcmp(s_bn, s_aw, sizeof s_bn) == 0);
    if (!ok) {
        fprintf(stderr, "MISMATCH at num_blocks=%zu\n  s2n: %08x %08x %08x %08x %08x\n  awslc: %08x %08x %08x %08x %08x\n",
                num_blocks,
                s_bn[0], s_bn[1], s_bn[2], s_bn[3], s_bn[4],
                s_aw[0], s_aw[1], s_aw[2], s_aw[3], s_aw[4]);
    }
    free(data);
    return ok;
}

#define INNER_REPS 100000
#define OUTER_REPS 5

typedef void (*bn_fn)(uint32_t[5], const uint8_t *, uint64_t, const uint32_t[16]);
typedef void (*aw_fn)(uint32_t[5], const uint8_t *, uint64_t);

static void bench_bn(size_t num_blocks, double *best_ns_per_byte, double *best_cyc_per_byte) {
    uint8_t *data = aligned_alloc(64, num_blocks * 64);
    for (size_t i = 0; i < num_blocks * 64; i++) data[i] = (uint8_t)i;
    uint32_t state[5];
    double best_ns = 1e30, best_cyc = 1e30;
    uint64_t cf = cycle_freq_hz();
    for (int o = 0; o < OUTER_REPS; o++) {
        memcpy(state, SHA1_INIT, sizeof state);
        // warm
        sha1_block_data_order_hw(state, data, (uint64_t)num_blocks, SHA1_K);
        uint64_t t0 = now_ns();
        uint64_t c0 = read_cycles();
        for (int r = 0; r < INNER_REPS; r++) {
            sha1_block_data_order_hw(state, data, (uint64_t)num_blocks, SHA1_K);
        }
        uint64_t c1 = read_cycles();
        uint64_t t1 = now_ns();
        double ns = (double)(t1 - t0);
        double cyc = (double)(c1 - c0);
        double bytes = (double)INNER_REPS * (double)num_blocks * 64.0;
        double npb = ns / bytes;
        double cpb = cyc / bytes;
        if (npb < best_ns) best_ns = npb;
        if (cpb < best_cyc) best_cyc = cpb;
        // Note: cntvct_el0 ticks at the system counter freq (often 1GHz / 50MHz),
        // not at CPU-cycle granularity. Convert ticks -> cpu-equivalent estimate
        // via the system counter freq scaling factor: cyc/byte here is "vct
        // ticks per byte"; multiply by (cpu_freq / cf) externally for cpu cyc.
        (void)cf;
    }
    *best_ns_per_byte = best_ns;
    *best_cyc_per_byte = best_cyc;
    free(data);
}

static void bench_aw(size_t num_blocks, double *best_ns_per_byte, double *best_cyc_per_byte) {
    uint8_t *data = aligned_alloc(64, num_blocks * 64);
    for (size_t i = 0; i < num_blocks * 64; i++) data[i] = (uint8_t)i;
    uint32_t state[5];
    double best_ns = 1e30, best_cyc = 1e30;
    for (int o = 0; o < OUTER_REPS; o++) {
        memcpy(state, SHA1_INIT, sizeof state);
        awslc_sha1_block_data_order_hw(state, data, (uint64_t)num_blocks);
        uint64_t t0 = now_ns();
        uint64_t c0 = read_cycles();
        for (int r = 0; r < INNER_REPS; r++) {
            awslc_sha1_block_data_order_hw(state, data, (uint64_t)num_blocks);
        }
        uint64_t c1 = read_cycles();
        uint64_t t1 = now_ns();
        double ns = (double)(t1 - t0);
        double cyc = (double)(c1 - c0);
        double bytes = (double)INNER_REPS * (double)num_blocks * 64.0;
        double npb = ns / bytes;
        double cpb = cyc / bytes;
        if (npb < best_ns) best_ns = npb;
        if (cpb < best_cyc) best_cyc = cpb;
    }
    *best_ns_per_byte = best_ns;
    *best_cyc_per_byte = best_cyc;
    free(data);
}

int main(void) {
    static const size_t sizes[] = {1, 2, 8, 64, 1024};
    static const size_t NSIZES = sizeof(sizes) / sizeof(sizes[0]);

    printf("Host counter freq (cntfrq_el0): %llu Hz\n",
           (unsigned long long)cycle_freq_hz());
    printf("INNER_REPS=%d OUTER_REPS=%d (best-of-outer reported)\n\n",
           INNER_REPS, OUTER_REPS);

    // Sanity-check: outputs must agree on every benchmarked block count.
    for (size_t i = 0; i < NSIZES; i++) {
        if (!verify_match(sizes[i])) {
            fprintf(stderr, "Output mismatch — refusing to benchmark.\n");
            return 1;
        }
    }
    printf("Output check: s2n-bignum and aws-lc agree on all block counts.\n\n");

    printf("%8s | %12s %12s | %12s %12s | %8s\n",
           "blocks", "s2n ns/B", "awslc ns/B", "s2n vct/B", "awslc vct/B", "ratio");
    printf("---------+--------------------------+--------------------------+--------\n");
    for (size_t i = 0; i < NSIZES; i++) {
        double bn_ns, bn_cyc, aw_ns, aw_cyc;
        bench_bn(sizes[i], &bn_ns, &bn_cyc);
        bench_aw(sizes[i], &aw_ns, &aw_cyc);
        printf("%8zu | %12.4f %12.4f | %12.4f %12.4f | %8.3f\n",
               sizes[i], bn_ns, aw_ns, bn_cyc, aw_cyc, bn_ns / aw_ns);
    }
    printf("\nratio = s2n_ns_per_byte / awslc_ns_per_byte (1.000 = parity, <1.0 = s2n faster)\n");
    return 0;
}
