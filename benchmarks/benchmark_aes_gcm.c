// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
// Benchmark the x86 AES-GCM entry points (aesni_gcm_encrypt /
// aesni_gcm_decrypt) and collect the aws-lc baseline numbers used as
// the performance reference for the s2n-bignum inlined variants.
//
// The benchmarked functions are taken from aws-lc's libcrypto.a; the
// binary linked by this translation unit is expected to be the
// reference (aws-lc) implementation.  To retarget to the s2n-bignum
// inlined variant, replace aesni_gcm_encrypt / aesni_gcm_decrypt at
// link time.
//
// Build (aws-lc baseline):
//   cc -O2 -I $AWSLC/include benchmark_aes_gcm.c \
//         $AWSLC/build/crypto/libcrypto.a -lpthread -o bench_gcm_stock
//
// Build (s2n-bignum inlined):
//   (build renamed .o's of x86/aes-gcm/*.S first)
//   cc -O2 -I $AWSLC/include benchmark_aes_gcm.c \
//         aesni_gcm_encrypt.o aesni_gcm_decrypt.o \
//         $AWSLC/build/crypto/libcrypto.a -lpthread -o bench_gcm_inlined
//
// Output: three lines per size, stating bytes/cycle and MB/s.

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define AES_MAXNR 14
struct aes_key_st {
    uint32_t rd_key[4 * (AES_MAXNR + 1)];
    unsigned rounds;
};
typedef struct aes_key_st AES_KEY;

typedef struct { uint64_t hi, lo; } u128_aws;

extern int aes_hw_set_encrypt_key(const uint8_t *key, int bits, AES_KEY *k);
extern void aes_hw_encrypt(const uint8_t *in, uint8_t *out, const AES_KEY *key);
extern void gcm_init_avx(u128_aws Htable[16], const uint64_t Xi[2]);
extern size_t aesni_gcm_encrypt(const uint8_t *in, uint8_t *out, size_t len,
                                const AES_KEY *key, uint8_t ivec[16],
                                const u128_aws Htable[16], uint8_t Xi[16]);
extern size_t aesni_gcm_decrypt(const uint8_t *in, uint8_t *out, size_t len,
                                const AES_KEY *key, uint8_t ivec[16],
                                const u128_aws Htable[16], uint8_t Xi[16]);

static double time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

static uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ volatile ("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

static void bench_one(
    const char *label,
    size_t nbytes,
    size_t (*fn)(const uint8_t*, uint8_t*, size_t,
                 const AES_KEY*, uint8_t*,
                 const u128_aws*, uint8_t*),
    const AES_KEY *key,
    const u128_aws *Htable)
{
    // Pre-allocate buffers.
    uint8_t *in  = aligned_alloc(64, nbytes);
    uint8_t *out = aligned_alloc(64, nbytes);
    if (!in || !out) { fprintf(stderr, "oom\n"); exit(1); }
    memset(in, 0x5a, nbytes);

    // Round trip one call to warm caches.
    uint8_t iv[16] = {0}, Xi[16] = {0};
    iv[15] = 2;
    (void)fn(in, out, nbytes, key, iv, Htable, Xi);

    // Determine a rep count that gives a reasonably long run (~200ms).
    const double target_ns = 2.0e8;
    size_t reps = 1;
    while (1) {
        double t0 = time_ns();
        for (size_t i = 0; i < reps; i++) {
            iv[12] = iv[13] = iv[14] = 0; iv[15] = 2;
            memset(Xi, 0, 16);
            (void)fn(in, out, nbytes, key, iv, Htable, Xi);
        }
        double dt = time_ns() - t0;
        if (dt >= target_ns) break;
        reps = reps * 2 + 1;
        if (reps > (1u << 24)) break;
    }

    // Now do the measured run.
    uint64_t c0 = rdtsc();
    double t0 = time_ns();
    for (size_t i = 0; i < reps; i++) {
        iv[12] = iv[13] = iv[14] = 0; iv[15] = 2;
        memset(Xi, 0, 16);
        (void)fn(in, out, nbytes, key, iv, Htable, Xi);
    }
    double dt = time_ns() - t0;
    uint64_t c1 = rdtsc();

    double total_bytes = (double)nbytes * (double)reps;
    double cycles = (double)(c1 - c0);
    double ns_per_call = dt / (double)reps;
    double cycles_per_byte = cycles / total_bytes;
    double throughput_mib_per_s = total_bytes / dt * 1000.0;  // MiB/s if dt in ns and bytes in MiB
    throughput_mib_per_s = (total_bytes / 1048576.0) / (dt / 1e9);

    printf("%-14s size=%6zu  reps=%8zu  ns/call=%9.1f  cycles/byte=%6.3f  MiB/s=%8.1f\n",
           label, nbytes, reps, ns_per_call, cycles_per_byte, throughput_mib_per_s);

    free(in); free(out);
}

int main(int argc, char **argv) {
    static const uint8_t kKey[16] = {
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
        0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
    };

    AES_KEY aes_key;
    if (aes_hw_set_encrypt_key(kKey, 128, &aes_key) < 0) {
        fprintf(stderr, "aes key setup failed\n"); return 1;
    }
    // H = AES-128(key, 0^128), bswapped per u64 half.
    uint8_t zero[16] = {0}, H[16];
    aes_hw_encrypt(zero, H, &aes_key);
    uint64_t Xi_kh[2];
    Xi_kh[0] = __builtin_bswap64(*(uint64_t*)H);
    Xi_kh[1] = __builtin_bswap64(*(uint64_t*)(H + 8));

    u128_aws Htable[16] __attribute__((aligned(16)));
    gcm_init_avx(Htable, Xi_kh);

    const size_t sizes[] = { 1024, 8192, 65536 };
    const char *names[] = { "1 KiB", "8 KiB", "64 KiB" };

    (void)argc; (void)argv;

    printf("\n--- aesni_gcm_encrypt ---\n");
    for (size_t i = 0; i < sizeof(sizes)/sizeof(*sizes); i++) {
        bench_one(names[i], sizes[i], aesni_gcm_encrypt, &aes_key, Htable);
    }
    printf("\n--- aesni_gcm_decrypt ---\n");
    for (size_t i = 0; i < sizeof(sizes)/sizeof(*sizes); i++) {
        bench_one(names[i], sizes[i], aesni_gcm_decrypt, &aes_key, Htable);
    }
    return 0;
}
