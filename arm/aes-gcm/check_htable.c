// Diff harness: compare ref_aes_gcm.c's GHASH primitives against aws-lc's
// actual gcm_init_v8 / gcm_gmult_v8 (linked from
// aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/ghashv8-armx.S).
//
// Build:
//   cp ~/whole-proofs/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/ghashv8-armx.S /tmp/
//   sed -i '/#include <openssl\//d' /tmp/ghashv8-armx.S
//   cc -DOPENSSL_AARCH64 -D__ELF__ -DAARCH64_VALID_CALL_TARGET= \
//      -DAARCH64_SIGN_LINK_REGISTER= -D__ARM_MAX_ARCH__=8 \
//      -o /tmp/check_htable arm/aes-gcm/check_htable.c \
//      /tmp/ghashv8-armx.S -L./arm -ls2nbignum
//
// This file is self-contained; it pulls in tests/ref_aes_xts.c (for the AES
// S-box and helpers) and tests/ref_aes_gcm.c via #include.
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "../../include/s2n-bignum.h"

extern void gcm_init_v8(uint64_t Htable[32], const uint64_t H[2]);
extern void gcm_gmult_v8(uint8_t Xi[16], const uint64_t Htable[32]);

#define BUFFERSIZE 256
static uint8_t bb1[BUFFERSIZE], bb2[BUFFERSIZE], bb3[BUFFERSIZE], bb4[BUFFERSIZE];
#define VERBOSE 1
static int tests = 1;
#include "../../tests/ref_aes_xts.c"
#include "../../tests/ref_aes_gcm.c"

static uint64_t load_be64(const uint8_t *p)
{ return ((uint64_t)p[0] << 56) | ((uint64_t)p[1] << 48) |
         ((uint64_t)p[2] << 40) | ((uint64_t)p[3] << 32) |
         ((uint64_t)p[4] << 24) | ((uint64_t)p[5] << 16) |
         ((uint64_t)p[6] << 8)  |  (uint64_t)p[7];
}

static void hexdump(const char *label, const void *p, size_t n)
{ const uint8_t *b = (const uint8_t *)p;
  size_t i;
  printf("%s = ", label);
  for (i = 0; i < n; ++i) printf("%02x", b[i]);
  printf("\n");
}

int main(void)
{ uint8_t key_bytes[16] = { 0xfe,0xff,0xe9,0x92,0x86,0x65,0x73,0x1c,
                            0x6d,0x6a,0x8f,0x94,0x67,0x30,0x83,0x08 };
  uint8_t H_raw[16];
  s2n_bignum_AES_KEY key;
  uint64_t my_Htable[24] = {0};
  uint64_t aws_Htable[24] = {0};
  uint8_t  zero[16] = {0};
  uint64_t H[2];

  ref_aes128_expand_key(key_bytes, &key);
  ref_aes128_encrypt_block(zero, H_raw, &key);

  // My init
  ref_gcm_init_htable(my_Htable, &key);

  // aws-lc init
  H[0] = load_be64(H_raw);
  H[1] = load_be64(H_raw + 8);
  gcm_init_v8(aws_Htable, H);

  hexdump("my  Htable[0]", my_Htable, 16);
  hexdump("aws Htable[0]", aws_Htable, 16);
  hexdump("my  Htable[2] (H^2)", (uint8_t *)my_Htable + 32, 16);
  hexdump("aws Htable[2] (H^2)", (uint8_t *)aws_Htable + 32, 16);
  hexdump("my  Htable[3] (H^3)", (uint8_t *)my_Htable + 48, 16);
  hexdump("aws Htable[3] (H^3)", (uint8_t *)aws_Htable + 48, 16);
  hexdump("my  Htable[5] (H^4)", (uint8_t *)my_Htable + 80, 16);
  hexdump("aws Htable[5] (H^4)", (uint8_t *)aws_Htable + 80, 16);

  // Test gcm_gmult_v8 vs my gcm_ghash_block_v8
  uint8_t Xi_aws[16] = {0};
  uint8_t Xi_my[16] = {0};
  uint8_t ct_block[16] = { 0x9b,0xb2,0x2c,0xe7,0xd9,0xf3,0x72,0xc1,
                           0xee,0x2b,0x28,0x72,0x2b,0x25,0xf2,0x06 };

  // aws: Xi ^= ct, then gmult
  for (int i = 0; i < 16; ++i) Xi_aws[i] ^= ct_block[i];
  gcm_gmult_v8(Xi_aws, aws_Htable);
  hexdump("aws after gmult_v8", Xi_aws, 16);

  // my: gcm_ghash_block_v8(Xi, ct, H_lo, H_hi)
  uint64_t H_lo, H_hi;
  v8_htable_load(&H_lo, &H_hi, (uint8_t *)my_Htable);
  printf("H_hi = %016lx, H_lo = %016lx\n", H_hi, H_lo);
  gcm_ghash_block_v8(Xi_my, ct_block, H_lo, H_hi);
  hexdump("my  after ghash_v8", Xi_my, 16);

  return 0;
}
