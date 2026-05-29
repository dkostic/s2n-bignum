// Naive reference implementation of AES-128-GCM for testing aes_gcm_enc_kernel.
//
// This implements the byte-level GCM-CTR keystream + GHASH composition that
// the kernel computes, plus the helpers needed to set up the AES-128 round
// key schedule and the GHASH H-table from a raw key/IV.
//
// AES core (S-box, key expansion, single-block encrypt) is reused from
// ref_aes_xts.c; only AES-128-specific routines and the GCM/GHASH layer
// live here. ref_aes_xts.c is included before this file by tests/test.c.
//
// Based directly on:
//   - FIPS 197 (AES) for the cipher,
//   - NIST SP 800-38D for the GCM mode,
//   - aws-lc's `gcm_polyval_nohw` (crypto/fipsmodule/modes/gcm_nohw.c) for
//     a constant-time scalar GHASH that we rebrand as a byte-reflected GCM
//     multiplication on H.
//
// The kernel-specific calling convention this reference matches:
//   - bit_len is in BITS, must be a positive multiple of 128.
//   - ivec_io is the 16-byte big-endian counter Y_i (the kernel increments
//     the trailing 32 bits in big-endian after each block).
//   - Xi_io is the running GHASH tag, big-endian.
//   - key_schedule->rd_key holds the AES-128 round-key bytes (11 × 16 = 176
//     bytes, the remaining 64 bytes of rd_key[30] are unused by the kernel).
//   - Htable is the standard aws-lc Karatsuba layout (offset 0 = twisted H,
//     offset 16 = h12k, offset 32 = H^2, offset 48 = H^3, offset 64 = h34k,
//     offset 80 = H^4). The reference only consults Htable[0] (twisted H).

// ***************************************************************************
// AES-128 key expansion (FIPS 197, Section 5.2, Nk=4, Nr=10)
// ***************************************************************************

static void ref_aes128_expand_key(const uint8_t key[16],
                                  s2n_bignum_AES_KEY *ek)
{ uint8_t w[176]; // 11 round keys * 16 bytes
  int i;

  // First 16 bytes are the original key
  memcpy(w, key, 16);

  // Expand: FIPS 197 key expansion for Nk=4
  for (i = 4; i < 44; ++i)
   { uint8_t t[4];
     t[0] = w[4*(i-1)+0]; t[1] = w[4*(i-1)+1];
     t[2] = w[4*(i-1)+2]; t[3] = w[4*(i-1)+3];

     if (i % 4 == 0)
      { // RotWord + SubWord + Rcon
        uint8_t u = t[0];
        t[0] = ref_aes_sbox[t[1]] ^ ref_aes_rcon[i/4];
        t[1] = ref_aes_sbox[t[2]];
        t[2] = ref_aes_sbox[t[3]];
        t[3] = ref_aes_sbox[u];
      }

     w[4*i+0] = w[4*(i-4)+0] ^ t[0];
     w[4*i+1] = w[4*(i-4)+1] ^ t[1];
     w[4*i+2] = w[4*(i-4)+2] ^ t[2];
     w[4*i+3] = w[4*(i-4)+3] ^ t[3];
   }

  // Copy into rd_key (zero-padded so the kernel's [x8, #240] rounds-field
  // read finds the right value).
  memset(ek->rd_key, 0, sizeof(ek->rd_key));
  memcpy(ek->rd_key, w, 176);
  ek->rounds = 10;
}

// ***************************************************************************
// AES-128 single block encrypt: FIPS 197, Section 5.1 (Nr=10)
// ***************************************************************************

static void ref_aes128_encrypt_block(const uint8_t in[16], uint8_t out[16],
                                     const s2n_bignum_AES_KEY *ek)
{ uint8_t s[16];
  const uint8_t *rk = (const uint8_t *)ek->rd_key;
  int r, i;

  // Initial AddRoundKey (round 0)
  for (i = 0; i < 16; ++i) s[i] = in[i] ^ rk[i];

  for (r = 1; r <= 10; ++r)
   { uint8_t t[16];

     // SubBytes
     for (i = 0; i < 16; ++i) t[i] = ref_aes_sbox[s[i]];

     // ShiftRows
     s[0]  = t[0];  s[1]  = t[5];  s[2]  = t[10]; s[3]  = t[15];
     s[4]  = t[4];  s[5]  = t[9];  s[6]  = t[14]; s[7]  = t[3];
     s[8]  = t[8];  s[9]  = t[13]; s[10] = t[2];  s[11] = t[7];
     s[12] = t[12]; s[13] = t[1];  s[14] = t[6];  s[15] = t[11];

     // MixColumns (skip in final round)
     if (r < 10)
      { for (i = 0; i < 4; ++i)
         { uint8_t a = s[4*i], b = s[4*i+1], c = s[4*i+2], d = s[4*i+3];
           s[4*i]   = ref_aes_xtime(a) ^ ref_aes_xtime(b) ^ b ^ c ^ d;
           s[4*i+1] = a ^ ref_aes_xtime(b) ^ ref_aes_xtime(c) ^ c ^ d;
           s[4*i+2] = a ^ b ^ ref_aes_xtime(c) ^ ref_aes_xtime(d) ^ d;
           s[4*i+3] = ref_aes_xtime(a) ^ a ^ b ^ c ^ ref_aes_xtime(d);
         }
      }

     // AddRoundKey
     for (i = 0; i < 16; ++i) s[i] ^= rk[16*r + i];
   }

  memcpy(out, s, 16);
}

// ***************************************************************************
// GHASH primitives — adapted from aws-lc's gcm_nohw.c (gcm_polyval_nohw),
// which implements GHASH via byte-reflected POLYVAL multiplication. Same
// math the GCM spec describes; same H representation aws-lc's gcm_init_v8
// produces (with bits flowing in reverse and the high bit handled per the
// GCM spec).
// ***************************************************************************

static uint64_t load_u64_be(const uint8_t *p)
{ return ((uint64_t)p[0] << 56) | ((uint64_t)p[1] << 48) |
         ((uint64_t)p[2] << 40) | ((uint64_t)p[3] << 32) |
         ((uint64_t)p[4] << 24) | ((uint64_t)p[5] << 16) |
         ((uint64_t)p[6] << 8)  |  (uint64_t)p[7];
}

static void store_u64_be(uint8_t *p, uint64_t v)
{ p[0] = (uint8_t)(v >> 56); p[1] = (uint8_t)(v >> 48);
  p[2] = (uint8_t)(v >> 40); p[3] = (uint8_t)(v >> 32);
  p[4] = (uint8_t)(v >> 24); p[5] = (uint8_t)(v >> 16);
  p[6] = (uint8_t)(v >> 8);  p[7] = (uint8_t)v;
}

// 64-bit carry-less multiply, scalar bit-by-bit (clarity over speed)
static void clmul64(uint64_t *out_lo, uint64_t *out_hi, uint64_t a, uint64_t b)
{ uint64_t lo = 0, hi = 0;
  int i;
  for (i = 0; i < 64; ++i)
   { if ((b >> i) & 1)
      { lo ^= a << i;
        hi ^= (i == 0) ? 0 : (a >> (64 - i));
      }
   }
  *out_lo = lo;
  *out_hi = hi;
}

// Compute X * H mod the GHASH polynomial, where both X and H are stored as
// the (Xi_lo, Xi_hi) pair the assembly uses internally:
//   Xi_lo = bytes 8..15 of Xi loaded as big-endian uint64,
//   Xi_hi = bytes 0..7 of Xi loaded as big-endian uint64,
// and H is similarly the (H_lo, H_hi) pair derived from the raw H = AES_E(K, 0).
//
// This matches `gcm_polyval_nohw` in aws-lc (modulo carry-less mul backend).
static void gcm_polyval_ref(uint64_t Xi[2], uint64_t H_lo, uint64_t H_hi)
{ uint64_t r0, r1, r2, r3, mid0, mid1;

  clmul64(&r0, &r1, Xi[0], H_lo);
  clmul64(&r2, &r3, Xi[1], H_hi);
  clmul64(&mid0, &mid1, Xi[0] ^ Xi[1], H_hi ^ H_lo);
  mid0 ^= r0 ^ r2;
  mid1 ^= r1 ^ r3;
  r2 ^= mid1;
  r1 ^= mid0;

  // Reduce: same bit-flow trick as gcm_polyval_nohw.
  r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);
  r2 ^= r0;
  r3 ^= r1;
  r2 ^= r0 >> 1;
  r2 ^= r1 << 63;
  r3 ^= r1 >> 1;
  r2 ^= r0 >> 2;
  r2 ^= r1 << 62;
  r3 ^= r1 >> 2;
  r2 ^= r0 >> 7;
  r2 ^= r1 << 57;
  r3 ^= r1 >> 7;

  Xi[0] = r2;
  Xi[1] = r3;
}

// Twist H to match aws-lc's gcm_init_v8 / nohw representation: the raw
// 16-byte H = AES_E(K, 0) is loaded as two big-endian uint64s, then the
// "shift-by-1 with reduction" twist is applied so that the polynomial
// algebra works out without an extra shift in each multiplication.
static void gcm_twist_h(uint64_t out[2], const uint8_t H_raw[16])
{ uint64_t lo = load_u64_be(H_raw + 8);
  uint64_t hi = load_u64_be(H_raw);
  uint64_t carry = (uint64_t)0 - (hi >> 63);
  hi <<= 1;
  hi |= lo >> 63;
  lo <<= 1;
  lo ^= carry & 1;
  hi ^= carry & UINT64_C(0xc200000000000000);
  out[0] = lo;
  out[1] = hi;
}

// Compute the squared product (X * Y mod GHASH polynomial) where X, Y are
// twisted H-domain values. Used to populate H^2, H^3, H^4 in the Karatsuba
// Htable layout aws-lc's gcm_init_v8 produces.
static void gcm_polyval_pair(uint64_t result[2],
                             uint64_t X_lo, uint64_t X_hi,
                             uint64_t Y_lo, uint64_t Y_hi)
{ uint64_t r0, r1, r2, r3, mid0, mid1;

  clmul64(&r0, &r1, X_lo, Y_lo);
  clmul64(&r2, &r3, X_hi, Y_hi);
  clmul64(&mid0, &mid1, X_lo ^ X_hi, Y_lo ^ Y_hi);
  mid0 ^= r0 ^ r2;
  mid1 ^= r1 ^ r3;
  r2 ^= mid1;
  r1 ^= mid0;

  r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);
  r2 ^= r0;
  r3 ^= r1;
  r2 ^= r0 >> 1;
  r2 ^= r1 << 63;
  r3 ^= r1 >> 1;
  r2 ^= r0 >> 2;
  r2 ^= r1 << 62;
  r3 ^= r1 >> 2;
  r2 ^= r0 >> 7;
  r2 ^= r1 << 57;
  r3 ^= r1 >> 7;

  result[0] = r2;
  result[1] = r3;
}

// Build the standard aws-lc Karatsuba Htable layout from the AES-128 round
// keys. Layout (each entry is a 16-byte (lo, hi) pair, written here as
// uint64_t pairs at the indicated byte offset):
//
//   offset  0: H^1 (twisted)
//   offset 16: h12k (Karatsuba pre-processed mix of H^1 and H^2)
//   offset 32: H^2
//   offset 48: H^3
//   offset 64: h34k
//   offset 80: H^4
//   offset 96: H^5  (unused by encrypt kernel; populated for completeness)
//   offset 112: h56k (unused)
//   offset 128: H^6  (unused)
//   ...
//
// For the encrypt kernel under test we only need H^1, H^2, H^3, H^4
// populated correctly at offsets 0, 32, 48, 80; the kernel does not read
// the h12k/h34k slots (it computes Karatsuba pre-processing on the fly).
// We still populate them to a valid value so the layout matches what
// aws-lc's gcm_init_v8 produces.
static void ref_gcm_init_htable(uint64_t Htable[12*2],  // 12 × 16-byte slots
                                const s2n_bignum_AES_KEY *key)
{ uint8_t  H_raw[16];
  uint8_t  zero[16] = {0};
  uint64_t H1[2], H2[2], H3[2], H4[2];

  // H = AES_E(K, 0)
  ref_aes128_encrypt_block(zero, H_raw, key);

  // Twist H
  gcm_twist_h(H1, H_raw);
  // H^2 = H * H
  gcm_polyval_pair(H2, H1[0], H1[1], H1[0], H1[1]);
  // H^3 = H * H^2
  gcm_polyval_pair(H3, H1[0], H1[1], H2[0], H2[1]);
  // H^4 = H^2 * H^2
  gcm_polyval_pair(H4, H2[0], H2[1], H2[0], H2[1]);

  // Slot 0: H^1
  Htable[0] = H1[0]; Htable[1] = H1[1];
  // Slot 1: h12k (placeholder — not consulted by kernel)
  Htable[2] = H1[0] ^ H1[1]; Htable[3] = H2[0] ^ H2[1];
  // Slot 2: H^2
  Htable[4] = H2[0]; Htable[5] = H2[1];
  // Slot 3: H^3
  Htable[6] = H3[0]; Htable[7] = H3[1];
  // Slot 4: h34k (placeholder)
  Htable[8] = H3[0] ^ H3[1]; Htable[9] = H4[0] ^ H4[1];
  // Slot 5: H^4
  Htable[10] = H4[0]; Htable[11] = H4[1];
  // Slots 6..11 (H^5, h56k, H^6, H^7, h78k, H^8): not consulted by
  // the AES-128 encrypt kernel; zero them defensively.
  memset(&Htable[12], 0, 6 * 16);
}

// Update Xi by feeding it one 16-byte block. Matches the kernel: read Xi as
// big-endian (Xi_hi:Xi_lo), XOR in the new block (also big-endian), multiply
// by H.
static void gcm_ghash_block(uint8_t Xi[16], uint64_t H_lo, uint64_t H_hi,
                            const uint8_t *block)
{ uint64_t state[2];
  state[0] = load_u64_be(Xi + 8) ^ load_u64_be(block + 8);
  state[1] = load_u64_be(Xi)     ^ load_u64_be(block);
  gcm_polyval_ref(state, H_lo, H_hi);
  store_u64_be(Xi + 8, state[0]);
  store_u64_be(Xi, state[1]);
}

// ***************************************************************************
// Full AES-128-GCM end-to-end reference encrypt — used to validate the test
// scaffolding against published NIST vectors, and as the comparison driver
// for end-to-end KATs. Mirrors NIST SP 800-38D, Algorithm 4 (GCM-AE).
//
// nonce is 12 bytes (the only IV size we test against — sufficient for KATs).
// ***************************************************************************

static void ref_aes128_gcm_encrypt(const uint8_t key_bytes[16],
                                   const uint8_t nonce[12],
                                   const uint8_t *plaintext, size_t pt_len,
                                   const uint8_t *aad, size_t aad_len,
                                   uint8_t *ciphertext, uint8_t tag[16])
{ s2n_bignum_AES_KEY key;
  uint8_t  H_raw[16];
  uint8_t  zero[16] = {0};
  uint64_t H_lo, H_hi;
  uint64_t H_pair[2];
  uint8_t  Xi[16] = {0};
  uint8_t  J0[16];
  uint8_t  J0_plus1[16];
  uint8_t  EKJ0[16];
  uint8_t  len_block[16];
  uint8_t  ks_block[16];
  uint8_t  ctr_block[16];
  size_t   i, off;
  uint32_t ctr32;

  ref_aes128_expand_key(key_bytes, &key);

  // H = AES_E(K, 0^128); twist for the algebra layer
  ref_aes128_encrypt_block(zero, H_raw, &key);
  gcm_twist_h(H_pair, H_raw);
  H_lo = H_pair[0];
  H_hi = H_pair[1];

  // J0 = nonce || 0^31 || 1  (NIST 800-38D Section 7.1, |IV|=96 case)
  memcpy(J0, nonce, 12);
  J0[12] = 0; J0[13] = 0; J0[14] = 0; J0[15] = 1;

  // Y_1 = J0 + 1 (the kernel's initial counter)
  memcpy(J0_plus1, J0, 16);
  ctr32 = ((uint32_t)J0_plus1[12] << 24) |
          ((uint32_t)J0_plus1[13] << 16) |
          ((uint32_t)J0_plus1[14] << 8)  |
           (uint32_t)J0_plus1[15];
  ctr32 += 1;
  J0_plus1[12] = (uint8_t)(ctr32 >> 24);
  J0_plus1[13] = (uint8_t)(ctr32 >> 16);
  J0_plus1[14] = (uint8_t)(ctr32 >> 8);
  J0_plus1[15] = (uint8_t)ctr32;

  // GHASH AAD blocks
  for (off = 0; off + 16 <= aad_len; off += 16)
    gcm_ghash_block(Xi, H_lo, H_hi, aad + off);
  if (off < aad_len)
   { uint8_t pad[16] = {0};
     memcpy(pad, aad + off, aad_len - off);
     gcm_ghash_block(Xi, H_lo, H_hi, pad);
   }

  // CTR encrypt + GHASH ciphertext
  ctr32 = ((uint32_t)J0_plus1[12] << 24) |
          ((uint32_t)J0_plus1[13] << 16) |
          ((uint32_t)J0_plus1[14] << 8)  |
           (uint32_t)J0_plus1[15];
  for (off = 0; off + 16 <= pt_len; off += 16)
   { memcpy(ctr_block, J0_plus1, 12);
     ctr_block[12] = (uint8_t)(ctr32 >> 24);
     ctr_block[13] = (uint8_t)(ctr32 >> 16);
     ctr_block[14] = (uint8_t)(ctr32 >> 8);
     ctr_block[15] = (uint8_t)ctr32;
     ref_aes128_encrypt_block(ctr_block, ks_block, &key);
     for (i = 0; i < 16; ++i)
       ciphertext[off + i] = plaintext[off + i] ^ ks_block[i];
     gcm_ghash_block(Xi, H_lo, H_hi, ciphertext + off);
     ctr32 += 1;
   }
  if (off < pt_len)
   { uint8_t pad[16] = {0};
     size_t  rem = pt_len - off;
     memcpy(ctr_block, J0_plus1, 12);
     ctr_block[12] = (uint8_t)(ctr32 >> 24);
     ctr_block[13] = (uint8_t)(ctr32 >> 16);
     ctr_block[14] = (uint8_t)(ctr32 >> 8);
     ctr_block[15] = (uint8_t)ctr32;
     ref_aes128_encrypt_block(ctr_block, ks_block, &key);
     for (i = 0; i < rem; ++i)
       ciphertext[off + i] = plaintext[off + i] ^ ks_block[i];
     memcpy(pad, ciphertext + off, rem);
     gcm_ghash_block(Xi, H_lo, H_hi, pad);
   }

  // Final length block: 64-bit big-endian aad bit-len, 64-bit big-endian
  // ciphertext bit-len.
  store_u64_be(len_block,     (uint64_t)aad_len * 8);
  store_u64_be(len_block + 8, (uint64_t)pt_len  * 8);
  gcm_ghash_block(Xi, H_lo, H_hi, len_block);

  // Tag = AES_E(K, J0) XOR Xi
  ref_aes128_encrypt_block(J0, EKJ0, &key);
  for (i = 0; i < 16; ++i)
    tag[i] = EKJ0[i] ^ Xi[i];
}

// ***************************************************************************
// AES-128-GCM encrypt-kernel reference (full 16-byte blocks only).
//
// Mirrors the kernel signature exactly:
//   in       — plaintext bytes
//   bit_len  — length in bits (must be multiple of 128, > 0)
//   out      — ciphertext bytes (may alias in)
//   Xi_io    — running GHASH tag (16 bytes, big-endian)
//   ivec_io  — current GCM counter Y_i (16 bytes, with last 32 bits being
//              the big-endian counter that the kernel increments per block)
//   key      — AES-128 expanded key schedule (rounds=10, 11 round keys)
//   Htable   — standard aws-lc Karatsuba layout; only Htable[0] (twisted H)
//              is consulted by this reference.
// ***************************************************************************

static void ref_aes_gcm_enc_kernel(const uint8_t *in, uint64_t bit_len,
                                   uint8_t *out, uint64_t Xi_io[2],
                                   uint8_t ivec_io[16],
                                   const s2n_bignum_AES_KEY *key,
                                   const uint64_t *Htable)
{ uint64_t H_lo = Htable[0];
  uint64_t H_hi = Htable[1];
  uint64_t bytes = bit_len >> 3;
  uint64_t blocks = bytes >> 4;
  uint64_t b;
  uint8_t  *Xi_bytes = (uint8_t *)Xi_io;
  uint32_t  ctr32 = ((uint32_t)ivec_io[12] << 24) |
                    ((uint32_t)ivec_io[13] << 16) |
                    ((uint32_t)ivec_io[14] <<  8) |
                     (uint32_t)ivec_io[15];

  for (b = 0; b < blocks; ++b)
   { uint8_t ctr_block[16];
     uint8_t keystream[16];
     uint8_t cblock[16];
     int     i;

     // Build the current counter block: top 12 bytes are unchanged,
     // bottom 4 bytes are ctr32 in big-endian.
     memcpy(ctr_block, ivec_io, 12);
     ctr_block[12] = (uint8_t)(ctr32 >> 24);
     ctr_block[13] = (uint8_t)(ctr32 >> 16);
     ctr_block[14] = (uint8_t)(ctr32 >>  8);
     ctr_block[15] = (uint8_t)(ctr32 >>  0);

     ref_aes128_encrypt_block(ctr_block, keystream, key);

     // Ciphertext = plaintext XOR keystream
     for (i = 0; i < 16; ++i)
       cblock[i] = in[16*b + i] ^ keystream[i];

     memcpy(out + 16*b, cblock, 16);

     // GHASH-update on the ciphertext block
     gcm_ghash_block(Xi_bytes, H_lo, H_hi, cblock);

     // Increment the 32-bit big-endian counter (with wrap)
     ctr32 += 1;
   }

  // Write back the updated counter to ivec_io. The kernel writes back its
  // last-used counter as a 16-byte big-endian value with the trailing
  // 32 bits being the *next* counter (i.e. ctr32 after the loop).
  ivec_io[12] = (uint8_t)(ctr32 >> 24);
  ivec_io[13] = (uint8_t)(ctr32 >> 16);
  ivec_io[14] = (uint8_t)(ctr32 >>  8);
  ivec_io[15] = (uint8_t)(ctr32 >>  0);
}
