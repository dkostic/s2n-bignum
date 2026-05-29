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
// GHASH primitives — direct emulation of aws-lc's `gcm_init_v8` and the
// per-block GHASH update inside `aes_gcm_enc_kernel`. The byte conventions
// these use are NOT the same as `gcm_init_nohw`/`gcm_polyval_nohw` (see the
// extended commentary on `ref_gcm_init_htable` below).
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

static uint64_t load_u64_le(const uint8_t *p)
{ return  (uint64_t)p[0]        | ((uint64_t)p[1] << 8) |
         ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24) |
         ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40) |
         ((uint64_t)p[6] << 48) | ((uint64_t)p[7] << 56);
}

static void store_u64_le(uint8_t *p, uint64_t v)
{ p[0] = (uint8_t) v;        p[1] = (uint8_t)(v >> 8);
  p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);
  p[4] = (uint8_t)(v >> 32); p[5] = (uint8_t)(v >> 40);
  p[6] = (uint8_t)(v >> 48); p[7] = (uint8_t)(v >> 56);
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

// gcm_init_v8 twist on a (lo, hi) pair where the inputs come from LE-load of
// H_raw bytes (with halves already swapped via vext). Same algebra as
// gcm_polyval_nohw's twist, just applied to LE-loaded integers instead of
// BE-loaded ones.
static void gcm_v8_twist(uint64_t *out_lo, uint64_t *out_hi,
                         uint64_t lo, uint64_t hi)
{ uint64_t carry = (uint64_t)0 - (hi >> 63);
  uint64_t new_hi = (hi << 1) | (lo >> 63);
  uint64_t new_lo = (lo << 1) ^ (carry & 1);
  new_hi ^= carry & UINT64_C(0xc200000000000000);
  *out_lo = new_lo;
  *out_hi = new_hi;
}

// Multiply two H-domain values in v8-internal pair form. Output is the
// internal pair of the resulting product H^(j+k).
static void gcm_v8_polymul(uint64_t *res_lo, uint64_t *res_hi,
                           uint64_t a_lo, uint64_t a_hi,
                           uint64_t b_lo, uint64_t b_hi)
{ uint64_t r0, r1, r2, r3, mid0, mid1;

  clmul64(&r0, &r1, a_lo, b_lo);
  clmul64(&r2, &r3, a_hi, b_hi);
  clmul64(&mid0, &mid1, a_lo ^ a_hi, b_lo ^ b_hi);
  mid0 ^= r0 ^ r2;
  mid1 ^= r1 ^ r3;
  r2 ^= mid1;
  r1 ^= mid0;

  // Same reduction as gcm_polyval_nohw — works because the polynomial
  // ring algebra is independent of the byte-encoding. This reduces (r0..r3)
  // (a 256-bit accumulator) modulo the GHASH polynomial.
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

  *res_lo = r2;
  *res_hi = r3;
}

// Read v8-formatted Htable[i] (16 bytes at the given pointer) into the
// kernel-internal pair (IN_lo, IN_hi). Inverse of v8_htable_store.
static void v8_htable_load(uint64_t *IN_lo, uint64_t *IN_hi,
                           const uint8_t htable_bytes[16])
{ *IN_hi = load_u64_le(htable_bytes);
  *IN_lo = load_u64_le(htable_bytes + 8);
}

// Pack an internal pair (IN_lo, IN_hi) into the 16-byte v8 layout (this
// applies the final vext.8 H,H,#8 swap and the LE store).
static void v8_htable_store(uint8_t htable_bytes[16],
                            uint64_t IN_lo, uint64_t IN_hi)
{ store_u64_le(htable_bytes,     IN_hi);
  store_u64_le(htable_bytes + 8, IN_lo);
}

// Compute one GHASH update: Xi := (Xi XOR block) * H mod GHASH-poly.
// The byte conventions mirror the kernel exactly:
//   - Xi[16] is the NIST-spec byte form (same as the kernel's [x3] memory
//     view of Xi);
//   - block[16] is also NIST-spec byte form (raw ciphertext);
//   - (H_lo, H_hi) is the kernel-internal pair, NOT a NIST-byte form. Use
//     v8_htable_load on Htable[0..15] to obtain it.
//
// Internally we apply the same vext+vrev64 transform the kernel does to
// convert Xi between NIST-byte form and the internal pair, multiply by H
// in pair form, then transform back.
static void gcm_ghash_block_v8(uint8_t Xi[16], const uint8_t *block,
                               uint64_t H_lo, uint64_t H_hi)
{ uint8_t  combined[16];
  uint64_t Xi_lo, Xi_hi, res_lo, res_hi;
  size_t   i;

  for (i = 0; i < 16; ++i) combined[i] = Xi[i] ^ block[i];

  // Transform NIST-byte combined to internal pair: vld1; vext; vrev64.
  //   t1.d[0] = LE-load(combined[ 0.. 7])
  //   t1.d[1] = LE-load(combined[ 8..15])
  //   IN.d[0] = t1.d[1]                 (after vext)
  //   IN.d[1] = t1.d[0]
  //   IN.d[k] = bswap(IN.d[k])          (vrev64 within each lane)
  Xi_lo = __builtin_bswap64(load_u64_le(combined + 8));
  Xi_hi = __builtin_bswap64(load_u64_le(combined));

  gcm_v8_polymul(&res_lo, &res_hi, Xi_lo, Xi_hi, H_lo, H_hi);

  // Inverse transform: vext; vrev64; vst1.
  {
    uint64_t v_after_ext_d0 = res_hi;        // vext: swap halves
    uint64_t v_after_ext_d1 = res_lo;
    uint64_t v_after_rev64_d0 = __builtin_bswap64(v_after_ext_d0);
    uint64_t v_after_rev64_d1 = __builtin_bswap64(v_after_ext_d1);
    store_u64_le(Xi,     v_after_rev64_d0);
    store_u64_le(Xi + 8, v_after_rev64_d1);
  }
}

// Build an Htable in the exact byte layout that aws-lc's gcm_init_v8
// assembly produces, mirroring the kernel's expectations:
//
//   offset  0: H^1   (v8 internal pair, stored as (IN_hi, IN_lo) in LE bytes)
//   offset 16: h12k  (Karatsuba pre-processed; not read by encrypt kernel)
//   offset 32: H^2
//   offset 48: H^3
//   offset 64: h34k
//   offset 80: H^4
//   offsets 96..191: H^5..H^8 + their Karatsuba pairs (not read by encrypt
//                    kernel; zeroed)
static void ref_gcm_init_htable(uint64_t Htable[12*2],  // 12 × 16-byte slots
                                const s2n_bignum_AES_KEY *key)
{ uint8_t  H_raw[16];
  uint8_t  zero[16] = {0};
  uint64_t t1_d0, t1_d1, IN_d0, IN_d1;
  uint64_t H1_lo, H1_hi, H2_lo, H2_hi, H3_lo, H3_hi, H4_lo, H4_hi;
  uint8_t *htable_bytes = (uint8_t *)Htable;

  // H = AES_E(K, 0)
  ref_aes128_encrypt_block(zero, H_raw, key);

  // Replicate gcm_init_v8's prologue:
  //   t1 = vld1(H_raw)            -- t1.d[0] = LE-load(H_raw[0..7]),
  //                                  t1.d[1] = LE-load(H_raw[8..15])
  //   IN = vext(t1, t1, #8)        -- IN.d[0] = t1.d[1], IN.d[1] = t1.d[0]
  t1_d0 = load_u64_le(H_raw);
  t1_d1 = load_u64_le(H_raw + 8);
  IN_d0 = t1_d1;
  IN_d1 = t1_d0;

  // Twist (lo, hi) = (IN.d[0], IN.d[1]) -> (twisted_lo, twisted_hi). The
  // kernel-internal (H_lo, H_hi) pair is (twisted_lo, twisted_hi), used
  // as-is in the polymul; the byte memory layout has them swapped via the
  // final vext.8.
  gcm_v8_twist(&H1_lo, &H1_hi, IN_d0, IN_d1);

  // H^2 = H * H, H^3 = H * H^2, H^4 = H^2 * H^2
  gcm_v8_polymul(&H2_lo, &H2_hi, H1_lo, H1_hi, H1_lo, H1_hi);
  gcm_v8_polymul(&H3_lo, &H3_hi, H1_lo, H1_hi, H2_lo, H2_hi);
  gcm_v8_polymul(&H4_lo, &H4_hi, H2_lo, H2_hi, H2_lo, H2_hi);

  // Store at the v8 byte offsets. v8_htable_store handles the final
  // vext.8 H,H,#8 swap and the LE-store for memory.
  v8_htable_store(htable_bytes +   0, H1_lo, H1_hi);    // slot 0
  v8_htable_store(htable_bytes +  16, H1_lo, H2_lo);    // slot 1: h12k (placeholder)
  v8_htable_store(htable_bytes +  32, H2_lo, H2_hi);    // slot 2: H^2
  v8_htable_store(htable_bytes +  48, H3_lo, H3_hi);    // slot 3: H^3
  v8_htable_store(htable_bytes +  64, H3_lo, H4_lo);    // slot 4: h34k (placeholder)
  v8_htable_store(htable_bytes +  80, H4_lo, H4_hi);    // slot 5: H^4
  // Slots 6..11 (H^5, h56k, H^6, H^7, h78k, H^8): zeroed (encrypt kernel
  // does not read them).
  memset(htable_bytes + 96, 0, 96);
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

  // H = AES_E(K, 0^128); compute v8-internal (H_lo, H_hi) pair the same
  // way gcm_init_v8 does, so the GHASH update agrees with the kernel.
  {
    uint64_t IN_d0, IN_d1;
    ref_aes128_encrypt_block(zero, H_raw, &key);
    IN_d0 = load_u64_le(H_raw + 8);   // after vext.8 swap of LE-loaded halves
    IN_d1 = load_u64_le(H_raw);
    gcm_v8_twist(&H_lo, &H_hi, IN_d0, IN_d1);
  }

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
    gcm_ghash_block_v8(Xi, aad + off, H_lo, H_hi);
  if (off < aad_len)
   { uint8_t pad[16] = {0};
     memcpy(pad, aad + off, aad_len - off);
     gcm_ghash_block_v8(Xi, pad, H_lo, H_hi);
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
     gcm_ghash_block_v8(Xi, ciphertext + off, H_lo, H_hi);
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
     gcm_ghash_block_v8(Xi, pad, H_lo, H_hi);
   }

  // Final length block: 64-bit big-endian aad bit-len, 64-bit big-endian
  // ciphertext bit-len.
  store_u64_be(len_block,     (uint64_t)aad_len * 8);
  store_u64_be(len_block + 8, (uint64_t)pt_len  * 8);
  gcm_ghash_block_v8(Xi, len_block, H_lo, H_hi);

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
{ // Decode H^1 from the v8-format Htable[0] (16 bytes at offset 0) into
  // the (H_lo, H_hi) internal pair.
  uint64_t H_lo, H_hi;
  uint64_t bytes = bit_len >> 3;
  uint64_t blocks = bytes >> 4;
  uint64_t b;
  uint8_t  *Xi_bytes = (uint8_t *)Xi_io;
  uint32_t  ctr32 = ((uint32_t)ivec_io[12] << 24) |
                    ((uint32_t)ivec_io[13] << 16) |
                    ((uint32_t)ivec_io[14] <<  8) |
                     (uint32_t)ivec_io[15];

  v8_htable_load(&H_lo, &H_hi, (const uint8_t *)Htable);

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

     // GHASH-update on the ciphertext block (using the v8-internal H
     // representation that matches the kernel's bytes at Htable[0]).
     gcm_ghash_block_v8(Xi_bytes, cblock, H_lo, H_hi);

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
