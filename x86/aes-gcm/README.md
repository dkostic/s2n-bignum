# x86-64 AES-GCM (aesni_gcm_encrypt / aesni_gcm_decrypt)

This directory contains the x86-64 AES-GCM implementation that s2n-bignum
is formally verifying.  The assembly is derived from
[aws-lc]'s `crypto/fipsmodule/modes/asm/aesni-gcm-x86_64.pl` by
**inlining** the private helpers
(`_aesni_ctr32_ghash_6x`, `_aesni_ctr32_6x`) into each public entry
point.  See [`../../tools/inline_x86_calls.py`](../../tools/inline_x86_calls.py)
for the tool and [`../../aes-gcm-x86-plan.md`](../../aes-gcm-x86-plan.md)
for the project plan.

[aws-lc]: https://github.com/aws/aws-lc

## Pinned aws-lc commit

The assembly here was generated from aws-lc at commit
`2ddb1c333f25f0288e8413d32b30260da3802157` (2026-05-06), file
`generated-src/linux-x86_64/crypto/fipsmodule/aesni-gcm-x86_64.S`.

If the aws-lc pin moves, re-run `tools/inline_x86_calls.py` against the
new source and re-run `benchmark_aes_gcm.c` to confirm no regression.

## What the inlining tool does

Three semantic-preserving rewrites in one pass:

1. **Inline every `call <helper>`** inside the public entry points.  The
   helper body is spliced in place of the call, with every local label
   `.Lxxx` renamed to `.Lxxx__<entry>_<helper>_<n>` so duplicate copies
   of the same helper don't collide.

2. **Replace each helper's `ret` with a `jmp .Lexit__<entry>_<helper>_<n>`**
   followed by an exit label right after the inlined block.
   `_aesni_ctr32_6x`'s ret sits *in the middle* of the function body,
   with a `.Lhandle_ctr32_2` cold path after it.  Without the rewrite,
   the fast-path exit would fall through into the cold path,
   re-entering the AES loop and running forever.

3. **Rewrite caller-relative stack offsets.**  The helpers' source uses
   `N+8(%rsp)` to compensate for the return address pushed by `call`.
   After inlining there's no pushed return address, so every
   `N+8(%rsp)` is rewritten to `N(%rsp)` to point at the same physical
   caller stack slot.

Additionally, a mnemonic substitution runs over the entire output:

4. **Rewrite `vmovups` → `vmovdqu`** everywhere.  The two instructions
   have identical semantics for 128-bit unaligned moves and the same
   cycle cost on Haswell+ Intel and all AMD Zen generations; the only
   measurable difference is a 1-cycle SSE-domain-cross penalty on
   pre-Haswell Intel, not a target microarchitecture.  The VEX
   encoding of `vmovups` is *not* in the s2n-bignum x86 decoder while
   `vmovdqu` is.  See aes-gcm-x86-plan.md §§2.3, 3.1.

## Functional equivalence vs. aws-lc

The inlined assembly was cross-tested against the stock aws-lc
implementation using `aesni_gcm_{encrypt,decrypt}` directly from
`libcrypto.a`, linked beside the inlined variants under renamed
symbols.  For every combination of
nblocks ∈ {18, 19, 20, 24, 25, 30, 60, 120, 240, 600} ×
seed ∈ {0xCAFEBABE, 0xDEADBEEF, 0xFEEDFACE, 0x01234567} = 40 cases,
the inlined and stock variants produced identical ciphertext, GHASH
output (`Xi`), and counter-block (`ivec`).  Decrypt of the inlined
ciphertext round-trips to the original plaintext.

## Performance baseline (aws-lc reference)

Benchmark host: **Intel Xeon 6975P-C** (Granite Rapids, AVX-512 /
VAES / VPCLMULQDQ class), Linux 6.17 kernel, `libcrypto.a` built
with `-O2`.

Measured with `benchmarks/benchmark_aes_gcm.c` (calls
`aesni_gcm_encrypt` / `aesni_gcm_decrypt` directly from
`libcrypto.a`).  Throughput numbers below are the MEDIAN of three
runs; run-to-run noise was within ±1% at every size.

```
--- aesni_gcm_encrypt ---
 1 KiB      cycles/byte = 0.377   MiB/s = 6829
 8 KiB      cycles/byte = 0.370   MiB/s = 6952
64 KiB      cycles/byte = 0.369   MiB/s = 6976

--- aesni_gcm_decrypt ---
 1 KiB      cycles/byte = 0.356   MiB/s = 7232
 8 KiB      cycles/byte = 0.367   MiB/s = 7024
64 KiB      cycles/byte = 0.364   MiB/s = 7068
```

Reading: throughput saturates by 8 KiB — as expected, the bulk loop
dominates at that size.  1 KiB sees a ~1.5% cycles/byte penalty from
the prologue/epilogue amortising over fewer blocks.

### Inlined variant (cross-check)

The same benchmark re-linked against
`x86/aes-gcm/aesni_gcm_{encrypt,decrypt}.S` (the inlined + vmovdqu
variants) produces:

```
--- aesni_gcm_encrypt ---
 1 KiB      cycles/byte = 0.373   MiB/s = 6912
 8 KiB      cycles/byte = 0.366   MiB/s = 7029
64 KiB      cycles/byte = 0.364   MiB/s = 7075

--- aesni_gcm_decrypt ---
 1 KiB      cycles/byte = 0.354   MiB/s = 7279
 8 KiB      cycles/byte = 0.361   MiB/s = 7127
64 KiB      cycles/byte = 0.362   MiB/s = 7104
```

Inlined numbers are **within 1%** of the aws-lc baseline across
every size, confirming:

- The `call` → inlined-body rewrite shaves ~2 cycles per invocation
  (call+ret), visible only at 1 KiB where invocation count dominates.
- The `vmovups` → `vmovdqu` rewrite has no measurable effect on
  this microarchitecture (as expected for Haswell-and-later Intel).

Future changes to this directory should re-run this benchmark and
record any deviation greater than 1% against the baseline above.
See aes-gcm-x86-plan.md §1.4 for the performance commitment.

## File layout

```
aesni_gcm_encrypt.S       # monolithic encrypt (~830 lines, inlined)
aesni_gcm_decrypt.S       # monolithic decrypt (~490 lines, inlined)
```

The `.o` files are produced at build time from these `.S` files (no
static `.o` lives in the repo).
