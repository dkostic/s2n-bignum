# Verified `sha1_block_data_order_hw`

A formal, machine-checked correctness proof of an aarch64 SHA-1
hardware-accelerated multi-block compression routine, in HOL Light against
the s2n-bignum ARMv8 ISA model. Performance-equivalent with aws-lc's
analogous routine on Neoverse-V2.

## What's proven

Three theorems, all with empty hypothesis lists, on top of HOL Light's three
standard axioms (`INFINITY_AX`, `SELECT_AX`, `ETA_AX`) — no `CHEAT_TAC`,
`mk_thm`, `new_axiom`, or `SORRY_TAC` anywhere in the SHA-1 proof files.

1. **`SHA1_HW_CORRECT`** — `arm/proofs/sha1_block_data_order_hw_ensures.ml`.
   The routine starting at PC processes `num_blocks` 16-word blocks (each
   loaded into Q-registers as `word_join4` of bytereversed int32s) starting
   from a 5-word state, and the final state buffer at `state_ptr` equals
   `sha1_hash_blocks num_blocks blocks [a;b;c;d;e]` per FIPS 180-4. Stated
   as an `ensures arm` over the multi-block loop with a worked-out
   invariant tracking Q0/Q1 state, K-band registers Q16–Q19, and the data
   buffer.

2. **`SHA1_HW_SUBROUTINE_CORRECT`** — same file. Lifts (1) to a callable
   subroutine via `ARM_ADD_RETURN_NOSTACK_TAC`: precondition includes
   `read X30 s = returnaddress`, postcondition is `read PC s =
   returnaddress`. This is the contract a caller actually uses.

3. **`SHA1_HW_BYTES_SUBROUTINE_CORRECT`** —
   `arm/proofs/sha1_block_data_order_hw_public.ml`. The public-facing
   theorem: precondition states the data buffer as a flat `byte list` of
   length `64 * num_blocks` (no per-block int32 decomposition exposed to
   the caller), postcondition is `sha1_hash_bytes num_blocks data_bytes
   [a;b;c;d;e]`. Discharged from (2) via byte-to-int32 bridging lemmas
   and `MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM)` —
   same idiom as the `bignum_bigendian_*` / `bignum_littleendian_*`
   wrappers in s2n-bignum.

The byte-level spec `sha1_hash_bytes` is whole-blocks-only — it does not
include the FIPS one-shot padding/length-tagging step. That's the
caller's responsibility (or a future higher-level wrapper) and was
deliberately scoped out.

## Soundness gate

`~/whole-proofs/orchestrator/logs/artifacts/session-022-verify.log`
(~1M lines, captured under fresh-load `loadt` on a clean HOL Light
session, ~46 min wall-clock):

- `axioms ()` returns exactly the 3 standard HOL Light axioms.
- `hyp SHA1_HW_CORRECT = []`.
- `hyp SHA1_HW_SUBROUTINE_CORRECT = []`.
- `hyp SHA1_HW_BYTES_SUBROUTINE_CORRECT = []`.

The full proof is now wired into the s2n-bignum Makefile, so
`make sha1/sha1_block_data_order_hw.correct` re-runs the proof end-to-end
(~15 min; .correct binds `SHA1_HW_BYTES_SUBROUTINE_CORRECT` and registered
in `arm/proofs/specifications.txt`).

## The implementation

`arm/sha1/sha1_block_data_order_hw.S` (255 lines). Modeled on aws-lc's
`generated-src/linux-aarch64/crypto/fipsmodule/sha1-armv8.S`, but takes
the K table as a register-loaded pointer (X3) rather than ADRP-relative
read-only data — matching s2n-bignum's SHA-256 HW pilot's calling
convention:

```c
extern void sha1_block_data_order_hw(uint32_t state[static 5],
                                     const uint8_t *data,
                                     uint64_t num_blocks,
                                     const uint32_t k[static 16]);
```

Uses the ARMv8 SHA-1 HW intrinsics (`SHA1H`, `SHA1C`, `SHA1P`, `SHA1M`,
`SHA1SU0`, `SHA1SU1`) plus `REV32` for the per-block big-endian
byteswap. Whole-blocks-only — caller pads.

## Performance

Head-to-head microbench (`tests/sha1_hw_bench.c` against
`tests/awslc_sha1_armv8.S`, a renamed copy of aws-lc's symbol). Outputs
agree byte-for-byte across 1, 2, 8, 64, 1024 blocks. Best-of-5 over
100k inner reps on aarch64 Neoverse-V2:

| blocks | s2n ns/B | awslc ns/B | ratio |
|-------:|---------:|-----------:|------:|
|      1 |   0.6272 |     0.6160 | 1.018 |
|      2 |   0.6044 |     0.5989 | 1.009 |
|      8 |   0.5876 |     0.5863 | 1.002 |
|     64 |   0.5827 |     0.5825 | 1.000 |
|   1024 |   0.5822 |     0.5822 | 1.000 |

At steady state (≥64 blocks), parity. The ~1–2% penalty at 1–2 blocks
is the extra K-pointer arg vs. the ADRP-relative load — amortized away
at any realistic batch size.

## How it was done

A 22-session orchestrated run:

- **Phases 0a–0c**: ARM ISA semantics for `SHA1*` instructions
  (`arm/proofs/sha1.ml`); decoder entries; simulator round-trip /
  iclasses gate (closed at commit `9c164d13`).
- **Phase 1**: FIPS 180-4 functional spec
  (`arm/proofs/utils/sha1_spec.ml`).
- **Phase 2**: bridging lemmas between ISA semantics and FIPS spec
  (`arm/proofs/utils/sha1_bridge.ml`), e.g. `SHA1H_BRIDGE`,
  `SHA1C_BRIDGE`, `SHA1P_BRIDGE`, `SHA1M_BRIDGE`, `SHA1SU_BRIDGE`.
- **Phase 3**: implementation file (`arm/sha1/sha1_block_data_order_hw.S`).
- **Phase 4**: KAT gate.
- **Phases 5–6**: pilot ensures lemmas — 4 register-only rounds, then
  with K constants loaded.
- **Phase 7**: full single-block correctness with cut-points at 4 round
  boundaries (`arm/proofs/sha1_block_core.ml` for cut-point machinery,
  `arm/proofs/sha1_block_data_order_hw.ml` for per-round-group
  ensures).
- **Phase 8**: multi-block loop, the `ensures` for the whole routine.
- **Phase 9**: byte-level public theorem (this commit chain).
- **Phase 10**: Makefile entry (this commit). Round-group-14 cosmetic
  comment + full CI re-run still deferred.

The hardest single problem was Phase 7's BODY closer (4 sessions blocked
on it): `RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ASSUME t])` at the loop body
was destructively rewriting the q1_lane_init invariant against itself,
leaving the closer's `ASM_REWRITE_TAC` with nothing to grab. The fix
(session 020) was to reintroduce the equation at the closer via
`ONCE_REWRITE_TAC[ASSUME ...]`, sound because the same equation is
already in the THM-level hyp set of every assumption that got rewritten.

## Layout

```
arm/sha1/sha1_block_data_order_hw.S            implementation
arm/proofs/sha1.ml                             ARM SHA-1 instruction semantics
arm/proofs/utils/sha1_spec.ml                  FIPS 180-4 spec + byte-level entry
arm/proofs/utils/sha1_bridge.ml                ISA-to-spec + bytes-to-int32 bridges
arm/proofs/sha1_block_core.ml                  cut-point machinery
arm/proofs/sha1_block_data_order_hw.ml         Phase 5/6 lemmas + per-round-group ensures
arm/proofs/sha1_block_data_order_hw_ensures.ml SHA1_HW_CORRECT + SHA1_HW_SUBROUTINE_CORRECT
arm/proofs/sha1_block_data_order_hw_public.ml  SHA1_HW_BYTES_SUBROUTINE_CORRECT
tests/sha1_hw_bench.c                          head-to-head benchmark vs aws-lc
tests/awslc_sha1_armv8.S                       renamed copy of aws-lc's symbol
```
