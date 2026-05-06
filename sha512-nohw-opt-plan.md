# SHA-512 nohw performance plan: close the gap to aws-lc

## Goal

Bring `sha512_block_data_order_nohw` within **5%** of aws-lc's scalar
performance on the target hardware (Graviton-class aarch64).

Current baseline (committed on branch `sha512-arm-nohw`, commit
`3f411a65`):

| implementation | ns/block | MB/s | vs aws-lc |
|---|---|---|---|
| aws-lc scalar  | ~203 | 630 | — |
| s2n-bignum sha512_nohw (baseline) | 347.5 | 368 | **1.71× slower** |
| s2n-bignum sha512_hw (FEAT_SHA512) | 118.4 | 1080 | n/a |

Target: **≤ 213 ns/block** (≈ 600 MB/s), i.e. ≥ 1.63× speedup.

Hardware: Graviton 3 (Neoverse V1), assumed for all timing figures.

## Root cause of the gap

Comparing aws-lc's `sha512-armv8.pl nohw` to our baseline, three
structural differences account for essentially all of the 1.71× gap:

1. **Schedule lives in registers, not stack.** aws-lc keeps a 16-word
   sliding window across x-registers (`x3..x15` plus `x0..x2` reused
   after spilling ctx/end pointers to the frame at `[x29,#96]` and
   `[x29,#112]`). We do `ldr x,[sp,#off]` + `str x,[sp,#off]` for every
   schedule read/write in both Phase B (64 loads + 64 stores) and Phase
   D (80 `ldr` for `W_t`).

2. **Schedule extend fused into compression.** aws-lc computes
   `W[i+17]` inside round `i`'s body for i = 15..78 (rounds 0..14 just
   load, round 79 just compresses). The OoO backend co-schedules the
   schedule sigma chain (independent from the compression T1/T2 chain)
   with the serial Sigma/Ch/Maj dependency. Our Phase B is a separate
   64-iteration loop before Phase D starts.

3. **Merged rotate-XOR ops.** aws-lc uses the ARM8 `eor xd,xn,xm,ror#k`
   form wherever possible (1 insn per ROR+XOR pair); we emit `ror`+`eor`
   as two separate instructions. SHA-512's 6 rotations per round
   (3 Sigma1, 3 Sigma0) plus 4 per schedule step (2 sigma0, 2 sigma1)
   mean significant instruction-count savings.

These three compose: (1) removes ~144 memory ops per block, (2) unlocks
ILP the narrow compression chain otherwise bottlenecks, (3) reduces
instruction count. The SHA-256 scalar family measured exactly this
progression: nohw baseline → nohw4 (fused) gave **1.36–1.39×**.

## Strategy: two staged variants

We build the optimised variants one at a time, benchmarking after each.
Stop at the first one that hits the ≤ 213 ns/block target.

### Variant 1 — `sha512_block_data_order_nohw2`

Analogue of SHA-256 `nohw5` (W-in-regs) + SHA-256 `nohw4` (fused B+D).
Applies all three fixes from the root-cause analysis simultaneously.

**Design:**

- **State registers**: `x20..x27` (= a..h), unchanged from baseline.
- **Schedule window**: 16 x-regs `x3..x15` + `x0`, `x1`, `x2` reused.
  The ctx pointer X0 and num/end are spilled to the frame at
  `[x29,#96]` and `[x29,#112]` during the block body (restored at
  block-tail / final exit). Schedule slot `t mod 16` lives in a fixed
  register; no sliding.
- **Fused body**: each round `t` in 15..78 computes `W[t+17]`
  alongside the Sigma/Ch/Maj chain. Rounds 0..14 are unrolled with
  just load+compress; round 79 is compress-only. This matches aws-lc's
  `BODY_00_xx` macro structure (SHA-256 nohw4 did the same).
- **Merged rotates**: use `eor xd,xn,xm,ror#k` throughout.
- **Callee-saves**: still x19..x28 (aws-lc uses x19..x28 too).

**Expected perf**: 220–245 ns/block (1.42–1.58× speedup).

  - If it lands at ≤ 213 ns, variant 2 is skipped.
  - Most likely: 220–230 ns, 8–12% gap remaining → proceed to variant 2.

**Proof strategy**: direct 64-bit port of
`arm/proofs/sha256_block_data_order_nohw5.ml`. Ref memory entries
transfer directly:
  - `feedback_nohw5_generic_p_round0.md` — generic-p round body tactic
  - `feedback_nohw5_list_8_compress.md` — LIST_8_COMPRESS destructuring
  - `feedback_nohw5_dtail_tactic.md` — D-tail closure
  - `feedback_nohw5_round_pattern.md` — full end-to-end closure
  - `feedback_nohw5_schedule_mono.md` — schedule-mono bridge for k≥1
  - `feedback_nohw5_round_k_specialize.md` — K specialization per round

SHA-256 nohw5 is 5809 lines. At 80 rounds + 64-bit (drops the
word_zx:int32->int64 gymnastics) expect **~5800–6200 lines**.

**Estimated effort**: 1 session for assembly + tests + benchmark; 2–3
sessions for proof (first load attempt + iterate on breakages).

### Variant 2 — `sha512_block_data_order_nohw3` (only if needed)

Only built if Variant 1 doesn't close the gap.

Analogue of SHA-256 `nohw6` (cyclic state naming). Eliminates the
7 `mov x11,x10; mov x10,x9; ...` state-rotation movs at the end of
each round body (~560 movs/block removed).

**Design:** at round `t` with `k = t mod 8`, position `j` of the
logical state `[a;b;c;d;e;f;g;h]` lives in register `x[4 + ((j-k) mod 8)]`.
8 distinct round macros `ROUND_SCHED_K0..K7` (and `ROUND_NOSCHED_K0..K7`
for rounds 64..79 after schedule finishes).

**Expected gain**: additional **5–8%** → 205–215 ns. On Neoverse-V1,
register moves are zero-latency on rename, so the benefit is
instruction-count only (frontend bandwidth). SHA-256 nohw5→nohw6 got
**1.05×** which matches.

**Proof strategy**: port
`arm/proofs/sha256_block_data_order_nohw6.ml` (5812 lines). Core hazard
is the 8-way cyclic rotation destructuring — SHA-256 nohw6 built it
once and ran through a Python generator for 2..15. Memory entry
`project_nohw6_progress.md` captures the full tactic.

**Estimated effort**: 1 session assembly; 2–3 sessions proof.

**Expected total line count**: ~6000–6500.

## Why not something else

**Why not rewrite one-shot into cyclic + fused (skip nohw2)?** Each
optimisation carries a distinct proof hazard. nohw5's register-resident
schedule broke the memory-specialisation pattern (`read (memory :>
bytes32 (word_add sp (word 4t))) s = EL t W` no longer present);
nohw6's cyclic rename broke the canonical state `[a;b;c;d;e;f;g;h]`.
Stacking them would confound debugging. Incremental variants keep each
32→64 lift cheap.

**Why not a NEON variant?** aws-lc's nohw is scalar; the FEAT_SHA512 hw
path already uses SIMD. A Neon-scalar hybrid would be a third
implementation axis (scalar vs. NEON vs. SHA-512 hw) and adds complexity
without a clear perf target — FEAT_SHA512 absence implies older µarchs
where Neon SHA-512 code is typically not the fastest scalar option.

**Why not tune the existing nohw (instruction scheduling only)?** We
already measured nohw = 347 ns with ~118 instructions per round
(baseline design). Getting to 213 ns would need removing ~1/3 of the
instruction stream, which is exactly what nohw2's three fixes provide.
Micro-tuning without structural changes gets <10%.

## Phase breakdown

### Phase N2-0 — nohw2 assembly + tests

**Inputs**: aws-lc `sha512-armv8.pl` BODY_00_xx macro for register
layout; existing SHA-256 `sha256_block_data_order_nohw5.S` for
s2n-bignum conventions.

**Outputs**:
- `arm/sha2/sha512_block_data_order_nohw2.S` (~500 lines, ~700 insns)
- `arm/Makefile` entry
- `include/s2n-bignum.h` extern
- `tests/test.c`: add `sha512_block_data_order_nohw2` to the test dispatcher
  and the existing `test_sha512_block_data_order_nohw` harness as a
  parallel cross-check
- `benchmarks/benchmark.c`: call harness + timingtests
- `tools/collect-signatures.py`: entry

**Exit criteria**: NIST "abc" KAT + 370 random 1-block + 2-block
cross-checks pass. Benchmark measured and recorded.

**Checkpoint**: if nohw2 ≤ 213 ns/block, skip to Phase N2-3.

### Phase N2-1 — nohw2 proof (straight-line)

**Inputs**: Phase N2-0 assembly; `utils/sha512_bridge.ml`; existing
`sha512_block_data_order_nohw.ml` helpers (EL_RECONSTRUCT_512,
SHA512_COMPRESS_ROUND_EL_LIST, LENGTH_SHA512_HASH_BLOCKS_SCALAR,
LIST_8_EL_64).

**Outputs**:
- `arm/proofs/sha512_block_data_order_nohw2.ml`
- Port of nohw5.ml's Phase A (load+REV inline), Phase B (schedule prefix:
  initial 16 words loaded from memory into registers), Phase D (fused
  compress + schedule), Phase E (add-back), Phase F (store) — all via
  ENSURES_WHILE_UP + ENSURES_SEQUENCE_TAC stages mirroring nohw5.

**Expected line count**: ~5800–6200 lines (at 80 rounds, 64-bit, W-in-regs).

**Exit criteria**: `SHA512_BLOCK_DATA_ORDER_NOHW2_CORRECT` and
`_SUBROUTINE_CORRECT` proved; `check_axioms() = 3`.

### Phase N2-3 — Write-up

**Outputs**:
- Update `sha512-report.md` with final numbers and methodology.
- Commit to branch `sha512-arm-nohw`.
- Memory entry: `project_sha512_nohw2_complete.md`.

### Phase N3-0 — nohw3 assembly + tests (conditional)

Skipped if nohw2 hit target. Otherwise:

- `arm/sha2/sha512_block_data_order_nohw3.S`: cyclic state-register
  renaming + the 8 ROUND_SCHED/ROUND_NOSCHED macros.
- Matching test + benchmark + signature wiring.

### Phase N3-1 — nohw3 proof (conditional)

- Port `sha256_block_data_order_nohw6.ml`. Key hurdle is the
  LIST_8_COMPRESS_NOHW6 destructuring for cyclic state; the
  memory entry `feedback_nohw5_list_8_compress.md` provides the
  template.

### Phase N3-2 — Final write-up (conditional)

- Update report with nohw3 numbers, close out.

## Risks

**Performance miss** — if nohw2 lands worse than 245 ns/block (e.g., due
to a µarch effect I'm not modelling), we may not hit 5% even after
nohw3. Mitigation: measure nohw2 early; if it's above 260 ns, pause and
re-evaluate rather than commit to nohw3. Possible contingency: port
aws-lc's exact scheduling (the Perl script has been tuned over years).

**Proof-port friction** — the nohw5 proof was the hardest of the SHA-256
scalar variants (three failed Option-A attempts on the WHILE restructure
before Option B succeeded). At 80 rounds that risk scales. Mitigation:
the memory entries are current and captured the successful Option-B
flow; the 32→64 lift continues to simplify (no int32→int64 crossovers).

**Register-pressure stumbles** — the W-in-regs design uses 16 schedule
regs + 8 state regs + ~4 scratch + x30 K-ptr + x17 loop counter + x29 fp
+ sp = 31. If a generator script picks the wrong 16 x-regs we'll get a
register-allocation error; we have 31 GPRs available, so a careful
assignment (mirroring aws-lc's x3..x15/x0..x2 choice) has headroom.

## Success criteria

- `sha512_block_data_order_nohw2` (and optionally `_nohw3`) at
  **≤ 213 ns/block** measured on Graviton 3.
- `check_axioms() = 3` (INFINITY_AX, SELECT_AX, ETA_AX only).
- NIST "abc" KAT + 370 random cross-checks pass.
- Report updated.
