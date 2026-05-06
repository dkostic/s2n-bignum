# SHA-256 Verification Pilot (x86 SHA-NI): Report

## Overview

This report covers the x86 leg of the SHA-256 formal verification pilot,
conducted through late April and early May 2026 as a follow-on to the
completed ARM64 pilot (see `pilot-report.md`). The goal was to prove
functional correctness of the x86-64 SHA-NI implementation of
`sha256_block_data_order_hw` against the same FIPS 180-4 HOL Light
specification used by the ARM proof, reusing the ARM proof's methodology
wherever it transferred and extending it where x86-specific structure
differed.

The pilot is **COMPLETE**. The theorem `SHA256_HW_CORRECT`
(`x86/proofs/sha256_block_data_order_hw.ml`) establishes that for any
`num_blocks >= 1`, the 200-instruction x86 SHA-NI assembly correctly
computes `sha256_hash_blocks` — the iterated FIPS 180-4 block
compression over all input blocks. A subroutine wrapper
`SHA256_HW_SUBROUTINE_CORRECT` wraps the core theorem with System V ABI
return-address handling via `X86_ADD_RETURN_NOSTACK_TAC`. Both theorems
are fully machine-checked (no `CHEAT_TAC`, no `new_axiom`).

The implementation is bit-identical (modulo K-constant sourcing) to the
production `sha256_block_data_order_hw` shipped by aws-lc on x86: same
SHA256RNDS2 / SHA256MSG1 / SHA256MSG2 instruction sequence, same 16
round-group structure, same `dec rdx; jne` loop. As on ARM, the only
code-level difference from production is that the K table is passed as
a fourth parameter rather than being referenced via RIP-relative
addressing — this keeps the proof independent of data-section layout
without affecting the machine code of the compression body.

Testing and benchmarking were already wired into the unified C harnesses
as part of a separate commit (`933800f7`, "Enable
sha256_block_data_order_hw tests & benchmarks on x86"): the existing ARM
test function `test_sha256_block_data_order_hw` covers x86 unchanged
(NIST "abc" KAT plus randomized single- and two-block inputs against a
C reference), and the benchmark reports ~34 ns/block in a 16-block batch
on a Graviton-equivalent x86 SHA-NI host.

Phases 1–2 of the ARM pilot (spec + bridging lemmas) transferred with
modest x86-specific adaptation; the bulk of the x86 work was in
Phase 4 (the single-block SHA-NI core) and Phase 5 (the multi-block
wrapper). The x86 proof reuses the ARM pilot's `common/sha256_spec.ml`
unchanged — demonstrating that the architecture-agnostic spec layer
written for ARM actually is architecture-agnostic.

---

## What Was Achieved

### Phase 1: Shared Spec (REUSED from ARM)

**Deliverable:** `common/sha256_spec.ml` (moved from
`arm/proofs/utils/sha256_spec.ml` by commit `1f997a3c`; ARM shim
preserved as a one-line re-export).

The entire FIPS 180-4 specification developed for ARM carried over
unchanged:

- Constants `sha256_K` (64 round constants) and `sha256_H0` (initial
  hash).
- Logical functions `sha256_Ch`, `sha256_Maj`, `sha256_Sigma0/1`,
  `sha256_sigma0/1`.
- `sha256_compress_round`, `sha256_compress`, `sha256_message_schedule`,
  `sha256_extend_schedule`, `sha256_block`, `sha256_hash_blocks`.

No x86-specific spec extensions were needed. The list-of-eight
representation of the hash state and the `sha256_compress n W H`
recursion — chosen on ARM to enable cut-point reasoning at any round
boundary — proved equally suitable for the x86 SHA-NI instruction
pattern, which operates 2 rounds at a time rather than 4.

### Phase 2: x86 ISA Model Extensions (COMPLETE)

**Deliverable:** `x86/proofs/{decode,instruction,simulator,x86}.ml`
(commit `96086766`), cherry-picked from an independent branch that
added bit-level semantics for 14 instructions not previously modeled
in s2n-bignum:

- **SHA-NI:** `SHA256RNDS2`, `SHA256MSG1`, `SHA256MSG2`
- **SSE2:** `PUNPCKLQDQ`, `PUNPCKHQDQ`, `PSLLD`, `PSLLDQ`, `PSRLD`,
  `PSRLDQ`, `PSRLQ`
- **SSSE3:** `PALIGNR`
- **AVX:** `VPALIGNR`, `VPSHUFD`, `VZEROUPPER`

For this pilot, only the SHA-NI three, `PALIGNR`, and the existing
`PSHUFB` / `PSHUFD` / `PADDD` / `MOVDQA` / `MOVDQU` were in the
instruction trace of `sha256_block_data_order_hw`. The rest of the
instruction set landed as part of the same cherry-pick because the
upstream branch also covered sibling proofs.

The SHA-256 helper functions (`sha256_Ch`, `sha256_Maj`,
`sha256_Sigma0/1`) were duplicated under the same names in `x86.ml`
because the instruction semantics in `x86.ml` must be definitionally
self-contained. These duplicate the `common/sha256_spec.ml`
definitions verbatim — they are provably equal and the duplication is a
known follow-up cleanup, not a soundness concern.

### Phase 3: Bridging Lemmas (COMPLETE)

**Deliverables:**
- `x86/proofs/utils/sha256_bridge_x86.ml` (871 lines)
- `x86/sha2/sha256_block_data_order_hw.S` (264 lines, ~200
  instructions; commit `733751c8`)

Phase 3 proved that the x86 SHA-NI instructions `SHA256RNDS2`,
`SHA256MSG1`, `SHA256MSG2` correctly implement pieces of the
algorithmic operations from `common/sha256_spec.ml`, and also introduced
the assembly itself.

**Core bridging lemmas:**

| Lemma | Statement |
|-------|-----------|
| `SHA256_COMPRESS_ROUND_2_HW_FORM` | 2 spec rounds expressed in the x86 operand sum order |
| `SHA256RNDS2_BRIDGE` (implicit, via `sha_ni_rnds2` semantics) | `SHA256RNDS2 dest=CDGH src=ABEF wk` returns ABEF after 2 compression rounds |
| `SHA256MSG1_BRIDGE` | `SHA256MSG1 dst src` = lane-wise `w_i + sigma0(w_{i+1})` for next-triple seeding |
| `SHA256MSG2_BRIDGE` | `SHA256MSG2 dst src` = 4 new schedule words via `sigma1(w_{i-2}) + w_{i-7} + (w_i + sigma0)` |
| `CDGH_EQ_ABEF` | `CDGH_PACK a b e f = ABEF_PACK a b e f` bit-for-bit |
| `SHA_NI_RNDS2_WK_DONTCARE` | The upper 64 bits of `wk` don't affect `sha_ni_rnds2` output |
| `SHA256SU_X86_BRIDGE` | Composition of MSG1+MSG2 = ARM's `sha256su0 + sha256su1` analog |

**Per-group arrays:**
- `GROUP_BRIDGE_H_UNIV` / `GROUP_BRIDGE_H2_UNIV` — abstract universal
  forms.
- `GROUP_BRIDGE_H.(i)` / `GROUP_BRIDGE_H2.(i)` for `i = 0..15` —
  concrete-index arrays stated in the spec's `sha256_compress (4*i) W H`
  form, one per round group. These parallel the ARM pilot's structure
  so the cut-point tactic `CUT_POINT_TAC_HW` follows the ARM template
  with register-name substitutions.

**Key x86-specific design decisions (captured in detail in the
`sha256_x86_bridge.md` memory note):**

1. **Lane packing is reversed vs. ARM.** `ABEF_PACK a b e f =
   word_join4 f e b a` and `CDGH_PACK c d g h = word_join4 h g d c`.
   ARM's `word_join4 a b c d` puts `a` in lane 0; x86's SHA-NI
   instructions put the *last* named argument in lane 0. Getting this
   backwards caused silent bridge-lemma failures that were expensive to
   debug.

2. **`F` is reserved.** HOL Light treats bare `F` as the boolean
   constant. All universally quantified statements use `FF` for the 6th
   working variable: `!A B C D E FF G H. …`.

3. **`BITBLAST_THEN` times out on `sha_ni_rnds2` bridges.** It descends
   into the opaque `sha256_Ch` / `sha256_Sigma1` bits and produces a
   huge per-bit disjunction that takes minutes to evaluate. The working
   pattern is `CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[SHA256_COMPRESS_ROUND_2_HW_FORM] THEN
   REWRITE_TAC[sha_ni_rnds2; ABEF_PACK; CDGH_PACK; WORD_JOIN4_SUBWORD]
   THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE`.

The assembly itself (`sha256_block_data_order_hw.S`) was written to be
byte-identical to the aws-lc production x86 SHA-NI implementation except
for K sourcing. The object file disassembles cleanly on the s2n-x86
checkpoint with no unknown instructions.

### Phase 4: Single-Block Core Proof (COMPLETE)

**Deliverable:** `x86/proofs/sha256_block_core.ml` (5 975 lines).

This phase proved the single-block compression body (`pc+64 …
pc+774`) correct against the spec. The theorem is named
`SHA256_BLOCK_CORE_CORRECT`:

```ocaml
SHA256_BLOCK_CORE_CORRECT:
  ensures x86
    (\s. XMM1 = ABEF_PACK a b e ff /\ XMM2 = CDGH_PACK c d g h /\
         XMM3..XMM6 contain w0..w15 (byte-reversed) /\
         K table at [rcx..rcx+255] /\ pshufb_mask at [rcx+256] /\ …)
    (\s. XMM1 = ABEF_PACK of sha256_block M H /\
         XMM2 = CDGH_PACK of sha256_block M H ...)
    (MAYCHANGE [YMM0_SSE; …; YMM10_SSE] ,, MAYCHANGE [SOME_FLAGS])
```

The 16 round groups of the SHA-NI body were handled by a per-group
tactic `GROUP<i>_TAC` for `i = 0..15`. Group 0 was packaged with the
14-instruction prologue as `PROLOGUE_PLUS_GROUP0_TAC`. The proof body
is then a straight-line composition:

```ocaml
REPEAT STRIP_TAC THEN
PROLOGUE_PLUS_GROUP0_TAC THEN
GROUP1_TAC THEN … THEN GROUP15_TAC THEN
POSTCOND_TAC_HW_NEW
```

**Reusable tactic infrastructure developed in this phase:**

| Tactic | Purpose |
|---|---|
| `PSHUFB_BYTEREVERSE_TAC` | Close a PSHUFB step that byte-reverses each of four 32-bit lanes against `pshufb_mask_val` |
| `PADDD_REFOLD_TAC` | Close a PADDD step; plugs in clean `word_join4` operands and refolds to `word_join4 (a0+b0) … (a3+b3)` |
| `FOLD_SHA_NI_RNDS2_TAC` | Refold stepper's 24 000-char `SHA256RNDS2` expansion back into `sha_ni_rnds2 CDGH ABEF wk` |
| `FOLD_SHA_NI_MSG1_TAC`, `FOLD_SHA_NI_MSG2_TAC` | Same idea for the two schedule instructions |
| `SUBSTITUTE_XMM_CLEANS_TAC` | Plug in known `read XMM_i = <clean_form>` into pending assumptions; matches on term structure, not pretty-printed strings |
| `REFOLD_INIT_GHOSTS_TAC` | Rewrite ghosted `ymm_i_init` back to `read YMMi s0` so `YMM_TO_XMM_SUBWORD` can fire |
| `CUT_POINT_TAC_HW i sname` | Assert `read XMM1 s = ABEF_PACK (EL 0 (compress (4i+4) W H)) …` and `read XMM2 s = ABEF_PACK (EL 0 (compress (4i+2) W H)) …` at group boundary; discharge via `GROUP_BRIDGE_H.(i)` / `GROUP_BRIDGE_H2.(i)` |
| `PROVE_LANE_EQ_TAC` / `APPLY_TWO_EQS_TAC` | Two-phase lane normalization for post-`SHA256MSG2` nested-sigma forms (groups ≥ 4) |
| `POSTCOND_TAC_HW_NEW` | Epilogue: CDGH→ABEF shift on XMM2, fold the two add-back PADDDs, close |

**What Phase 4 had to solve that Phase 3 of the ARM pilot did not:**

1. **SIMD stepper output is huge.** A single x86 SIMD instruction
   (`SHA256RNDS2`, `SHA256MSG2`) can produce a 24 000-character bit-level
   expansion when evaluated by `x86_execute`. Plain `X86_STEPS_TAC`
   on such a step produces an assumption list whose pretty-printed
   length exceeds 1 MB, and downstream tactics time out. The fix is
   the `X86_VERBOSE_STEP_TAC + FOLD_*_TAC + SUBGOAL_THEN + DISCARD`
   pattern that refolds the stepper output into a structural form
   (`sha_ni_rnds2`, `word_join4`, `ABEF_PACK`) on a per-step basis
   before continuing.

2. **`X86_STEPS_TAC` does `DISCARD_OLDSTATE_TAC` internally.** The
   stepper erases any assumption referencing a prior-state variable.
   For SIMD results this is catastrophic because the refolded
   `read YMMi s_prev = word_join top_preserved (word_join4 …)` form
   is exactly what downstream steps need. Using
   `X86_VERBOSE_STEP_TAC` (no auto-discard) is required; discards
   happen explicitly via `DISCARD_OLDSTATE_TAC "s_n"` only after each
   clean-form subgoal has been asserted.

3. **YMM vs XMM write semantics differ.** Writing to `XMMi` zeros the
   upper 128 bits of the underlying `YMMi`; SSE instructions
   (everything in this proof except the prologue's AVX VZEROUPPER
   which is modeled as a no-op) write through the `ZMMi :> bottom_256
   :> bottom_128` projection, which leaves the upper 128 bits
   *unchanged*. The stepper therefore tracks writes as
   `MAYCHANGE [YMMi_SSE]`, a strict superset of `MAYCHANGE [XMMi]`.
   Attempting to close the proof with an `XMMi` postcondition frame
   fails at the MAYCHANGE subsumption check. The theorem's MAYCHANGE
   frame must be widened to `YMMi_SSE` — even though the core proof
   never reads the upper 128 bits.

4. **`PSHUFD` leaves don't-care lanes.** After `PSHUFD xmm0,
   xmm0, 0x0e` (the standard SHA-NI pattern between the two RNDS2
   calls of a group), lanes 2 and 3 contain arbitrary leftover values.
   `GROUP_BRIDGE_H_UNIV` expects `word 0` in those lanes. The fix is
   `SHA_NI_RNDS2_WK_DONTCARE`, which proves that `sha_ni_rnds2` only
   reads the lower 64 bits of its `wk` argument, so the upper-64-bit
   garbage is absorbable.

5. **The x86 SHA-NI pattern spans 4 rounds over 2 instructions.** ARM's
   `SHA256H` and `SHA256H2` each do 4 rounds; x86's two back-to-back
   `SHA256RNDS2` calls (with a `PSHUFD` between them) do 4 rounds split
   2+2 in the CDGH/ABEF lane convention. The per-group bridge therefore
   requires a two-step composition: `ABEF_PACK (compress (4i) W H)
   → ABEF_PACK (compress (4i+2) W H) → ABEF_PACK (compress (4i+4) W H)`.
   `COMPRESS_EL_SHIFT` lemmas for each `n` handle the CDGH/ABEF
   re-linking at group boundaries.

6. **Groups 13–15 break the steady-state pattern.** G13 ends at 9
   steps (no `NOP`, no trailing `SHA256MSG1`, `SHA256RNDS2` *before*
   the final PADDD). G14 is a 7-step group that reloads the PSHUFB
   mask into XMM7 (`movdqa xmm7, xmm8`) mid-group in preparation for
   the epilogue's byte-swap. G15 contains a mid-group `dec rdx` that
   mutates RDX and `SOME_FLAGS`. These were hand-written rather than
   generated.

The 16 group tactics were developed incrementally through many sessions,
with the cleanest cadence being G7–G12 (each closed on first try from a
mechanical copy-paste of the previous group). The pattern-finding
difficulty was concentrated at the boundaries: G0 (prologue + first
bridge), G3 (first full steady-state group with `SHA256MSG2`), G4 (first
group whose current-triple input is in post-`SHA256MSG2` nested-sigma
form), and G13/G14/G15 (structurally divergent final groups).

**`SHA256_BLOCK_CORE_CORRECT_PLUS`** is a strengthened restatement of
`SHA256_BLOCK_CORE_CORRECT` that additionally asserts `XMM7 = XMM8 =
pshufb_mask_val` at loop exit. The core proof already establishes both
(they are carried through the body), but the original theorem statement
elides them. The strengthened form is what the multi-block wrapper's
`ENSURES_WHILE_UP2_TAC` body subgoal needs to recurse. It is proved by
refining the original core proof to preserve XMM7/XMM8 through all 16
groups, relying in particular on an explicit `SUBGOAL_THEN` around
prologue steps 9 and 13 that bridges `ymm_init` back to `read YMMi s0`
via `REFOLD_INIT_GHOSTS_TAC` (bare `YMM_TO_XMM_SUBWORD` is not
sufficient).

### Phase 5: Multi-Block Loop + Subroutine Wrapper (COMPLETE)

**Deliverable:** `x86/proofs/sha256_block_data_order_hw.ml` (864 lines).

Phase 5 wraps `SHA256_BLOCK_CORE_CORRECT_PLUS` in the outer loop (`dec
rdx; jne`), handles the prologue (load initial state, pack into
ABEF/CDGH, set up PSHUFB mask) and epilogue (unpack, store result), and
provides the Sys-V-ABI subroutine wrapper.

**Theorems:**

```ocaml
SHA256_HW_CORRECT:
  ensures x86
    (\s. RDI = state_ptr /\ RSI = data_ptr /\ RDX = num_blocks /\ RCX = kptr /\
         1 <= num_blocks /\ num_blocks < 2^64 /\
         LENGTH blocks = num_blocks /\ ALL (len=16) blocks /\
         aligned 16 kptr /\
         nonoverlapping {state,data,K,code} ... /\
         memory layouts for state (16 bytes), data (64*num_blocks), K (272 bytes) ...)
    (\s. RIP = returnaddress /\
         (let result = sha256_hash_blocks num_blocks blocks
                         [a;b;c;d;e;ff;g;h] in
          state[0..7] = result[0..7]))
    (MAYCHANGE [YMM0_SSE..YMM10_SSE] ,, memory :> bytes(state_ptr,32) ,, events)

SHA256_HW_SUBROUTINE_CORRECT:
  (* Same but with stackpointer precondition and RSP += 8 postcondition *)
  proof: X86_ADD_RETURN_NOSTACK_TAC HW_EXEC SHA256_HW_CORRECT
```

**Structural differences from the ARM Phase 4 multi-block proof:**

1. **`ENSURES_WHILE_UP2_TAC`, not `ENSURES_WHILE_UP_TAC`.** The x86 loop
   uses `dec rdx; jne`: a conditional backward branch whose condition is
   computed by an instruction before the branch itself. `ENSURES_WHILE_UP`
   expects the loop-control test to be the last instruction of the body;
   `ENSURES_WHILE_UP2` folds the JNE into the body (avoiding a separate
   back-edge subgoal). The exact ZF form is `read ZF s <=> val
   (word_sub rdx_in (word 1):int64) = 0` — this shape appears in the
   body subgoal's precondition and the core theorem's postcondition must
   produce exactly the same word-arithmetic expression for
   `ENSURES_WHILE_UP2_TAC` to fire.

2. **Data and K nonoverlapping.** The x86 multi-block precondition
   requires `nonoverlapping (data_ptr, 64 * num_blocks) (kptr, 272)`.
   The ARM proof did not need this because its loop body does not
   re-read the K table on each iteration in the same register-allocation
   pattern. On x86 the K loads (`movdqa xmm0, [rcx+16i]`) are inside the
   loop body and the loop-body subgoal's nonoverlapping clauses must be
   rebuilt per iteration.

3. **Prologue is non-trivial.** The x86 prologue (14 instructions,
   `pc+0..pc+63`) loads the state, re-packs it from linear `[a;b;c;d;e;
   f;g;h]` layout into ABEF/CDGH packing, stashes the original ABEF and
   CDGH in XMM9/XMM10 for the final add-back, and duplicates the PSHUFB
   mask into XMM7 and XMM8. It is packaged as `PROLOGUE_HW_TAC`.

4. **Epilogue unpack + store.** The x86 epilogue (`pc+794..pc+828`, 7
   SIMD instructions) inverts the prologue's packing: three PSHUFDs +
   PUNPCKHQDQ + PALIGNR, then two MOVDQU stores. The proof uses
   `XMM_EXISTSTOP_TAC` (originally written for
   `mlkem_rej_uniform_VARIABLE_TIME.ml`) to re-ghost each YMM's top-128
   between SIMD writes, preventing the stepper's `word_join (word_subword
   (word_join top (word_subword …)))` nesting from exploding past
   `WORD_BLAST`'s reach.

**Key Phase-5 tactical findings (captured in the `sha256_x86_phase5.md`
memory note):**

- **`ASM_REWRITE_TAC` auto-discharges MAYCHANGE.** After
  `ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC + let_CONV`, only the two
  state-memory conjuncts remain — the MAYCHANGE goal is already closed
  by accumulated `X86_STEPS_TAC` side-effect assumptions. First-attempt
  proofs that wrote `REPEAT CONJ_TAC THENL [w1; w2; maychange]` failed
  with a length mismatch; the correct form is `CONJ_TAC THEN CONV_TAC
  WORD_BLAST`.

- **`let result = ...` must be unfolded before `WORD_BLAST`.** The
  postcondition contains `let result = sha256_hash_blocks … in …`, and
  after `ENSURES_FINAL_STATE_TAC`'s beta + `ABBREV_TAC`, the remaining
  goal has `let result' = result in …`. `CONV_TAC(TOP_DEPTH_CONV
  let_CONV)` unfolds it.

- **Body subgoal's `VAL_INT64_TAC \`num_blocks - ii\`` is load-bearing.**
  Without it, the body subgoal's `word_sub` term does not numerically
  reduce and `X86_BIGSTEP_TAC HW_EXEC "s1"` fails to match the precondition
  of `SHA256_BLOCK_CORE_CORRECT_PLUS`.

Build times on a fresh `s2n-x86` checkpoint:
- `sha256_block_core.ml` (Phase 3 + 4 through `GROUP15_TAC` +
  `POSTCOND_TAC_HW_NEW`): ~4–5 min
- `SHA256_BLOCK_CORE_CORRECT_PLUS` (re-strengthened core): ~322 s
- `PROLOGUE_HW_TAC` + helpers: a few seconds
- `SHA256_HW_CORRECT`: ~23 s (body + exit fully de-`CHEAT_TAC`-ed)
- `SHA256_HW_SUBROUTINE_CORRECT`: ~4.6 s

### Testing & Benchmarking (ALREADY INTEGRATED)

Commit `933800f7` enabled the already-existing ARM test and benchmark
entries on x86 by:

- Extending the public `k[]` argument in `include/s2n-bignum.h` from 64
  to 68 entries so the x86 SHA-NI implementation can read its SSSE3
  byte-swap mask from the same buffer (ARM continues to read only
  indices 0..63).
- Dropping the `#ifdef __x86_64__` early-return in
  `test_sha256_block_data_order_hw` and lifting its dispatcher entry out
  of the AArch64-only block.
- Wiring the live x86 benchmark paths (`call_sha256_block_data_order_hw__1`
  and `__16`) and their `timingtest` dispatchers.

Test coverage (shared between ARM and x86, in `tests/test.c:14567`):
- NIST "abc" known-answer vector with hand-padded block.
- Randomized single-block inputs against `reference_sha256_block`.
- Randomized two-block inputs against the same reference.

All pass on x86 (`./test sha256_` under `tests/Makefile`).

Benchmarks (`benchmarks/benchmark.c:1627-1628`):
- `sha256_block_data_order_hw (1 block)` — ~37 ns/call.
- `sha256_block_data_order_hw (16 blocks)` — ~545 ns/call ≈ 34 ns/block.

Numbers are consistent with x86 SHA-NI expectations (~1–2 cpb on
SHA-NI-capable Intel/AMD parts at typical CPU frequencies).

---

## How It Was Done

### Proof Architecture

The proof follows the same three-layer architecture as the ARM pilot:

```
    SHA-256 Spec (FIPS 180-4)                [common/sha256_spec.ml — SHARED]
           |
    Bridging Lemmas (SHA256RNDS2 = 2 rounds, ...)   [sha256_bridge_x86.ml]
           |
    Assembly Proof (symbolic execution + cut-points) [sha256_block_core.ml
                                                      + sha256_block_data_order_hw.ml]
```

As on ARM, the key innovation is the **cut-point approach**: rather than
symbolically executing all 160 compression-body instructions and then
matching against the spec, the proof inserts a verification checkpoint
after each of the 16 round groups. At each checkpoint:

1. Symbolically execute 7–11 instructions (one round group).
2. Apply the per-SIMD-op refold tactic chain
   (`FOLD_SHA_NI_RNDS2_TAC` / `PADDD_REFOLD_TAC` /
   `PSHUFB_BYTEREVERSE_TAC` / `FOLD_SHA_NI_MSG{1,2}_TAC`).
3. Assert via `SUBGOAL_THEN` that `XMM1 = ABEF_PACK (EL 0 (sha256_compress
   (4*(i+1)) W H)) …` and `XMM2 = ABEF_PACK (EL 0 (sha256_compress (4*i+2)
   W H)) …`.
4. Discharge via `CUT_POINT_TAC_HW i` (which invokes `GROUP_BRIDGE_H.(i)`
   and `GROUP_BRIDGE_H2.(i)` from Phase 3).
5. Discard the accumulated complex YMM assumptions, keeping only the
   clean `ABEF_PACK` forms.
6. Continue to the next group.

This keeps terms small throughout the proof.

### x86-specific challenges vs ARM

| Challenge | ARM | x86 |
|---|---|---|
| Rounds per SIMD instruction | 4 (`sha256h`, `sha256h2`) | 2 (`sha256rnds2`) |
| Message-schedule instruction count | 2 (`su0 + su1`) | 2 (`msg1 + msg2`), but different lane structure |
| State packing | `word_join4 a b c d` (natural order) | `word_join4 d c b a` (REVERSED) |
| Loop test | Decrement + CBNZ (one instruction) | DEC + JNE (two instructions) |
| Byte-swap | `REV32` (register) | `PSHUFB` with per-byte mask constant |
| K sourcing | Loaded from memory per group | Loaded from memory per group, but ALIGNED 16 via `movdqa` — requires `aligned 16 kptr` precondition |
| Prologue complexity | 4 instructions | 14 instructions (state repack + mask duplicate + CDGH/ABEF stash) |
| Epilogue complexity | 3 instructions | 7 instructions (full inverse of prologue repack) |
| Groups with non-uniform structure | None (all 16 steady-state) | 3 (G13 9-step, G14 7-step, G15 with mid-group `dec`) |
| Stepper output size per SIMD instruction | ~1 000 chars | up to 24 000 chars — required per-step refold |

### Proof Development Process

The proof was developed iteratively over roughly a dozen sessions using
`holctl`, a CLI tool for interactive HOL Light sessions. Most group
tactics (G1 through G12) were developed by:

1. Load the current checkpoint (fresh `s2n-x86` + previously verified
   groups).
2. Execute one step of the next group interactively.
3. Inspect the resulting goal; identify which refold tactic applies.
4. Tune the `SUBGOAL_THEN` clean-form assertion.
5. Once all steps close, codify as `GROUP<i>_TAC` and commit.

Several strategies that worked on ARM were tried and failed on x86:

- **`WORD_BLAST` as the universal closer for PADDD refolds.** Attempted
  on the raw stepper output of a single PADDD step: timed out past 10
  minutes with 2+ GB resident memory. The 256-bit expression with 8
  input words is too big for the bit-blasting tactic. The structural
  `PADDD_REFOLD_TAC` chain (YMM_TO_XMM_SUBWORD →
  `SUBSTITUTE_XMM_CLEANS_TAC` → `WORD_SIMPLE_SUBWORD_CONV` →
  `WORD_JOIN4_SUBWORD` → `GSYM WORD_JOIN4_BALANCED`) closes in
  milliseconds.

- **Forward bridging during symbolic execution.** Applying
  `SHA256H_BRIDGE`-analog rewrites after each group: on x86 this is
  `sha_ni_rnds2` applied to an `ABEF_PACK`, which duplicates each
  sub-sum 8x per instruction. After 2–3 groups, terms are too large.

- **Single `CUT_POINT_TAC_HW` at each group boundary.** The first
  attempt targeted `CDGH_PACK (EL 2 (compress (4i+4))) …` for XMM2
  because that's what the hardware emits after two RNDS2 calls. But
  `GROUP_BRIDGE_H2.(i)` concludes `ABEF_PACK (EL 0 (compress (4i+2)))
  …` — the ABEF pack two rounds in, not the CDGH pack four rounds in.
  These are related by `CDGH_EQ_ABEF + two more rounds`, but that
  conversion doesn't fit inside `CUT_POINT_TAC_HW`. The fix (commit
  `1d6e2241`) changed the XMM2 target to match `GROUP_BRIDGE_H2`'s
  shape; the CDGH/ABEF shift was deferred to the group-boundary CDGH
  shift and to `POSTCOND_TAC_HW_NEW`.

---

## Key Technical Findings

### What Worked Well

1. **The spec is architecture-agnostic.** `common/sha256_spec.ml`
   required zero modifications. Every lemma in the ARM `sha256_bridge.ml`
   that was stated in terms of the spec (not in terms of ARM
   instruction helpers) transferred to x86 unchanged.

2. **Per-group copy-paste scales.** Groups 5–12 each closed on first
   try from a mechanical edit of the previous group (substitute
   compress indices, K offsets, XMM rotation, step numbers). The
   steady-state cycle is four groups long (the XMM rotation has
   period 4), so G8 wraps back to G4's pattern, G9 to G5's, etc.
   This cut the per-group implementation cost by ~10x compared to G3
   and G4.

3. **The cut-point approach scales to 200+ instructions.** Without
   cut-points, the 160-instruction compression body would produce terms
   that do not simplify in reasonable time. With cut-points at each of
   the 16 group boundaries, the proof runs in ~5 minutes of CPU time
   (compared to presumed-non-terminating without).

4. **`holctl` sessions + `CHEAT_TAC` placeholders.** Each group was
   committed with `CHEAT_TAC` for its successors so the file always
   loaded. A new session could load the checkpoint, inspect the
   remaining `CHEAT_TAC` sites, and resume. This pattern was essential:
   the pilot spanned roughly a dozen sessions interrupted by context
   exhaustion and machine restarts.

### What Didn't Work

1. **Pretty-print-based term matching.** `SUBSTITUTE_XMM_CLEANS_TAC`'s
   first version matched `"= word_join4"` as a literal substring of the
   pretty-printed assumption. This broke when pretty-print inserted a
   newline between `=` and `word_join4` (happens naturally for wide
   `word_join4` terms like MSG2 output). Fix: match on term structure
   via `dest_eq` + `strip_comb`.

2. **Assumption self-rewrite.** `SUBSTITUTE_XMM_CLEANS_TAC` applied
   `REWRITE_RULE` with all matching `read XMM_i … = <const>` assumptions
   to every assumption, including themselves. This rewrote the LHS to
   the RHS, producing `<const> = <const>` → T, which HOL drops —
   silently losing the precondition. Fix: skip the assumption itself
   during the batch rewrite.

3. **Ghosting YMM7/YMM8 broke PSHUFB reduction.** YMM7 and YMM8 hold the
   PSHUFB mask. `GHOST_INTRO_TAC` before `ENSURES_INIT_TAC` would have
   replaced them with symbolic `ymm7_init`/`ymm8_init`, after which the
   stepper could not reduce PSHUFB byte-by-byte. Fix: leave
   `read XMM7 s = pshufb_mask_val` in concrete form and ghost only
   YMM0–YMM6, YMM9, YMM10.

4. **`X86_STEPS_TAC` across SIMD instructions.** The internal
   `DISCARD_OLDSTATE_TAC` throws away the refolded `read YMMi s_prev`
   forms produced by PADDD_REFOLD / FOLD_SHA_NI_* tactics. Fix: use
   `X86_VERBOSE_STEP_TAC` for SIMD steps and assert the clean form
   with `SUBGOAL_THEN` before calling `DISCARD_OLDSTATE_TAC` explicitly.

### Open Questions Resolved

| Question from x86 onset | Answer |
|---|---|
| Can we reuse the ARM spec? | Yes — moved to `common/sha256_spec.ml` verbatim, ARM shim preserves compatibility |
| Do the x86 SHA-NI semantics in `x86.ml` match the spec? | Yes — helper functions (`Ch`, `Maj`, `Sigma0/1`) are definitionally identical across the two files |
| Can the `GROUP_BRIDGE` array structure transfer? | Yes — stated as `sha256_compress (4*i) W H`, independent of hardware — just requires new `SHA256RNDS2` + `SHA256MSG1/2` bridge lemmas instead of ARM's `H/H2/SU` lemmas |
| How to handle `PSHUFD` don't-care lanes? | `SHA_NI_RNDS2_WK_DONTCARE` — proves upper 64 bits of `wk` don't affect output |
| How to handle the `dec rdx; jne` loop? | `ENSURES_WHILE_UP2_TAC` — folds JNE into body, avoiding separate back-edge subgoal |
| Subroutine wrapper complication? | None — `X86_ADD_RETURN_NOSTACK_TAC` one-liner closes it |
| Is MAYCHANGE frame `XMMi` or `YMMi_SSE`? | `YMMi_SSE` (SSE SIMD writes leave upper 128 untouched, not zeroed — XMMi frame is strictly too tight) |

---

## Lessons Learned Specific to x86

### SIMD stepper output management

The single biggest x86-specific engineering lesson is that the
`x86_execute` output for SIMD instructions (especially `SHA256RNDS2`,
`SHA256MSG1`, `SHA256MSG2`) is orders of magnitude larger than any ARM
instruction's output. A naive `X86_STEPS_TAC [s1;s2;...;s16]` on a
single round group produces an assumption list whose pretty-printed size
exceeds 1 MB, and any downstream tactic that walks the assumption list
(even `ASM_REWRITE_TAC`) takes minutes.

The `X86_VERBOSE_STEP_TAC + FOLD_*_TAC + SUBGOAL_THEN clean-form +
DISCARD_OLDSTATE_TAC` pattern is mandatory on x86 for SIMD-heavy proofs.
It is worth codifying in `agent-guide.md` / `MEMORY_HANDLING_TUTORIAL.md`
as the canonical pattern for x86 SIMD proofs.

### MAYCHANGE frame widening

The `XMMi` vs `YMMi_SSE` distinction is not a bug in the stepper or the
MAYCHANGE machinery — it correctly reflects Intel's actual semantics
(`MOVDQA` is `VEX.128`-encoded if from AVX, but the bare SSE encoding
leaves upper bits alone). Proofs that write SSE to XMM registers must
widen their MAYCHANGE frame to `YMMi_SSE`. This applies to every x86
SSE/SHA-NI/SSSE3 proof, not just SHA-256.

### CDGH vs ABEF tracking across groups

The two-round-per-instruction nature of `SHA256RNDS2` (vs ARM's
four-round `SHA256H`) means that between groups, the x86 XMM2 register
holds the ABEF pack of `sha256_compress (4i+2) W H` — *not* the
CDGH pack of `sha256_compress (4i+4) W H`, which is what one might
expect because RNDS2 treats XMM2 as its "CDGH operand." The next
group's first RNDS2 then re-uses XMM2 as CDGH. The intermediate
ABEF→CDGH conversion happens via `CDGH_EQ_ABEF + COMPRESS_EL_SHIFT.(i)`:

```ocaml
COMPRESS_EL_SHIFT.(i):
  LENGTH H = 8 ==>
  EL 2 (compress (4i+4) W H) = EL 0 (compress (4i+2) W H) /\
  EL 3 (compress (4i+4) W H) = EL 1 (compress (4i+2) W H) /\
  EL 6 (compress (4i+4) W H) = EL 4 (compress (4i+2) W H) /\
  EL 7 (compress (4i+4) W H) = EL 5 (compress (4i+2) W H)
```

Each `COMPRESS_EL_SHIFT.(i)` is proven per-group by unrolling
`sha256_compress` from round 0 (so proving it at `i = 15` requires
unfolding 64 rounds). This is automated by `mk_compress_el_shift`.

### Session resilience (confirmed from ARM, extended)

Same workflow as ARM: frequent commits with `CHEAT_TAC` placeholders,
structured progress notes in memory files, `holctl` servers surviving
session restarts. The x86 proof added one refinement: the
`sha256_x86_phase4.md` memory file was structured as a narrative log
with per-session updates (each new finding appended, not replacing prior
text) and explicit "GROUP_i_TAC done" markers. This made "resume from
session N+1" straightforward — a new agent could grep for the last
completed group marker, load the corresponding checkpoint, and continue
with the next group's templated copy-paste.

### Memory notes caught failures early

Three of the non-trivial x86-specific bugs — the self-rewrite bug in
`SUBSTITUTE_XMM_CLEANS_TAC` (commit `38db5e6b`), the pretty-print
matching bug (commit `b41d64f1`), and the CUT_POINT_TAC XMM2 target bug
(commit `1d6e2241`) — were discovered and explained via memory-note
"hard-won findings" sections that then served as a reference for
the fix. Capturing these as concrete, dated observations (with the
precise term shape that triggered failure) was markedly more useful
than general "debugging tips" documentation, because the next failure
of the same shape could be recognized by grep.

---

## Artifacts Summary

### Final Deliverables (on branch `sha256-x86`)

**Shared specifications (reused from ARM):**
- `common/sha256_spec.ml` — FIPS 180-4 SHA-256 spec
  (moved to `common/` by commit `1f997a3c`; ARM location is now a shim)

**x86-specific bridging lemmas:**
- `x86/proofs/utils/sha256_bridge_x86.ml` (871 lines) — SHA256RNDS2 /
  MSG1 / MSG2 bridges, `ABEF_PACK`/`CDGH_PACK`, per-group bridge arrays

**x86 assembly:**
- `x86/sha2/sha256_block_data_order_hw.S` (264 lines, 200 instructions)

**Proofs:**
- `x86/proofs/sha256_block_core.ml` (5 975 lines) — tactic infrastructure
  (`PROLOGUE_PLUS_GROUP0_TAC`, `GROUP1_TAC` … `GROUP15_TAC`,
  `POSTCOND_TAC_HW_NEW`), theorem `SHA256_BLOCK_CORE_CORRECT`
- `x86/proofs/sha256_block_data_order_hw.ml` (864 lines) —
  `SHA256_BLOCK_CORE_CORRECT_PLUS` (strengthened core),
  `PROLOGUE_HW_TAC`, `SHA256_HW_CORRECT` (multi-block),
  `SHA256_HW_SUBROUTINE_CORRECT` (ABI wrapper)

**ISA extensions (Phase 2 cherry-pick):**
- `x86/proofs/{decode,instruction,simulator,x86}.ml` — bit-level
  semantics for SHA-NI and associated SSE/SSSE3/AVX instructions

**Tests and benchmarks (already integrated in commit `933800f7`):**
- `tests/test.c` — `test_sha256_block_data_order_hw` now runs on x86
- `benchmarks/benchmark.c` — 1-block and 16-block entries
- `include/s2n-bignum.h` — `k[]` parameter widened from 64 to 68 entries

### Reusability for Future x86 Targets

The tactic infrastructure in `sha256_block_core.ml` is largely
x86-SIMD-general, not SHA-256-specific:

- `PSHUFB_BYTEREVERSE_TAC` works for any PSHUFB step against a
  byte-reverse mask.
- `PADDD_REFOLD_TAC` works for any PADDD on `word_join4`-shaped XMM
  operands.
- `FOLD_SHA_NI_{RNDS2,MSG1,MSG2}_TAC`, `SUBSTITUTE_XMM_CLEANS_TAC`,
  `REFOLD_INIT_GHOSTS_TAC` are SHA-NI-specific in naming but the pattern
  (refold stepper output → structural form) is generic.
- `XMM_EXISTSTOP_TAC` is already general (originally from
  `mlkem_rej_uniform_VARIABLE_TIME.ml`).

The bridging-lemma structure — per-group arrays `GROUP_BRIDGE_H.(i)` and
`GROUP_BRIDGE_H2.(i)` stated in the spec's `sha256_compress (4*i) W H`
form — is specifically modeled to mirror ARM's
`GROUP_BRIDGE_H.(i)` / `GROUP_BRIDGE_H2.(i)`. Any future cross-platform
hash proof should plan for the same two-layer structure (universal
form + per-group concrete array).

The `ENSURES_WHILE_UP2_TAC` pattern for `dec R; jne` loops transfers
directly to any x86 multi-iteration crypto primitive with a trailing
conditional backward branch (SHA-1, SHA-512, AES-GCM counter loop, …).

### Not Yet Done

- **`SHA256_HW_SUBROUTINE_SAFE` (memory safety proof).** Same status as
  ARM: requires the function to be added to `subroutine_signatures.ml`
  with buffer-size metadata. The dynamic-sized data buffer and 4-argument
  interface make this non-trivial compared to fixed-size functions.
  Tracked as follow-up.

- **IBT (Indirect Branch Tracking) variant of the subroutine theorem.**
  Other x86 subroutines in s2n-bignum expose an `_IBT_SUBROUTINE_CORRECT`
  that accounts for the `ENDBR64` trimmed from the core proof. Deferred
  until a CI requirement for it surfaces.

- **Spec deduplication.** The SHA-256 helper functions (`Ch`, `Maj`,
  `Sigma0/1`) exist both in `common/sha256_spec.ml` and in `x86.ml` under
  the same names, with definitionally identical RHS. Unifying via a
  shared import is a pure housekeeping cleanup.
