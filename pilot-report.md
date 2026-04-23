# SHA-256 Verification Pilot: Report on Phases 1-5 (Complete)

## Overview

This report covers the SHA-256 formal verification pilot conducted in
April 2026, as the first target of the whole-proofs project. The goal was
to develop and validate an end-to-end methodology for proving functional
correctness of ARM64 cryptographic assembly against a HOL Light specification,
using the s2n-bignum verification infrastructure.

The pilot is COMPLETE. The final target, **sha256_block_data_order_hw** (124
instructions), is a multi-block ARM64 SHA-256 function that has been proven
correct against the FIPS 180-4 specification. The theorem `SHA256_HW_CORRECT`
establishes that for any `num_blocks >= 1`, the function correctly computes
`sha256_hash_blocks` -- the iterated application of SHA-256 block compression
over all input blocks. The full proof loads via
`needs "arm/proofs/sha256_block_data_order_hw.ml"` in approximately 15 minutes.

The implementation is structurally equivalent to the production
`sha256_block_data_order_hw` in aws-lc: it uses the same SHA256H/SHA256H2/
SHA256SU0/SHA256SU1 instruction pattern, the same loop structure, and the same
register allocation. The only difference is K-constant handling (passed as a
parameter rather than embedded via PC-relative addressing). In addition to the
proof, the pilot includes unit tests (NIST "abc" known-answer vector plus
random single-block and multi-block tests against a C reference) and benchmarks
(~37.7 ns/block, ~1.78 GB/s on Graviton).

Phases 1-3 built up the methodology incrementally -- specification, bridging
lemmas, and single-block assembly proof -- before Phase 4 tackled the
multi-block loop that constitutes the production-grade target. Phase 5 aligned
the code and proof with s2n-bignum CI conventions so the proof can be built and
checked as part of the standard `make` workflow.

---

## What Was Achieved

### Phase 1: SHA-256 Algorithmic Specification (COMPLETE)

**Deliverable:** `s2n-bignum/arm/proofs/utils/sha256_spec.ml` (149 lines)

A self-contained HOL Light specification of SHA-256 at the FIPS 180-4 level:

- **Constants:** All 64 round constants (`sha256_K`) and 8 initial hash values
  (`sha256_H0`), cross-checked against both FIPS 180-4 and the Cryptol
  reference spec.

- **Logical functions:** `sha256_Ch`, `sha256_Maj`, `sha256_Sigma0`,
  `sha256_Sigma1`, `sha256_sigma0`, `sha256_sigma1` -- independent definitions
  matching the standard, not reusing the existing instruction-level helpers.

- **Message schedule:** `sha256_extend_schedule` and
  `sha256_message_schedule`, defined recursively. The schedule is computed by
  extending a 16-word message block by `n` additional words. The full schedule
  for one SHA-256 block is `sha256_message_schedule 48 M` (16 + 48 = 64 words).

- **Compression:** `sha256_compress_round` (single round) and `sha256_compress`
  (iterated rounds), defined recursively in the same style as the Keccak spec.

- **Block processing:** `sha256_block M H` computes the schedule extension,
  runs 64 rounds of compression, and adds the result back to the initial hash.

**Design decisions and rationale:**

- Used list representation `[a;b;c;d;e;f;g;h]` for state (matching Keccak's
  25-element list pattern) rather than tuples.
- Recursive `sha256_compress n W state` rather than 64 individual definitions --
  this allows cut-point reasoning at any round boundary.
- The schedule uses `sha256_message_schedule n M` rather than computing all 64
  words upfront, enabling incremental extension lemmas.

### Phase 2: Bridging Lemmas (COMPLETE)

**Deliverable:** `s2n-bignum/arm/proofs/utils/sha256_bridge.ml` (467 lines)

This phase proved that the ARM SHA-256 hardware instructions correctly implement
the algorithmic operations defined in Phase 1.

**Core bridging lemmas:**

| Lemma | Statement |
|-------|-----------|
| `SHA256H_BRIDGE` | ARM `sha256h` instruction = 4 rounds of `sha256_compress_round` on state elements 0-3 (ABCD) |
| `SHA256H2_BRIDGE` | ARM `sha256h2` instruction = 4 rounds of `sha256_compress_round` on state elements 4-7 (EFGH) |
| `SHA256SU_BRIDGE` | ARM `sha256su0` + `sha256su1` = 4 new message schedule words via `sha256_sigma0`/`sha256_sigma1` |

**Supporting infrastructure:**

- `word_join4`: Packs four 32-bit words into a 128-bit value (modeling how state
  elements map to NEON Q registers).
- `WORD_JOIN4_SUBWORD`: Extracts individual 32-bit words back from packed values.
- `SHA256_COMPRESS_ROUND_PREADD`: Handles the hardware's pre-addition of K+W
  constants before the SHA256H instruction.
- Equivalence lemmas (`sha256_Ch = sha_choose`, etc.) connecting the spec
  functions to existing s2n-bignum instruction-level definitions.

**What was hard:** The main challenge was the register packing/unpacking --
the hardware operates on 128-bit values containing 4 packed 32-bit words, while
the spec uses lists of individual 32-bit words. The `word_join4` abstraction
and its extraction lemmas were essential to bridge this gap cleanly.

### Phase 3: Assembly Proof (COMPLETE)

Two assembly implementations were written and proven correct:

#### sha256_block_core (109 instructions)

**Assembly:** `s2n-bignum/arm/sha2/sha256_block_core.S` (170 lines)
**Proof:** `s2n-bignum/arm/proofs/sha256_block_core.ml` (459 lines)

A straight-line register-to-register SHA-256 core:
- **Input:** State in Q0/Q1, message words in Q4-Q7 (pre-byte-swapped), K table
  pointer in X1.
- **Output:** `sha256_block M H` result in Q0/Q1.
- **Structure:** 16 round groups (4 SHA-256 rounds each), groups 0-11 with
  message schedule update (7 instructions), groups 12-15 without (5
  instructions), plus 2 state add-back instructions and a RET.

**Theorem proved:**

```ocaml
SHA256_BLOCK_CORE_CORRECT:
  ensures arm
    (\s. ... Q0 = word_join4 a b c d /\ Q1 = word_join4 e f g h /\
         Q4..Q7 = message words /\ K table in memory ...)
    (\s. ... Q0/Q1 = word_join4 of sha256_block M H elements ...)
    (MAYCHANGE ...)
```

#### sha256_block_simple (122 instructions)

**Assembly:** `s2n-bignum/arm/sha2/sha256_block_simple.S` (199 lines)
**Proof:** `s2n-bignum/arm/proofs/sha256_block_simple.ml` (99 lines)

Wraps the core with memory I/O:
- **Input:** State pointer in X0, message data pointer in X1, K table pointer
  in X2.
- **Output:** Updated state written back to memory at X0.
- **Additional operations:** Memory loads (LDR Q), REV32 byte-swap from
  little-endian memory to big-endian SHA-256 word order, memory stores (STR Q).

**Theorem proved:**

```ocaml
SHA256_BLOCK_SIMPLE_CORRECT:
  ensures arm
    (\s. ... state in memory at X0 /\ data in memory at X1 /\
         K table in memory at X2 ...)
    (\s. ... memory at X0 = sha256_block (byte-swapped data) (initial state) ...)
    (MAYCHANGE ...)
```

#### Supporting proof infrastructure

In addition to the two main proof files, several supporting artifacts were
developed:

| File | Lines | Purpose |
|------|-------|---------|
| `sha256_block_core_setup.ml` | 132 | Interactive proof development setup |
| `sha256_el_w_gen.ml` | 76 | 64 schedule extraction lemmas (EL n W = expression) |
| `sha256_group_bridge_gen.ml` | 97 | 32 per-group bridge lemmas (16 for H, 16 for H2) |
| `sha256_groups_0_3.ml` | 162 | Interactive cut-point testing for groups 0-3 |
| `sha256_simple_groups.ml` | 121 | Cut-point testing for memory version |
| `sha256_block_core_notes.md` | 164 | Progress notes and technical findings |

**Total new code:** ~3,650 lines across 46 files (including assembly,
proof infrastructure, test files, and documentation).

### Phase 4: Multi-Block Loop (COMPLETE)

**Deliverable:** `s2n-bignum/arm/proofs/sha256_block_data_order_hw.ml`
**Assembly:** `s2n-bignum/arm/sha2/sha256_block_data_order_hw.S` (124 instructions)

This phase proved the full multi-block SHA-256 function correct, building on
the single-block infrastructure from Phases 1-3.

**Theorem proved:**

```ocaml
SHA256_HW_CORRECT:
  ensures arm
    (\s. ... state in memory at X0 /\ data (num_blocks * 16 words) at X1 /\
         K table (64 words) at X3 /\ 1 <= num_blocks ...)
    (\s. ... memory at X0 = sha256_hash_blocks blocks H0 ...)
    (MAYCHANGE ...)
```

**What Phase 4 added over Phase 3:**

- **Multi-block loop** via `ENSURES_WHILE_UP_TAC`: processes `num_blocks`
  consecutive 512-bit blocks, iterating the hash state.
- **Quantified memory in loop invariant:** The loop invariant must include
  quantified assumptions for both the data blocks and the K constants table,
  even though K doesn't change across iterations.
- **REV32 byte-swap within loop body:** Each iteration loads and byte-swaps
  64 bytes of message data from memory.
- **Block counter arithmetic:** Tracking the data pointer advancement
  (`WORD_ADVANCE_64`) and block counter decrement across iterations.

**Key technical challenges solved:**

1. **FIRST_ASSUM vs FIRST_X_ASSUM.** The single most important fix in Phase 4.
   Quantified memory assumptions for data blocks and K constants must survive
   through 118 `ARM_STEPS_TAC` propagation steps. `FIRST_X_ASSUM` (used in
   standard s2n-bignum patterns) removes the assumption after first use,
   causing later steps that need the same memory to fail. Changing to
   `FIRST_ASSUM` (which preserves the assumption) unblocked the entire proof.

2. **RECONSTRUCT_BLOCK_TAC.** After symbolic execution, the postcondition
   requires proving that `EL ii blocks = [w0;...;w15]` for each block index.
   The initial approach using `GSYM ALL_EL` failed because it picked the wrong
   quantifier. The fix used `LIST_16_EL` + `EXPAND_TAC` to reconstruct the
   block element list directly.

3. **Single-pass postcondition discharge.** The final postcondition
   (`sha256_hash_blocks`) was discharged in a single pass using
   `ASM_REWRITE_TAC[sha256_hash_blocks; sha256_block; WORD_ADVANCE_64]`
   followed by `let_CONV`, `EL_MAP2`, and `WORD_SUB_SUC`.

**Proof structure:** The proof uses `ENSURES_WHILE_UP_TAC` which generates
4 subgoals:

| Subgoal | Steps | Description |
|---------|-------|-------------|
| Init | 2 ARM steps | Establish loop invariant at i=0 (load K pointer, set up state) |
| Body | 118 ARM steps | Single-block compression with 16 cut-point groups |
| Back-edge | 1 CBNZ step | Decrement counter, branch back if nonzero |
| Exit | 3 ARM steps | Store final state to memory |

The loop body (118 steps) dominates the proof time, using the same cut-point
strategy from Phase 3 but with quantified memory propagation through each step.

**Performance:** Full proof loads in ~15 minutes (~490 seconds for the body
symbolic execution).

**Additional artifacts:**
- Unit tests in `tests/test.c`: NIST "abc" known-answer test plus random
  single-block and multi-block tests against a C reference implementation.
- Benchmarks in `benchmarks/benchmark.c`: ~37.7 ns/block, ~1.78 GB/s.
- `MEMORY_HANDLING_TUTORIAL.md`: Guide to quantified memory propagation
  patterns, written as a reference for AI agents tackling similar proofs.

### Phase 5: CI Integration (COMPLETE)

This phase aligned the assembly, proof, header, and tooling with s2n-bignum
conventions so that the proof can be built and verified by the standard CI
pipeline (`make build_proofs`).

**Assembly changes (`arm/sha2/sha256_block_data_order_hw.S`):**

- Added `#include "_internal_s2n_bignum_arm.h"` and replaced raw directives
  with standard macros: `S2N_BN_SYM_VISIBILITY_DIRECTIVE`,
  `S2N_BN_FUNCTION_TYPE_DIRECTIVE`, `S2N_BN_SYM_PRIVACY_DIRECTIVE`,
  `S2N_BN_SYMBOL`, `S2N_BN_SIZE_DIRECTIVE`.
- Added `CFI_START` / `CFI_RET` for call-frame information (stack unwinding
  support).
- Renamed local label `.Loop_hw` to `Lsha256_block_data_order_hw_loop`
  (s2n-bignum naming convention: `L<function_name>_<label>`, no leading dot).
- Added `#if defined(__linux__) && defined(__ELF__)` GNU-stack section.
- Added `// extern void ...` declaration comment and `// Inputs ...; output ...`
  comment, both required by `tools/collect-signatures.py`.

The machine code is byte-identical after these changes -- only metadata
(symbol visibility, CFI directives, section markers) differs in the object file.

**Proof changes (`arm/proofs/sha256_block_data_order_hw.ml`):**

- Added `SHA256_HW_SUBROUTINE_CORRECT` theorem. This wraps `SHA256_HW_CORRECT`
  with return-address handling: the precondition reads `X30 = returnaddress`,
  the postcondition asserts `PC = returnaddress`, and the frame condition uses
  `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`. The proof is a single call to
  `ARM_ADD_RETURN_NOSTACK_TAC HW_EXEC SHA256_HW_CORRECT`.

**Header and tooling changes:**

- `include/s2n-bignum.h`: Fixed the comment above the function declaration to
  include both "Inputs" and "output" keywords (required by
  `collect-signatures.py`). Renamed parameter `K` to `k` for case-consistency
  with the comment parser (which lowercases everything).
- `tools/collect-signatures.py`: Added `sha256_block_data_order_hw` to the
  `onlyInArm` list (no x86 counterpart exists).
- `arm/proofs/subroutine_signatures.ml`: Regenerated by `collect-signatures.py`
  with the new function entry.

**Restored `arm/proofs/simulator_iclasses.ml`:**

This file was accidentally deleted in commit `0d6153ae` ("Remove intermediate
development files"). It contains instruction class bit patterns used by the
ARM simulator and is required by the CI build. The file was restored from git
history with all REV32 entries intact.

**Not yet done:**

- `SHA256_HW_SUBROUTINE_SAFE` (memory safety proof). This requires adding the
  function to `subroutine_signatures.ml` with buffer size metadata and building
  a safety proof via `mk_safety_spec`. The dynamic-sized data buffer
  (`64 * num_blocks` bytes) and the 4-argument interface make this non-trivial
  compared to fixed-size functions. This is tracked as future work.

---

## How It Was Done

### Proof Architecture

The proof follows a three-layer architecture:

```
    SHA-256 Spec (FIPS 180-4)
           |
    Bridging Lemmas (SHA256H_BRIDGE, etc.)
           |
    Assembly Proof (symbolic execution + cut-points)
```

The key innovation in the assembly proof was the **cut-point approach**. Rather
than symbolically executing all 109 instructions and then matching the result
against the spec (which causes terms to grow to unmanageable sizes), the proof
inserts verification checkpoints after each of the 16 round groups:

1. Symbolically execute 5-7 instructions (one round group).
2. Simplify the NEON ADD operations (`WORD_JOIN4_SUBWORD`, `WORD_JOIN_4x32`).
3. Assert via `SUBGOAL_THEN` that Q0 = `word_join4(EL 0..3 (sha256_compress
   (4*(i+1)) W H))` and similarly for Q1.
4. Prove this assertion using the per-group bridge lemma and schedule extraction
   lemmas.
5. Discard the old (complex) symbolic state assumptions, keeping only the clean
   sha256_compress form.
6. Continue to the next group.

This keeps terms small throughout the proof. The full proof runs in about 2-3
minutes, compared to 45+ minutes without cut-points (and that's for the
degenerate case with a trivial postcondition -- with a real postcondition, the
non-cut-point approach doesn't terminate at all).

### Proof Development Process

The proof was developed iteratively using `holctl`, a CLI tool for interactive
HOL Light sessions. The workflow was:

1. Start from a checkpoint with s2n-bignum infrastructure pre-loaded.
2. Load spec and bridge files.
3. Test tactics interactively to find working proof strategies.
4. Once a strategy was validated, codify it into .ml proof files.
5. Verify the complete proof loads without errors.

Several approaches were tried and discarded before arriving at the cut-point
method:

- **Forward bridging during execution:** Apply `SHA256H_BRIDGE` as a rewrite
  rule after each round group. Failed because each bridge application duplicates
  the inner state expression (8x per group), causing exponential growth.

- **Reverse bridging from spec:** Start from `sha256_block`, unfold to
  individual rounds, and fold back into hardware instructions. Conceptually
  clean but difficult to implement due to the intermediate term sizes.

- **End-to-end execution + postcondition matching:** Execute all 109
  instructions, then prove the result equals the spec. Works for trivial
  postconditions (~45 minutes) but the final matching step doesn't terminate
  with the real spec.

---

## Key Technical Findings

### What Worked Well

1. **The spec structure mirrors the hardware well.** The recursive
   `sha256_compress n W state` definition aligns naturally with the hardware's
   4-round groups -- you simply check at multiples of 4.

2. **Bridging lemmas are reusable.** The same `SHA256H_BRIDGE` and
   `SHA256H2_BRIDGE` lemmas work for any implementation that uses the ARM SHA-256
   instructions, regardless of how the surrounding code is structured.

3. **The s2n-bignum infrastructure is solid.** `define_from_elf`,
   `ARM_MK_EXEC_RULE`, `ARM_STEPS_TAC`, `ENSURES_INIT_TAC`, and
   `ENSURES_FINAL_STATE_TAC` all worked as expected with minimal adaptation.

4. **Cut-point reasoning scales.** Adding 2 more instructions for memory I/O
   (sha256_block_simple) required only minimal proof changes -- the core
   structure remained the same.

5. **HOL Light's word reasoning is capable.** `WORD_RULE`, `WORD_REDUCE_CONV`,
   and the existing `WORD_JOIN4_SUBWORD` infrastructure handled the 32-bit/128-bit
   packing without needing custom tactics.

### What Didn't Work

1. **Forward bridging during symbolic execution causes exponential term
   growth.** This was the biggest obstacle. Applying `SHA256H_BRIDGE` as a
   rewrite after each group duplicates the inner state 8x (once per EL
   extraction). After 4 groups, terms are already too large.

2. **Symmetric rewrite rules loop.** `SHA256_COMPRESS_ROUND_KW_SYM` (which
   swaps K and W arguments) is symmetric: `f K W = f W K`. Using it in
   `REWRITE_RULE` causes an infinite loop. It must be applied with
   `ONCE_REWRITE_RULE` or targeted conversions.

3. **Abbreviation management is fragile.** The message schedule `W` is
   abbreviated via `ABBREV_TAC` to keep terms small, but `ASM_REWRITE_TAC` can
   inadvertently expand it, breaking later pattern matching. The solution
   (`UNDISCH_THEN` to temporarily remove, then `ASSUME_TAC` to restore) works
   but is brittle.

4. **Schedule register growth.** In groups 12-15 (which don't update the
   message schedule), the Q4-Q7 registers still carry accumulated schedule
   expressions that can reach millions of characters. This didn't block Phase 3
   (where those registers are unused after the cut-point) but is a concern for
   Phase 4.

### Open Questions Resolved

| Question from Plan | Answer |
|---|---|
| Spec granularity: individual rounds or recursive? | Recursive `sha256_compress n W state` -- enables cut-points at any boundary |
| State representation: list or tuple? | List `[a;b;c;d;e;f;g;h]` -- matches Keccak pattern, works well with EL |
| Message schedule: upfront or on-demand? | Upfront via `sha256_message_schedule 48 M`, abbreviated as `W` |
| Reduction performance? | SHA256H_REDUCE_CONV not needed -- bridging lemmas bypass reduction entirely |
| Register packing effort? | Significant but manageable -- `word_join4` + `WORD_JOIN4_SUBWORD` handle it cleanly |

---

## Lessons Learned from Phase 4

### Loop invariant design

The loop invariant must include ALL state that the postcondition needs,
including quantified memory assumptions that don't change across iterations.
In particular, the K constants table memory must be part of the invariant even
though no iteration modifies it -- because the postcondition needs to know the
memory layout is preserved. Omitting "unchanged" state from the invariant is
the most common source of unprovable exit subgoals.

### Quantified memory propagation through ARM_STEPS_TAC

Quantified memory assumptions (of the form `!i. i < n ==> read ... = ...`)
propagate automatically through `ARM_STEPS_TAC`. `DISCARD_OLDSTATE_TAC`
preserves these assumptions because they are quantified over an index variable,
not the state variable that gets updated. This was initially a major concern
but turned out to work without any special handling.

### The FIRST_ASSUM fix

The single most important lesson of Phase 4. The standard s2n-bignum memory
read pattern uses `FIRST_X_ASSUM` to find and instantiate quantified memory
assumptions. However, `FIRST_X_ASSUM` removes the assumption after use. In
a loop body with 118 ARM steps, the same quantified memory assumption is needed
by multiple steps (e.g., loading different words from the same data block). One
word change -- `FIRST_X_ASSUM` to `FIRST_ASSUM` -- unblocked the entire proof.
This fix applies to any proof where quantified memory is read multiple times.

### Interactive vs end-to-end behavior

The exit subgoal (after the loop completes) was trivial: just `STRIP_TAC` plus
some rewrites. But the `STRIP_TAC` that worked in interactive testing failed in
the end-to-end proof because `REWRITE_TAC[NONOVERLAPPING_CLAUSES]` (applied
earlier in the proof) changed the goal shape in a way that altered how
`STRIP_TAC` decomposed it. The fix was to use more explicit decomposition
(`CONJ_TAC` chains) rather than relying on `STRIP_TAC` to guess correctly.
This is a general hazard: tactics that work interactively on a specific goal
may fail when the goal arrives in a slightly different normal form.

### Session resilience

The pilot spanned multiple days and many agent sessions. Sessions were
interrupted by context window exhaustion, machine reboots, and deliberate
restarts to get fresh context. What made recovery fast:

- **Frequent git commits with CHEAT_TAC placeholders.** Every time a subgoal
  was proved, it was committed. Unfinished subgoals used `CHEAT_TAC` so the
  file always loaded. A new session could load the latest commit, inspect the
  remaining `CHEAT_TAC` sites, and continue.

- **Structured progress notes in memory files.** Each session update included:
  which subgoals were proved, what the current blocker was, what had been tried,
  and what to try next. Good notes named specific tactics, error messages, and
  assumption indices. Vague notes like "working on postcondition" were useless.

- **Persistent HOL Light servers.** `holctl` servers survive session restarts.
  After 8+ minutes of symbolic execution in the loop body, the server state was
  valuable. New sessions checked `holctl list` first and reused surviving
  servers instead of re-running expensive computations.

What could be improved: progress notes were sometimes written too late (after
hitting a wall) rather than proactively (after each milestone). A discipline of
"commit and update progress after every proved subgoal" would make recovery
even faster.

---

## Artifacts Summary

### Final Deliverables (on branch tip)

The final commit contains only the files needed to load and verify the proof,
with all intermediate development files removed.

**Specifications and lemmas (reusable for any SHA-256 implementation):**
- `arm/proofs/utils/sha256_spec.ml` -- FIPS 180-4 SHA-256 spec
- `arm/proofs/utils/sha256_bridge.ml` -- Hardware instruction bridging lemmas

**Assembly:**
- `arm/sha2/sha256_block_data_order_hw.S` + `.o` -- Multi-block with loop (the verified target)

**Proofs:**
- `arm/proofs/sha256_block_core.ml` -- Reusable proof infrastructure (bridge lemma arrays, schedule extraction, cut-point and postcondition tactics)
- `arm/proofs/sha256_block_data_order_hw.ml` -- Multi-block correctness proof (`SHA256_HW_CORRECT`) and subroutine correctness (`SHA256_HW_SUBROUTINE_CORRECT`), fully machine-checked

**Testing and benchmarks:**
- `tests/test.c` -- NIST known-answer + random tests
- `benchmarks/benchmark.c` -- Performance benchmarks

**CI integration:**
- `include/s2n-bignum.h` -- Function declaration with input/output comment
- `arm/Makefile` -- Build rules (object file in OBJ list, proof target auto-generated)
- `tools/collect-signatures.py` -- Function added to `onlyInArm` list
- `arm/proofs/subroutine_signatures.ml` -- Regenerated with function entry

**ISA extension:**
- `arm/proofs/decode.ml`, `arm/proofs/instruction.ml` -- REV32 instruction added
- `arm/proofs/simulator_iclasses.ml` -- REV32 instruction class bit patterns

### Intermediate Development Files (in git history)

The incremental proof steps (Phases 1-3) produced ~40 additional files that
were essential during development but are not needed for the final proof. These
include the register-only core assembly and proof (`sha256_block_core.S`,
`sha256_block_simple.ml`), the incremental step implementations
(`sha256_4rounds_reg`, `sha256_roundgroup`, etc.), generator scripts,
development variants, and scratch/testing files. All remain accessible in the
git history (commits prior to `0d6153ae`) for reference.

### Reusability for Future Targets

The spec and bridging lemmas are implementation-independent. Any ARM64 SHA-256
implementation using SHA256H/SHA256H2/SHA256SU0/SHA256SU1 can reuse:
- `sha256_spec.ml` (unchanged)
- `sha256_bridge.ml` (unchanged)
- The cut-point proof strategy (adapted to the specific instruction sequence)

The Phase 4 loop infrastructure -- `ENSURES_WHILE_UP_TAC` with a quantified
memory invariant covering both mutable state and read-only tables -- transfers
directly to any multi-block hash function (SHA-512, SHA-384, etc.). The key
patterns (quantified memory in the loop invariant, `FIRST_ASSUM` for
multi-read memory, `RECONSTRUCT_BLOCK_TAC` for block element extraction) are
not SHA-256-specific.

For SHA-512, the spec would need new constants and rotation amounts, but the
structure would be identical. For x86 SHA-NI, the instruction semantics have
already been added to s2n-bignum; new bridging lemmas would be needed to
connect them to the spec.
