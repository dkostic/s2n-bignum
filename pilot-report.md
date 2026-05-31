# CRC32C Verification Pilot: 8-Chain Octo-Buffer Kernel Report

## Overview

This report covers the CRC32C formal verification pilot conducted between
2026-05-22 and 2026-05-31 — the second target of the whole-proofs project
following the SHA-256 pilot of April 2026. The verified function is
**`crc32c_octo_zerofill_xor`**, an 8-chain CRC32C kernel that simultaneously
processes eight independent input buffers, produces the XOR of their finalised
CRC32C values, and zero-fills all eight buffers in-place. The kernel is 156
ARM64 instructions including a stack-arg-loading prologue, an 8-init MOV
preamble, a 35-instruction 16-byte main loop with `cmp`/`b.ge` back-edge,
four TBZ-gated tail blocks for residual 8/4/2/1-byte handling, a 7-instruction
EOR-tree XOR reduction, and a 2-instruction epilogue.

The pilot is COMPLETE. Two top-level theorems are machine-checked:

- **`CRC32C_OCTO_ZERO_FILL_XOR_CORRECT`**: the core theorem (PC starts after
  the 2-instruction prologue, ends before the 2-instruction epilogue),
  establishing both the XOR-of-finalised-CRC32C output in `W0` and the
  zero-fill of all 8 input buffers.
- **`CRC32C_OCTO_ZERO_FILL_XOR_SUBROUTINE_CORRECT`**: the standard subroutine
  wrapper, proven via `ARM_ADD_RETURN_STACK_TAC`, with the unusual prologue
  (`str x19, [sp, #-16]!; ldr x19, [sp, #16]`) that loads the 9th stack-passed
  argument `len`.

The full proof file `arm/proofs/crc32c_octo_zerofill_xor.ml` (9514 lines)
loads via `needs "arm/proofs/crc32c_octo_zerofill_xor.ml"` in approximately
85 minutes on a warm `s2n-arm` checkpoint. The final HEAD on branch
`dkostic/crc32c-arm` is `9a21aeab` (closure of the last residue, `len = 15`)
plus `c8fd6eaa` (cosmetic comment scrub of stale CHEAT_TAC references).

The implementation is `~/whole-proofs/crc32.S` adapted to s2n-bignum
visibility/CFI macros: it uses the ARM `crc32cb`/`crc32ch`/`crc32cw`/`crc32cx`
hardware instructions exclusively (no software polynomial reduction).

In addition to the proof, the pilot contributed:

- Three new ISA-model entries in `arm/proofs/{instruction,decode,
  simulator_iclasses}.ml`: TBZ/TBNZ (Phase 0a), LDRH/STRH (Phase 0b),
  CRC32C{B,H,W,X} (Phase 0c) — the first ARM crypto-extension model in
  s2n-bignum.
- A reusable algorithmic specification (`utils/crc32c_spec.ml`, 147 lines).
- A bridging-lemma library (`utils/crc32c_bridge.ml`, 5458 lines) with
  per-residue X-update / memory-close lemma families.
- Four incremental stepping-stone proofs (Phases 5–8).
- A C reference implementation (`reference_crc32c`) and a length-sweep KAT
  test in `tests/test.c`.

The pilot ran across 70 sessions over 10 days, the longest stretch concentrated
in the Phase 9 residue case-split (one residue per session at ~30–60 min load
cost; 16 cases total).

---

## What Was Achieved

### Phase 0a–0c: ISA Model Extensions

Three new instruction families were added to the s2n-bignum ARM ISA model
before any proof work began. This was a deliberate ordering choice (Decisions
Log 2026-05-22): modelling instructions first means the kernel-import smoke
test in Phase 1 is meaningful from the first commit.

**Phase 0a — TBZ/TBNZ (session-001):**
- New ops `arm_TBZ`, `arm_TBNZ` modeled after `arm_CBZ`/`arm_CBNZ`, with the
  14-bit signed offset and 6-bit bit-position encoding.
- Decode patterns wired into `arm/proofs/decode.ml`; iclass strings added.
- Sanity proof on a tiny `tbz x0, #3, .L1` snippet, both branch-taken and
  fall-through paths.

**Phase 0b — LDRH/STRH (session-002):**
- 16-bit halfword variants of `arm_LDRB`/`arm_STRB`, reading `bytes16` rather
  than `bytes8`. Both immediate-offset and post-immediate-offset addressing.
- 4-instruction sanity snippet hitting both forms.

**Phase 0c — CRC32C{B,H,W,X} (session-003):**
- New definitions `crc32c_bit` (single-bit polynomial step) and `crc32c_hw_step`
  (8-bit byte step), wired into ARM_OPERATION_CLAUSES.
- Four `arm_CRC32C*` operations corresponding to the 1/2/4/8-byte hardware
  variants.
- Decode patterns verified against `aarch64-as` for `crc32cb`/`crc32cx`.
- Bit-level model semantically validated against the IETF CRC32C("1") KAT
  (`0x6F0A661C`).
- Sanity proofs `CRC32CB_TEST` and `CRC32CX_TEST` close at the ISA level.

These three commits establish the ISA-level foundation that the rest of the
pilot relies on. The `_ALT` form (a redundant alternative formulation seen in
some other operations) was deliberately omitted, mirroring the Phase 0b
precedent.

### Phase 1: Kernel Import (session-004)

The user-supplied `~/whole-proofs/crc32.S` was copied into
`arm/crc32/crc32c_octo_zerofill_xor.S` with only visibility/CFI macro
adaptations (no machine-code change). `.arch armv8-a+crc` was added so the
file self-elevates to the CRC extension. `CRC32_OBJ` was wired into
`arm/Makefile`.

The decoder smoke test — `define_assert_from_elf` over the assembled `.o` —
succeeded over all 156 instructions. Phase 0 was confirmed to fully cover the
kernel; no fifth unmodeled instruction surfaced.

### Phase 2: KAT Gating (session-005)

A C reference `reference_crc32c` (bit-by-bit, polynomial `0x82F63B78`,
init `0xFFFFFFFF`, finalisation = bitwise NOT) was added at
`tests/test.c:3128`. The full test
`test_crc32c_octo_zerofill_xor` covers:

- IETF `"123456789"` KAT against expected `0xE3069283`.
- Length sweep `len ∈ {0,1,2,3,7,8,9,15,16,17,31,32,33,64,127,128}` × 100
  random trials.
- For each trial: assert both XOR equality and the post-call zerofill of
  all 8 buffers.

`make test && ./test crc32c_octo_zerofill_xor` ran clean (1602 OK). No
ABI/endianness/clobber bugs surfaced. **The kernel was C-level validated
end-to-end before any proof work began.**

### Phase 3: HOL Specification (sessions 006 – 007)

`arm/proofs/utils/crc32c_spec.ml` (147 lines) defines:
- `crc32c_poly_refl = word 0x82F63B78 : int32`
- `crc32c_step : int32 -> bool -> int32` — single-bit reduction
- `crc32c_byte : int32 -> int8 -> int32` — 8-bit byte step (LSB first)
- `crc32c_bytes : int32 list -> int32 -> int32` — folded byte processing
- `crc32c_buffer : byte list -> int32` — full kernel spec (`word_not (crc32c_bytes ... (word 0xFFFFFFFF))`)

Plus `CRC32C_BUFFER_KAT` proving `crc32c_buffer "123456789" = word 0xE3069283`
in ~7s, and reduction conversions `CRC32C_BYTE_CONV` / `CRC32C_BYTES_CONV`.

A late-discovered bug in this phase (renamed parameter `bytes` → `bs` in
`crc32c_buffer`) was a harmless shadowing of `common/components.ml:1458`'s
`bytes` constant — the spec was smoke-tested in isolation, so the load-time
conflict only surfaced when stacking on `arm/proofs/base.ml`. Fixed at
`0a2ebd2a`.

### Phase 4: Bridging Lemmas (session-007)

`arm/proofs/utils/crc32c_bridge.ml` (initial ~106 lines, grew to 5458 lines
by Phase 9) contains five core lemmas:

| Lemma | Statement |
|-------|-----------|
| `CRC32C_STEP_BRIDGE` | spec `crc32c_step` = hw `crc32c_bit` |
| `CRC32CB_BRIDGE` | hw `crc32c_hw_step` = spec `crc32c_byte` (load-bearing) |
| `CRC32CH_BRIDGE` | 2-byte hw step = `crc32c_bytes acc [LE-subword-bytes]` |
| `CRC32CW_BRIDGE` | 4-byte hw step (analogous) |
| `CRC32CX_BRIDGE` | 8-byte hw step (analogous) |

The 1-byte bridge is the load-bearing one; the wider bridges are compositional
and close by `REWRITE_TAC[crc32c_bytes; CRC32CB_BRIDGE]`.

The `_BRIDGE` lemmas express the `n`-byte hardware ops as an `n`-step
`crc32c_bytes`-fold over the LE-subword-extracted byte list — the right shape
for downstream phases to accumulate byte lists from concatenated buffer
contents.

### Phase 5: Tiny Register-Only Proof (session-008)

`arm/proofs/crc32c_step_reg.ml` (79 lines): a 3-instruction toy kernel
`mov w0, #-1; crc32cx w0, w0, x1; ret`, proven correct against the
`crc32c_bytes (word_to_bytes_le v) (word 0xFFFFFFFF)` spec value. This
validates `CRC32CX_BRIDGE` in a real proof context and exercises the new
ISA model end-to-end.

### Phase 6: One-Buffer LDP+CRC+CRC+STP Unit (session-009)

`arm/proofs/crc32c_block16_one.ml` (116 lines): a 4-instruction kernel
`ldp x16, x17, [x0]; crc32cx w8, w8, x16; crc32cx w8, w8, x17;
stp xzr, xzr, [x0], #16`, proving correctness of the 16-byte buffer
zerofill, X0 advance, and `crc32c_bytes` accumulator update. **This is
exactly one slice of the 8-buffer main loop body** — the loop body is 8 such
slices in sequence.

### Phase 7: 8-Buffer Single-Iteration Loop Body (session-010)

`arm/proofs/crc32c_loop16_body.ml` (250 lines): one full iteration of
`.Lxzf_loop16`, 32 buffer-touching instructions plus `sub x19, x19, #16`
(no `cmp`/`b.ge` — those belong to the loop tactic). Postcondition: 8
accumulators advanced by 16 bytes, 8 buffer pointers advanced by 16, len
counter decremented. `ALLPAIRS nonoverlapping` for the 8 buffer + code
regions.

### Phase 8: Multi-Iteration Loop16 (sessions 011 – 015)

`arm/proofs/crc32c_loop16.ml` (559 lines) wraps Phase 7 in
`ENSURES_WHILE_DOWN_TAC` with a loop invariant carrying:
- 8 accumulator values as `crc32c_bytes (consumed_bytes_i) (word 0xFFFFFFFF)`
- 8 pointers advanced by `16 * (initial_iters - i)`
- Quantified-memory facts stating the unconsumed suffix is unchanged and the
  consumed prefix is zeroed.

The most fraught phase of the pilot. Three direction-call decisions
(documented in the Decisions Log) shaped the final shape:

1. **Strategy A pivot (session-013)**: the original parametric-forall
   invariant was silently dropped during `ARM_STEPS_TAC` because
   `COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV` operates per-specific-term
   and could not prove the parametric orthogonality. Strategy A
   (`wordlist_from_memory` pattern from `sha3_keccak_f1600_alt.ml`) was
   proposed.

2. **Strategy A SUPERSEDED (session-014)**: prover-014 found that the
   AES-XTS proof (`aes_xts_encrypt.ml`) survives 183 `ARM_ACCSTEPS_TAC`
   steps with a structurally identical parametric forall. Diagnosis:
   the dropped forall's antecedent `i <= j` includes the write target
   `j = i`. Deriving a *reduced* forall with antecedent
   `i + 1 <= j /\ j < iters` *before* `ARM_STEPS_TAC` — a one-line
   `SUBGOAL_THEN` from the original via SPEC + ASM_ARITH_TAC — excludes
   the write target from each surviving instance. Net effect: ~50-line
   edit to body subgoal only; original invariant preserved.

3. **Loop16 RET refactor (session-015)**: original `crc32c_loop16_mc` had
   36 instructions ending in trailing RET (`0xd65f03c0`); octo's mc had only
   35 in the analogous prefix region. The trailing RET was dropped from both
   the .S and the mc list to avoid a non-trivial byte-prefix lemma in
   downstream phases. Validated: `CRC32C_LOOP16_CORRECT` still proves with
   the 35-instruction mc.

`CRC32C_LOOP16_CORRECT` lands at HEAD `57ce7e25` (later refactored to
`019e4389`).

### Phase 9: Loop+Tail Composition + XOR Reduction + Subroutine Wrapper (sessions 016–069)

By far the longest phase. The strategy doc envisioned this as Phases 9–12
spanning ~5 sessions; in practice the residue case-split inside
`BRANCH_A_TAIL_CLOSURE` (the consolidated Branch A "len < 16" lemma)
absorbed all four phases worth of work into a single 9514-line proof file,
attacked one residue per session.

**Structural decomposition.** The core theorem first sequence-splits at
`pc + 0x28..0x2c` (the `cmp x19, #16; b.lt .Lxzf_tail` entry guard),
producing two branches:

- **Branch A** (`len < 16`): jump to tail entry `pc + 0xbc`, all consumption
  happens in tail blocks.
- **Branch B** (`len >= 16`): fall through to loop entry `pc + 0x30`, `iters
  = len DIV 16` iterations of the main loop, then `residue = len MOD 16`
  bytes of tail.

Both branches end at the same XOR-reduction PC (`pc + 0x24c`) and converge
via the same 7-instruction EOR tree.

The tail blocks are TBZ-gated by bits 3, 2, 1, 0 of `len` (residue), giving
16 cases: `residue ∈ {0, 1, ..., 15}`. Each case has a unique 4-bit
decomposition fixing the four TBZ outcomes; the consumed-byte-count per case
is the 4-bit integer itself.

**Bridge-lemma families (`crc32c_bridge.ml` extension).** Per-residue
X-update and memory-close lemmas were proven and reused across all 16
residue arms:

| Family | Width | Element |
|--------|-------|---------|
| `RESIDUE1_X_UPDATE`, `RESIDUE1_MEMORY_CLOSE` | 1 byte | CRC32CB |
| `RESIDUE2_X_UPDATE`, `RESIDUE2_MEMORY_CLOSE` | 2 bytes | CRC32CH |
| `RESIDUE4_X_UPDATE`, `RESIDUE4_MEMORY_CLOSE` | 4 bytes | CRC32CW |
| `RESIDUE8_X_UPDATE`, `RESIDUE8_MEMORY_CLOSE` | 8 bytes | CRC32CX |

Plus `BYTES8/16/32/64_FROM_BYTELIST` pre-stage helpers and a
`SUB_LIST_SUB_LIST` helper (`!l p n m. p + n <= m ==>
SUB_LIST(p,n) (SUB_LIST(0,m) l) = SUB_LIST(p,n) l`, added at `a9d3b768`)
for collapsing nested bytelist slices.

**Residue closure pattern.** Each residue arm has the same shape: pre-stage
the 8 buffers via `BYTES{8,16,32,64}_FROM_BYTELIST` corresponding to the
bits in the residue's binary expansion; chain `RESIDUE{1,2,4,8}_X_UPDATE`
applications (innermost = highest bit, outermost = lowest bit), with one
`AP_THM_TAC + AP_TERM_TAC` pair per intermediate `crc32c_hw_step` call to
strip; close memory via the parallel chain of `RESIDUE{1,2,4,8}_MEMORY_CLOSE`
applications gated by an explicit `ARITH_RULE` for each addition.

**Composite types by residue.**

| Residue | Bits | Composite type | Sessions |
|---------|------|----------------|----------|
| 0 | 0000 | trivial (no consumption) | 053 |
| 1, 2, 4, 8 | one-bit | single-layer `RESIDUE{1,2,4,8}_X_UPDATE` | 054–057 |
| 3, 5, 6, 9, 10, 12 | 2-bit | 2-way `RESIDUE_a + RESIDUE_b` | 058–063 |
| 7, 11, 13, 14 | 3-bit | 3-way 8-bit-anchored | 065–068 |
| 15 | 1111 | unique 4-way `RESIDUE8+4+2+1` (final) | 069 |

The 4-way residue=15 case took the longest single session (~85 min full
kernel load, 4 TBZs + 4×24 = 100 ARM steps). Once it landed, the
catch-all CHEAT_TAC was removed entirely.

**Phase 9 prologue refactor (session-016).** Before Phase 9 closures
began, a hard blocker surfaced: stepping `str x19, [sp, #-16]!`
directly inside `ARM_STEPS_TAC` failed because the symbolic write
target `word_add sp_in (word 18446744073709551600)` (= `sp_in - 16`
unsigned wrap) doesn't `WORD_RULE`-bridge to the nonoverlapping
driver's `word_sub sp_in (word 16)`. Decision: split the proof into a
CORE theorem (PC range `pc+8..pc+0x268`, assumes X19 = `word len`,
SP = `sp_in - 16`) plus an `ARM_ADD_RETURN_STACK_TAC`-style wrapper.

The wrapper requires the SUBROUTINE forall-list to be a strict superset
of CORE with the extra quantifier (`sp_in`) at the END; this caused
session-018 to reformulate the originally "frozen" public statement
(decisions: drop `init_x19`, drop X19 from MAYCHANGE, reorder `sp_in`
to last). Pattern matches `BIGNUM_EMONTREDC_8N_SUBROUTINE_CORRECT`.

**Late-Phase-9 collapse (session-069).** The Strategy doc envisioned Phase
10 as "full tail composition", Phase 11 as "loop+tail+XOR reduction", and
Phase 12 as "subroutine wrapper". In practice, the existing residue
case-split ladder inside `crc32c_octo_zerofill_xor.ml` already dispatched
to `BRANCH_A_TAIL_CLOSURE` in-place; closing residue=15 effectively
discharged Phases 10–12 in the same file load. Both
`CRC32C_OCTO_ZERO_FILL_XOR_CORRECT` (line 6616 of validation log) and
`CRC32C_OCTO_ZERO_FILL_XOR_SUBROUTINE_CORRECT` (line 9454) printed
cleanly as `thm`s in the same load. The 16-phase strategy collapsed into
Phase 13 (CI / wrap-up) for session-070.

---

## Key Technical Findings

### What Worked Well

1. **The incremental Phase 5–8 stepping-stones paid off.** Phase 5 (3-instr
   toy) validated `CRC32CX_BRIDGE` in a real proof context. Phase 6 (one
   buffer) added memory I/O. Phase 7 (8 buffers, no loop) validated the
   `ALLPAIRS nonoverlapping` setup. Phase 8 (multi-iteration loop) validated
   the loop invariant and quantified-memory pattern. Each phase caught a
   different class of issue early.

2. **The residue case-split was uniform.** The 16 residue arms in Path C all
   follow the same pattern (pre-stage with `BYTES_FROM_BYTELIST`, chain
   `RESIDUE_X_UPDATE`s, close with `RESIDUE_MEMORY_CLOSE`s). The Python
   generator approach (`/tmp/s068/gen_residue14.py`,
   `/tmp/s069/gen_res15.py`) avoided transcription error across hundreds of
   mostly-mechanical lines.

3. **The bridge-lemma factoring scaled.** Once `RESIDUE{1,2,4,8}_X_UPDATE`
   and `RESIDUE{1,2,4,8}_MEMORY_CLOSE` existed, every composite residue
   (2-way, 3-way, 4-way) reused them mechanically. The only per-residue
   work was the explicit `ARITH_RULE` for each nested addition (e.g.
   `8 + 4 = 12`, `12 + 2 = 14`, `14 + 1 = 15`).

4. **The s2n-bignum infrastructure handled the new ISA cleanly.** Adding
   TBZ/TBNZ, LDRH/STRH, and CRC32C{B,H,W,X} to `instruction.ml`, `decode.ml`,
   and `simulator_iclasses.ml` was mechanical — the existing
   `arm_CBZ`/`arm_CBNZ`, `arm_LDRB`/`arm_STRB`, and bit-level operation
   patterns provided clean templates.

### What Didn't Work (Direction Calls Made)

1. **The original parametric-forall loop invariant.** Strategy A
   (`wordlist_from_memory` pattern) was proposed in session-013 to work
   around `ASSUMPTION_STATE_UPDATE_TAC`'s inability to prove parametric
   orthogonality. **Superseded by session-014's reduced-forall trick**:
   the actual mechanism is that the original forall's antecedent `i <= j`
   includes the write target; deriving a reduced forall over
   `i + 1 <= j /\ j < iters` before stepping excludes the write target,
   and the per-specific-term orthogonality conv succeeds for each surviving
   instance. **Reusable lesson**: for any per-iteration loop body where a
   parametric forall ranges over a write region, derive the reduced forall
   before stepping.

2. **The `crc32c_loop16` trailing RET.** Original `_loop16.S` ended in RET,
   matching the SHA-256 pilot's stepping-stone shape. But the octo kernel
   has no such RET in its loop region (followed instead by TBZ). Without
   refactor, `ARM_BIGSTEP_TAC CRC32C_LOOP16_CORRECT` would need a non-trivial
   byte-prefix lemma. The RET was dropped from both .S and mc list (with
   `aligned_bytes_loaded` only constraining the bytes that still match);
   this was a one-time refactor and downstream phases ignored the trailing
   RET entirely.

3. **The "frozen public statement" of `_SUBROUTINE_CORRECT`.** Three
   syntactic changes (logically equivalent, mutually derivable) were needed
   in session-018 to fit `ARM_ADD_RETURN_STACK_TAC`'s expectations:
   (a) reorder `sp_in` to LAST in the forall-list; (b) drop `init_x19`
   universal + `read X19 s = init_x19` conjunct (X19 preservation is
   implicit because X19 is not in MAYCHANGE); (c) drop X19 from MAYCHANGE.
   Pattern matches `BIGNUM_EMONTREDC_8N_SUBROUTINE_CORRECT`.

### Open Questions Resolved

| Question | Answer |
|----------|--------|
| Should `_ALT` instruction forms be added? | No — Phase 0b/0c precedent. |
| Should the spec use polynomial-step or byte-step granularity? | Byte step (`crc32c_byte`), with a `crc32c_step` polynomial-step helper. |
| Strategy A vs reduced-forall for loop invariant? | Reduced forall (session-014). |
| Is BIGSTEP-deferral acceptable? | Only with a live consumer (advisor-021). |
| 16 residue arms one-per-session — can we compress? | Yes, but the 1-residue-per-session pace was reliable and easy to review. |
| Phase 10/11/12 separate vs. collapsed? | Collapsed automatically by the case-split ladder. |

---

## Lessons Learned

### Loop invariant design

The loop invariant must include ALL state that the postcondition needs,
including quantified memory assumptions for read-only data (the K table in
SHA-256 had this; the consumed-prefix-is-zero / unconsumed-suffix-unchanged
assertion is the analogue here).

For per-iteration loop bodies that write to a quantified region, derive a
reduced forall whose antecedent excludes the current write target *before*
stepping. The natural form is a one-line `SUBGOAL_THEN` from the original
forall via `SPEC + ASM_ARITH_TAC`. This is the single most reusable
tactical lesson from Phase 8.

### The residue case-split

When a function has TBZ-gated tail blocks for the low bits of a remaining-
length counter, the natural decomposition is a 16-way (or 2^k-way) case
split on the residue. Each case fixes the TBZ outcomes and reduces to a
straight-line proof. The bridge-lemma factoring (one `RESIDUE_X_UPDATE` +
one `RESIDUE_MEMORY_CLOSE` per width) makes the per-case work mechanical.

### Python generators for mechanical edits

Many residue closures involved 600–900 lines of structurally identical
proof script differing only in a buffer index (0..7) or width (1/2/4/8).
Hand-typing these is error-prone; using a small Python generator
(`/tmp/s068/gen_residue14.py`, ~200 lines) to emit the proof script
cut typo risk to near-zero. Reviewers accepted this as a legitimate
engineering tool.

### Session resilience

The pilot ran across 70 sessions. Practices that survived:

- **`CHEAT_TAC` placeholders for unfinished residue arms.** Each session's
  commit either closed one residue (shrinking the inner CHEAT_TAC's
  remaining-residue set) or made forward bridge progress. The file
  always loaded cleanly.

- **Per-session structured progress notes in STATE.md and session
  summaries.** Each session ended with: which residue closed, what the
  next residue's structural diff was, what helpers were needed, what
  ARITH_RULEs to carry forward.

- **Long-lived `s053-validate` server.** Held the full s2n-arm checkpoint
  across multiple validation runs. New residue closures triggered an ~85-min
  full kernel load to confirm green.

What could be improved: the Phase 9 work was monotonic (one residue per
session) but slow. A single late-pilot session that closed multiple
residues at once was attempted but not pursued because the per-session
verification cost was dominated by the kernel load, not the new closure
itself. With a faster validation path, residues 1–15 could plausibly
collapse to 3–4 sessions.

---

## Artifacts Summary

### Final Deliverables

**Specifications and lemmas (reusable for any CRC32C implementation):**
- `arm/proofs/utils/crc32c_spec.ml` — algorithmic CRC32C spec
- `arm/proofs/utils/crc32c_bridge.ml` — hardware bridging + per-residue
  X-update/memory-close lemma families

**Assembly:**
- `arm/crc32/crc32c_octo_zerofill_xor.S` + `.o` — the verified target

**Proofs:**
- `arm/proofs/crc32c_octo_zerofill_xor.ml` — main correctness proof
  (`CRC32C_OCTO_ZERO_FILL_XOR_CORRECT` and
  `CRC32C_OCTO_ZERO_FILL_XOR_SUBROUTINE_CORRECT`), fully machine-checked

**Stepping-stone proofs (Phases 5–8, retained for reference):**
- `arm/proofs/crc32c_step_reg.ml` — Phase 5 (tiny register-only)
- `arm/proofs/crc32c_block16_one.ml` — Phase 6 (one-buffer LDP+CRC+CRC+STP)
- `arm/proofs/crc32c_loop16_body.ml` — Phase 7 (8 buffers, no loop)
- `arm/proofs/crc32c_loop16.ml` — Phase 8 (multi-iteration loop)

Their `.S` and `.o` siblings live in `arm/crc32/`.

**Testing:**
- `tests/test.c` (`test_crc32c_octo_zerofill_xor`, `reference_crc32c`)

**ISA extensions:**
- `arm/proofs/instruction.ml` — TBZ, TBNZ, LDRH, STRH, CRC32C{B,H,W,X}
- `arm/proofs/decode.ml` — decode bitmatches for all five
- `arm/proofs/simulator_iclasses.ml` — iclass strings

**CI integration:**
- `include/s2n-bignum.h` — function declaration with input/output comment
- `arm/Makefile` — `CRC32_OBJ` includes `crc32c_octo_zerofill_xor.o`
- `arm/proofs/subroutine_signatures.ml` — `crc32c_octo_zerofill_xor` entry

### Reusability for Future Targets

The CRC32C spec and bridging lemmas are implementation-independent. Any
ARM64 CRC32C implementation using the `crc32c{b,h,w,x}` instructions can
reuse:
- `crc32c_spec.ml` (unchanged)
- `crc32c_bridge.ml` (the `CRC32C{B,H,W,X}_BRIDGE` lemmas; the per-residue
  families would need re-statement against a new buffer count, but the
  proof technique transfers)

The Phase 8 reduced-forall trick (derive a write-target-excluding forall
before `ARM_STEPS_TAC`) transfers to any per-iteration loop body that
writes to a region also covered by a quantified-memory invariant.

The Phase 9 residue case-split (uniform 2^k-way split on the low bits of
a length counter) transfers to any function with TBZ-gated tail blocks.

---

## Project Statistics

- **10 days** of wall-clock from kickoff (2026-05-22) to closure (2026-05-31).
- **70 sessions**, with the longest concentration in Phase 9 residue closures
  (sessions 053–069, ~30–60 min each on s053-validate).
- **120 commits** on `dkostic/crc32c-arm` branch beyond `origin/main`.
- **156 instructions** verified in the final kernel.
- **~16,000 lines** of HOL Light proof artifact across 9 .ml files.
- **0 admissions** in the final proof (no `cheat`, no `mk_thm`, no
  `new_axiom`, no `SORRY_TAC`).
