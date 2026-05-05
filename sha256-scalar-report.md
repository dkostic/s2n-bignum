# SHA-256 Scalar (no-HW) Verification Report

## Overview

This report summarises the formal verification of five ARM64
SHA-256 implementations that use *only* base integer instructions (no
SHA-256 crypto extensions, no NEON):

- **`sha256_block_data_order_nohw`**  -- baseline scalar reference
- **`sha256_block_data_order_nohw2`** -- shifted-register EOR fusion +
  fused Maj (1.13x speedup)
- **`sha256_block_data_order_nohw4`** -- nohw2 fusions +
  message-schedule/compression interleaving (1.36-1.39x speedup)
- **`sha256_block_data_order_nohw5`** -- nohw4 fusions +
  message schedule kept in 16 registers instead of stack scratch
  (1.52-1.53x speedup)
- **`sha256_block_data_order_nohw6`** -- nohw5 + cyclic state-register
  naming + intra-round schedule/compression interleaving
  (1.61x speedup)

All five are scalar complements to `sha256_block_data_order_hw`
(verified in the SHA-256 pilot; see `pilot-report.md`) and can be
linked into the same `libs2nbignum.a`.

The function processes `num_blocks >= 1` consecutive 512-bit message
blocks and updates an 8-word state in place. Its C signature is

```c
void sha256_block_data_order_nohw(
    uint32_t      state[8],
    const uint8_t *data,
    uint64_t       num_blocks,
    const uint32_t k[64]);
```

The K round-constant table is passed as a pointer (rather than embedded
via PC-relative addressing) to match the convention of the HW variant.

All top-level theorems for all five variants load without
`CHEAT_TAC` on top of the existing s2n-bignum ARM infrastructure:

```
needs "arm/proofs/sha256_block_data_order_nohw.ml";;   (* CHEAT-free *)
needs "arm/proofs/sha256_block_data_order_nohw2.ml";;  (* CHEAT-free *)
needs "arm/proofs/sha256_block_data_order_nohw4.ml";;  (* CHEAT-free *)
needs "arm/proofs/sha256_block_data_order_nohw5.ml";;  (* CHEAT-free *)
needs "arm/proofs/sha256_block_data_order_nohw6.ml";;  (* CHEAT-free *)
```

## What has been proven

Two theorems (`arm/proofs/sha256_block_data_order_nohw.ml`):

- **`SHA256_BLOCK_DATA_ORDER_NOHW_CORRECT`** -- core correctness
  (post-prologue to pre-epilogue):
  ```
  !num_blocks blocks a b c d e f g h state_ptr data_ptr kptr pc stackpointer.
    1 <= num_blocks /\ num_blocks < 2 EXP 64 /\
    LENGTH blocks = num_blocks /\ ALL (\bl. LENGTH bl = 16) blocks /\
    <nonoverlapping constraints> /\ aligned 16 stackpointer
    ==> ensures arm
      (\s. read PC s = word (pc + 0x14) /\
           <initial state: registers, memory regions for state, data, K>)
      (\s. read PC s = word (pc + 0x1b0) /\
           !t. t < 8 ==>
               read (memory :> bytes32 (word_add state_ptr (word (4*t)))) s =
               EL t (sha256_hash_blocks num_blocks blocks [a;b;c;d;e;f;g;h]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26] ,,
       MAYCHANGE [memory :> bytes(state_ptr,32);
                  memory :> bytes(stackpointer,256)])
  ```
  i.e. for any number of blocks, the function correctly applies
  `sha256_hash_blocks` -- the iterated per-block compression defined in
  `arm/proofs/utils/sha256_spec.ml`, which in turn mirrors the FIPS 180-4
  compression function.

- **`SHA256_BLOCK_DATA_ORDER_NOHW_SUBROUTINE_CORRECT`** -- full
  subroutine including prologue/epilogue, obtained by applying
  `ARM_ADD_RETURN_STACK_TAC` to the core theorem with a 320-byte stack
  frame (256 bytes for the message-schedule scratch + 64 bytes for
  callee-saved `x19..x26`).

Together these establish functional correctness of the entire 114-
instruction function against the FIPS 180-4 specification.

## Specification chain

The proof is stated against the same spec used by the HW variant:

- **`sha256_hash_blocks n blocks H`** (iterated hashing over a list of
  blocks) -- unchanged from the pilot.
- **`sha256_block M H`** (one-block compression; add-back of initial
  hash to 64-round compressor output) -- unchanged.
- **`sha256_compress i W H`** (iterated round function) and
  **`sha256_compress_round K_t W_t H`** (single round) -- unchanged.
- **`sha256_message_schedule n M`** (extends 16-word input to 16+n-word
  schedule) -- unchanged.
- **`sha256_sigma0/sigma1`**, **`sha256_Sigma0/Sigma1`**,
  **`sha256_Ch`**, **`sha256_Maj`** -- unchanged.

No new spec functions were introduced; the proof targets the existing
`sha256_hash_blocks` used for the HW proof.

## Implementation structure

`arm/sha2/sha256_block_data_order_nohw.S` (181 lines, 456 bytes) has
five instruction-level phases plus prologue/postamble/epilogue:

- Prologue (pc+0..0x14): 5 instructions. `sub sp, sp, #320`; save
  `x19..x26` on top of the frame.
- Block loop (pc+0x14..pc+0x1ac), repeated `num_blocks` times:
  - **Phase A** (pc+0x14..pc+0x30, 7 instr): load 16 words from
    `data_ptr`, byte-reverse with `rev`, store to stack scratch.
  - **Phase B** (pc+0x30..pc+0x90, 24 instr): extend schedule to 64
    words via 48 iterations of `sigma0 + sigma1 + add`. Uses `x4` (not
    `x2`) as the scratch-pointer register so that `x2` (block counter)
    stays live across the phase.
  - **Phase C** (pc+0x90..pc+0xd0, 16 instr): load initial state into
    `w4..w11` and save a copy to callee-saved `w19..w26`.
  - **Phase D** (pc+0xd0..pc+0x164, 37 instr): 64-round compression
    loop. One round per iteration; uses `Sigma0/Sigma1/Ch/Maj` on the
    32-bit W-subregister views of `x4..x11`.
  - **Phase E** (pc+0x164..pc+0x184, 8 instr): 8 `add w*, w*, w*`
    instructions for the state add-back.
  - **Phase F** (pc+0x184..pc+0x1a4, 8 instr): 8 `str w*, [x0, #N]` to
    write the updated state back to memory.
  - Postamble (pc+0x1a4..pc+0x1ac, 2 instr): `add x1, #64; sub x2, #1`.
  - Back-edge (`cbnz x2, .Lblock_loop`).
- Epilogue (pc+0x1b0..pc+0x1c4): restore callee-saved registers,
  deallocate frame, `ret`.

## Proof strategy

The proof was built bottom-up in five steps; each was committed as a
self-contained, closed theorem before the next began:

1. **Step 1** (`sha256_1round_scalar.ml`): single compression round,
   proving one iteration of the 36-instruction Phase D body maps to
   `sha256_compress_round`.
2. **Step 2** (`sha256_core_scalar.ml`): the 64-round compression loop
   against `sha256_compress 64 W H`.
3. **Step 3** (`sha256_schedule_scalar.ml`): the 48-iteration schedule
   extension against `sha256_message_schedule 48 M`.
4. **Step 4** (`sha256_block_scalar.ml`): the single-block composite --
   schedule + 64 rounds + add-back -- against `sha256_block M H`. Both
   `_CORRECT` and `_SUBROUTINE_CORRECT` theorems close.
5. **Step 5** (`sha256_block_data_order_nohw.ml`): the multi-block
   wrapper. An outer `ENSURES_WHILE_UP_TAC` induction over
   `num_blocks`; the body subgoal re-uses the single-block proof by
   introducing ghost variables `dptr_i`, `H_i`, `M_i`, and
   destructuring `H_i` into `a_i..h_i` via `LIST_8_EL` so that every
   tactic from Step 4 transfers verbatim.

At each step the ARM assembly structure (cut-point offsets, register
allocations, instruction layout) is identical to the single-block
variant, so porting was mainly a matter of refreshing invariants to
carry the newly-relevant ghost state (the block index `ii`, the
advanced data pointer `dptr_i`, the iterated hash `H_i`).

## Notable engineering findings

Two surprises emerged during Step 5 that are worth recording:

- **`ASM_ARITH_TAC` is unusable inside the multi-block body subgoal.**
  After Step 5's ghost-variable setup + Phase B/D symbolic execution,
  the goal state has ~70 hypotheses including many complex non-
  arithmetic terms (`word_zx (word_zx (EL i (sha256_compress ...)))`,
  long `forall t. ...` data memory quantifiers, the eight
  `EL i H_i = x_i` abbreviations). `ASM_ARITH_TAC` then runs for
  *hours* without completing. The fix is to replace every in-body
  `ASM_ARITH_TAC` with a targeted
  `UNDISCH_TAC \`<relevant hyp>\` THEN ARITH_TAC`, which completes in
  milliseconds. Outer-level calls (with ~12 hyps) are fine unchanged.

- **Register preservation across intermediate invariants matters even
  when not used internally.** Single-block proofs drop `X1` (data
  pointer) and the unchanged data/K memory quantifiers from their
  Phase A exit invariant onwards, because the single-block
  postcondition doesn't need them. The multi-block postamble
  (`add x1, x1, #64; sub x2, x2, #1`) and the loop postcondition at
  `pc+0x1ac` both *do* need them, so every intermediate
  `ENSURES_SEQUENCE_TAC` post-assertion must explicitly carry `X1 =
  dptr_i`, `X3 = kptr`, and the data/K memory quantifiers -- a
  verbatim port of the single-block invariants to the multi-block
  body therefore fails at Phase F with `NO_TAC` on
  `read X3 s = kptr`.

Both findings are written up in the memory files
`feedback_asm_arith_in_big_contexts.md` and
`feedback_x1_x3_track_through_invariants.md` for future multi-block
ports.

## Performance

On Graviton (2.5 GHz Neoverse-V1):

| Function                                                       | 1 block | 16 blocks | vs baseline |
|----------------------------------------------------------------|---------|-----------|-------------|
| `sha256_block_data_order_hw` (SHA-256 extension)               | 38 ns   | 575 ns    | 7.3x / 7.6x |
| `sha256_block_data_order_nohw` (baseline scalar)               | 276 ns  | 4393 ns   | 1.00x       |
| `sha256_block_data_order_nohw2` (fusion)                       | 243 ns  | 3891 ns   | 1.14x / 1.13x |
| `sha256_block_data_order_nohw4` (fusion + interleave)          | 198 ns | 3236 ns    | 1.39x / 1.36x |
| `sha256_block_data_order_nohw5` (nohw4 + W in registers)       | 181 ns | 2872 ns    | 1.52x / 1.53x |
| `sha256_block_data_order_nohw6` (nohw5 + cyclic state naming)  | 171 ns | 2710 ns    | **1.61x / 1.62x** |

For reference, the AWS-LC `sha256_block_data_order_nohw` (based on
OpenSSL's hand-written AArch64 scalar implementation) runs at
approximately 164 ns/block on the same host, so the gap from nohw6 to
a best-in-class hand-tuned scalar is ~4%. The remaining gap is mostly
explained by AWS-LC's 64-bit `ldp` data loads (the s2n-bignum proof
infrastructure does not yet model 32-bit `ldp w*`, see
`feedback_32bit_ldp_stp_fail.md`).

`nohw5` keeps the full message-schedule window in 16 registers
(`w12..w17, w19..w28`) with a rotating logical-to-physical slot
mapping, eliminating the 256-byte stack scratch used by the prior
variants. The .S is verified correct via the test harness (201 random
tests + NIST "abc" vector across 1- and 2-block inputs), and the
full HOL Light proof closes without `CHEAT_TAC` (`check_axioms()`
reports only the three standard HOL axioms).

The baseline scalar variant is intentionally written for
verifiability rather than peak throughput: a single round per loop
iteration, no manual software pipelining, no
message-schedule / compression interleaving.

Both optimised variants are drop-in replacements with the same ABI.
Their proofs are ports of the baseline proof with the minimal edits
required for each optimisation.

### Optimisations in `nohw2`

1. **Shifted-register EOR fusion for all four sigma functions.**
   The classical sequence
   ```asm
   ror Wt, Wn, #r1
   eor Wd, Wd, Wt
   ```
   is fused into the single instruction
   ```asm
   eor Wd, Wd, Wn, ror #r1
   ```
   This applies to `sigma0`, `sigma1`, `Sigma0`, `Sigma1`, saving
   4 instructions per schedule iteration and 6 instructions per
   compression round.

2. **Fused Maj.** `Maj(a,b,c)` is computed as `(a AND b) XOR ((a XOR b) AND c)`
   (4 instructions) rather than `(a AND b) XOR (a AND c) XOR (b AND c)`
   (5 instructions). Semantically equivalent; saves 1 instruction
   per round.

Total: 384 instructions saved in the compression loop + 192 in the
message-schedule extension = 576 instructions per block. The
`.S` shrinks from 456 bytes to 420 bytes; cut-point offsets shift
accordingly (Phase B exit pc+0x90 → pc+0x80, Phase D exit
pc+0x164 → pc+0x140, epilogue pc+0x1b0 → pc+0x18c).

### Proof changes (nohw2)

Because the phase structure, register allocation, stack frame, ABI,
and loop invariants are all unchanged, the optimised proof is a
verbatim copy of the baseline with three edits:

- **Offset and step-count updates.** `0x90 → 0x80`, `0x164 → 0x140`,
  `0x1b0 → 0x18c`, `0x1ac → 0x188`, `0x1c8 → 0x1a4`, `0xd4 → 0xc4`,
  `0xd0 → 0xc0`; Phase D body `1--36 → 1--31`; Phase B body
  `1--22 → 1--18`.

- **Normalise `word_ror` to `word_subword(word_join ...)` form in
  Phase D body.** The shifted-register EOR encoding uses
  `regshift_operation ROR = word_ror`, so `ARM_STEPS_TAC` now
  produces `word_ror` in hypotheses, whereas the postcondition --
  already rewritten by `SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF]` --
  is in `word_subword(word_join ...)` form. Adding a second
  `SIMP_TAC[GSYM WORD_SUBWORD_JOIN_SELF; DIMINDEX_32; ARITH]` pass
  after `ARM_STEPS_TAC` normalises both sides. (The baseline did
  not need this because `arm_ROR` is defined via `arm_EXTR`, which
  produces `word_subword` directly.)

- **`CONV_TAC WORD_RULE` after `REWRITE_TAC[BIC_NORM]`** to close
  the register-equality subgoals. The fused-Maj form differs in
  bracketing and commutativity from the classical form; `WORD_RULE`
  handles the full word-level ring equivalence.

Both `SHA256_BLOCK_DATA_ORDER_NOHW2_CORRECT` and
`SHA256_BLOCK_DATA_ORDER_NOHW2_SUBROUTINE_CORRECT` close without
`CHEAT_TAC`. `check_axioms()` reports no additional axioms.

### Artefacts (nohw2)

| Path                                                       | Purpose                                  |
|------------------------------------------------------------|------------------------------------------|
| `arm/sha2/sha256_block_data_order_nohw2.S`                 | Optimised assembly (170 lines, 420 bytes)|
| `arm/proofs/sha256_block_data_order_nohw2.ml`              | Full HOL-Light proof                     |
| `include/s2n-bignum.h`                                     | C declaration                            |
| `arm/Makefile`                                             | Build integration                        |
| `benchmarks/benchmark.c`                                   | Benchmark entry                          |
| `tests/test.c`                                             | Cross-check test vs baseline + reference |

### Optimisations in `nohw4`

nohw4 keeps both of nohw2's fusions (shifted-register EOR and fused
Maj) and adds **message-schedule / compression interleaving**: the
separate Phase B loop of nohw/nohw2 is fused into the first 48
compression rounds. Each fused iteration t in `[0, 48)` now:

1. Performs compression round t on the scalar state using `K[t]` and
   the already-extended `W[t]` from the stack.
2. Computes `W[t+16] = W[t] + sigma0(W[t+1]) + W[t+9] + sigma1(W[t+14])`
   and stores it to the stack.

The schedule step's computation is independent of the compression
state, so the out-of-order backend can co-schedule schedule-side
ops with compression-side ops, hiding the serial Sigma/Ch/Maj/T1/T2
dependency chain that bottlenecks nohw2. Rounds 48..63 run in a
D-tail loop identical in shape to the nohw2 Phase D body.

Other structural changes:

- **Phase C moves ahead of the fused loop.** State must live in
  `w4..w11` when the first compression round runs; nohw/nohw2 load
  it after Phase B.
- **X27 is added to the callee-saved set.** The fused body needs
  `w16` as compute scratch, so the persistent schedule-base pointer
  cannot stay in x16; x27 takes that role. Stack frame grows from
  320 to 336 bytes (extra stp/ldp pair for x27/x28; x28 is just
  padding for the paired save).

Net instruction delta relative to nohw2 per block:

- **Phase B (message-schedule extension) gone**, 360 instructions removed.
- **Fused B+D loop body is 46 instructions** instead of 31 (nohw2 Phase D)
  + 18 (nohw2 Phase B) = 49: a net reduction of 3 per iteration, so
  `48 * 3 = 144` instructions saved over the fused range.
- **D-tail** (rounds 48..63) identical to nohw2 Phase D.
- Phase A unchanged; Phase E, F unchanged.

Measured speedup: **1.39x on 1-block, 1.36x on 16-block** relative
to the `nohw` baseline; **1.23x / 1.20x** on top of the `nohw2`
fusions alone.

### Proof changes (nohw4)

The proof (`arm/proofs/sha256_block_data_order_nohw4.ml`, ~860 lines)
ports all of nohw2's phase proofs with the following changes:

- **Offsets shift throughout.** New structural offsets (from objdump):
  Phase A `pc+0x18 .. pc+0x34`, Phase C `pc+0x34 .. pc+0x74`,
  fused B+D setup `pc+0x74 .. pc+0x7c`, fused B+D loop
  `pc+0x7c .. pc+0x134`, D-tail loop `pc+0x134 .. pc+0x1b0`, Phase E
  `pc+0x1b0 .. pc+0x1d0`, Phase F `pc+0x1d0 .. pc+0x1f0`. Program
  size is 0x218 (was 0x1a4 for nohw2). Prologue/epilogue grow to
  6/6 instructions (was 5/5).

- **`ENSURES_WHILE_AUP2_TAC 48 64 pc+0x134 pc+0x1b0`** for the
  D-tail. `AUP2_TAC` (start..end variant) lets the D-tail loop run
  from 48 to 64 directly, so the loop counter range aligns with the
  compress-step index. The body proof is identical to nohw2 Phase D.

- **Fused B+D loop invariant.** Abbreviate `W = sha256_message_schedule 48 M_i`
  (the eventual full schedule), then invariant at j carries:
  - `read X{4+p} s = word_zx (EL p (sha256_compress j W H_i))`
  - `read X27 s = word_add stackpointer (word (4 * j))`
  - `!t. t < j + 16 ==> stack[4*t] s = EL t W`

  At j=0 the stack prefix matches M_i via `SHA256_SCHEDULE_PREFIX`
  (EL t (schedule 0 M) = EL t M for t < 16). At j=48 the full stack
  matches W.

- **New subgoal: stack memory forall post-iter.** After the body's
  46 ARM steps (including the b.ne), the stack-memory conjunct
  becomes `!t. t < j + 17 ==> stack[4*t] = EL t W`. For t < j+16 the
  inductive hypothesis closes it directly; for t = j+16 (newly
  stored), `SHA256_W_EXTEND` reduces `EL (j+16) W` to
  `word_add (sigma1(EL (j+14) W')) (word_add (EL (j+9) W') ...)`
  where `W' = sha256_message_schedule j M_i`. Fold `W' → W` via
  `SHA256_SCHEDULE_MONO` (at k < j+16, schedule j and schedule 48
  agree). Then `sha256_sigma0/sigma1` unfold to word_subword form,
  and `CONV_TAC WORD_RULE` closes by ring-equivalent add-association.

- **Per-conjunct closure after ENSURES_FINAL_STATE_TAC.** Unlike
  nohw2 (4 explicit branches: PC, X17, X4, X8), nohw4's fused body
  closes most conjuncts generically with
  `TRY(REWRITE_TAC[BIC_NORM] THEN CONV_TAC WORD_RULE)`. That handles
  X4..X11 (via BIC_NORM for Ch/Maj + WORD_RULE for ring eq),
  X17 counter, and X27 base. The two remaining goals -- the
  stack-memory forall and the PC branch condition -- get dedicated
  tactic blocks.

Both `SHA256_BLOCK_DATA_ORDER_NOHW4_CORRECT` and
`SHA256_BLOCK_DATA_ORDER_NOHW4_SUBROUTINE_CORRECT` close without
`CHEAT_TAC`. `check_axioms()` on a fresh session reports no
additional axioms.

### Artefacts (nohw4)

| Path                                                       | Purpose                                  |
|------------------------------------------------------------|------------------------------------------|
| `arm/sha2/sha256_block_data_order_nohw4.S`                 | Optimised assembly (225 lines, 536 bytes)|
| `arm/proofs/sha256_block_data_order_nohw4.ml`              | Full HOL-Light proof (~860 lines)        |
| `include/s2n-bignum.h`                                     | C declaration                            |
| `arm/Makefile`                                             | Build integration                        |
| `benchmarks/benchmark.c`                                   | Benchmark entry                          |
| `tests/test.c`                                             | Cross-check test vs baseline + reference |

### Optimisations in `nohw5`

nohw5 keeps all of nohw4's fusions (shifted-register EOR, fused Maj,
schedule/compression interleaving) and further eliminates the
256-byte stack scratch used for the 16-word sliding schedule window.
The entire window lives in 16 registers (`w12..w17, w19..w28`), and
each compression round reads `W[t]` from the slot register currently
holding it and writes `W[t+16]` back to the same slot once `W[t]` is
consumed. The logical-to-physical slot mapping rotates by one every
round, so after 16 rounds every slot has been overwritten exactly
once with the corresponding 16-advanced schedule word, returning the
mapping to its starting shape.

To keep the fused B+D loop unrolled at instruction level without
blowing up code size, the 48 fused rounds are expressed as **three
iterations of a 16-round unrolled "period"**. Rounds 48..63 remain
in a 16-round unrolled D-tail (identical in shape to nohw4's D-tail
body but reading `w*` from slot registers instead of from stack).

Net effect per block relative to nohw4:

- **Stack scratch gone.** 48 `str` (write schedule to stack) + 64
  `ldr` (read schedule during compression, across the 48 fused rounds
  + 16 D-tail rounds) eliminated. Stack frame shrinks from 336 bytes
  to 112 bytes (just the 16 callee-saved-register slots + 16 bytes
  for spilling `x1`/`x2`).
- **Slot-register rotation replaces one post-round `str`**. Each fused
  round previously wrote `W[t+16]` to stack (1 instruction); now the
  register that held `W[t]` is simply overwritten by the schedule-side
  result. Reads are zero-cost (the slot reg is already the operand).
- **No new scratch register required** -- the three bookkeeping
  registers (`x0..x2`) previously used for schedule arithmetic and
  `K[t]` load remain in the same roles.

Measured speedup: **1.52x on 1-block, 1.53x on 16-block** relative to
the `nohw` baseline; **1.09x / 1.13x** on top of the `nohw4`
schedule/compression interleaving alone.

### Proof changes (nohw5)

The proof (`arm/proofs/sha256_block_data_order_nohw5.ml`, ~5800
lines) is substantially larger than nohw4's because it cannot reuse
nohw4's stack-based schedule invariants -- the sliding-register
window has to be tracked through every round. Key structural
elements:

- **`LIST_8_COMPRESS_NOHW5` helper lemma.** Destructures
  `sha256_compress n W H` into eight fresh `int32` variables for
  symbolic `n`. Needed because `EL j (sha256_compress n W H)` does
  not reduce by `EL_CONV` when `n` is a symbolic `num` -- it
  requires a concrete `n+1` pattern to unfold via the definition's
  recursive clause. Destructuring bypasses the definition entirely:
  after the lemma introduces `a_pk..h_pk` with
  `sha256_compress n W H = [a_pk;..;h_pk]`, subsequent `EL_CONV` on
  the list reduces directly to the fresh variables.

- **Period 0 (rounds 0..15): 16 ROUND_SCHED bodies unrolled inline**,
  each concrete-index. The per-round proof uses the standard Step-1
  single-round tactic with added `SHA256_W_EXTEND + SCHEDULE_MONO`
  bridging to fold `schedule k M_i` (still incomplete at round k)
  into `schedule 48 M_i = W` for the indices actually read
  (`k, k+1, k+9, k+14`). The initial `EL t M_i = EL t W` bridge for
  `t < 16` is discharged with `SHA256_SCHEDULE_PREFIX`.

- **Periods 1, 2: `ENSURES_WHILE_UP_TAC` over two iterations.**
  Preserves the 16 inline p=0 rounds; replaces only the post-p=0
  back-edge and two remaining periods. Invariant is parameterized
  by iteration index `i`:
  ```
  X30 = word (2 - i),  X3 = word_add kptr (word (64 * (i + 1))),
  X4..X11 = sha256_compress (16 * (i + 1)) W H_i,
  slot(m) = EL (16 * (i + 1) + m) W  for m in 0..15.
  ```
  Entry from `pc+0x9c8` (post-p=0-round-15) to `pc+0xc8` is
  two ARM steps (sub + cbnz taken). Body is a generic-`i` 16-round
  chain plus sub, using a parameterized round-k tactic with
  `ARITH_RULE` normalisation of indices of the form
  `(16*(i+1)+k)+N = 16*(i+1)+(k+N)` to align
  `SHA256_SCHEDULE_MONO` specializations with the
  post-`SHA256_W_EXTEND` goal form. Back-edge is one step
  (cbnz taken at `X30 != 0` for `0 < i < 2`), exit is one step
  (cbnz not taken at `i = 2`).

- **D-tail (rounds 48..63): 16 ROUND_NOSCHED bodies unrolled inline**,
  each concrete-index (48..63). Uses `LIST_8_COMPRESS_NOHW5`
  destructuring again (because `sha256_compress 48 W H_i` with
  concrete 48 still doesn't unfold past the definition's step case
  without 48 repetitions of the `n+1` unfolder). No schedule step;
  closure is just 2 `CONV_TAC WORD_RULE` conjuncts per round (T1+T2
  and d+T1).

The proof file grew from ~300 lines of early scaffolding to ~5800
lines overall: approximately 2000 lines of inline period-0 rounds,
1800 lines of WHILE_UP for periods 1-2, 1400 lines of D-tail, and
~600 lines of Phase A/C/E/F and helper-lemma setup.

Both `SHA256_BLOCK_DATA_ORDER_NOHW5_CORRECT` and
`SHA256_BLOCK_DATA_ORDER_NOHW5_SUBROUTINE_CORRECT` close without
`CHEAT_TAC`. `check_axioms()` on a fresh session reports three
axioms total (the three standard HOL-Light axioms; no additional
axioms from this proof).

### Artefacts (nohw5)

| Path                                                       | Purpose                                  |
|------------------------------------------------------------|------------------------------------------|
| `arm/sha2/sha256_block_data_order_nohw5.S`                 | Optimised assembly                       |
| `arm/proofs/sha256_block_data_order_nohw5.ml`              | Full HOL-Light proof (~5800 lines)       |
| `include/s2n-bignum.h`                                     | C declaration                            |
| `arm/Makefile`                                             | Build integration                        |
| `benchmarks/benchmark.c`                                   | Benchmark entry                          |
| `tests/test.c`                                             | Cross-check test vs baseline + reference |

### Optimisations in `nohw6`

nohw6 is the first scalar variant aimed explicitly at *matching*
AWS-LC's hand-written `sha256_block_data_order_nohw`. It keeps all
of nohw5's fusions (shifted-register EOR, fused Maj, schedule/
compression interleaving, register-resident schedule window) and adds
two further optimisations:

1. **Cyclic state-register naming.** The logical state positions
   `a..h` live in a rotating set of eight registers (`w4..w11`). At
   round `t` with `t mod 8 = k`, logical state position `j` (0..7 for
   a..h) is held in physical register `w[4 + ((j-k) mod 8)]`. Each
   round writes only *two* registers -- new_e (into the slot that
   held d) and new_a (into the slot that held h); all other state
   positions stay in the same physical register and are merely
   re-interpreted by the next round's macro. This removes the six
   state-rotation MOVs per round (384 per block) that nohw5 executes.

   Because the rotation cycle has period 8 and each period of the
   schedule loop is 16 rounds, state returns to canonical
   `w4..w11 = a..h` at every period boundary (0, 16, 32, 48) and at
   round 64. The proof invariant shape at those boundaries is therefore
   identical to nohw5's.

2. **Intra-round schedule/compression interleaving.** The SCHED step
   (which reads `W[t+1]`, `W[t+9]`, `W[t+14]` and writes `W[t+16]`
   back to the slot that held `W[t]`) is dependency-independent of
   the compression's Maj+Sigma0 tail. The ROUND_SCHED body is
   reordered to issue the new_e `add _d, _d, T1` immediately after
   T1 is complete (so the d-slot forwarding opens up), then issue
   the sigma0/sigma1 ror/eor chain for the schedule, then the
   Maj/Sigma0 chain for T2, and finally the new_a `add _h, T1, T2`.
   This keeps both ALU pipes busy on Neoverse-V1 throughout the body.

Measured speedup: **1.61x on 1-block, 1.62x on 16-block** relative to
the `nohw` baseline; **1.05x** on top of the `nohw5`
register-resident-W variant. On the same host, AWS-LC's scalar
implementation runs at ~164 ns/block; nohw6 closes to within ~4%.

### Proof changes (nohw6)

Structural offsets change (30 instr/round instead of nohw5's 36;
total program 0xe28 bytes instead of 0x1128). The outer multi-block
`ENSURES_WHILE_UP_TAC` structure, the body preamble (ghost intros,
`H_i`, `M_i` destructure, `dptr_i` normalisation), Phase A (16 ldr
+rev), Phase C (8 state ldrs), Phase E (8 add-back pairs), Phase F
+ postamble (writeback + x1/x2 advance), and the `ARM_ADD_RETURN_STACK_TAC`
subroutine wrapper are all proved on the same pattern as nohw5.

The D-tail (16 compression-only rounds 48..63, pc+0x850..pc+0xd90)
mirrors nohw5's 16 nested ENSURES_SEQUENCE_TAC stanzas but with
per-round post-condition subscripts rotated through the cyclic-naming
map (m-th logical position at rotation k lives in
`X[4 + ((m - k) mod 8)]`). Each round closes via the same tactic
shape: `ENSURES_INIT_TAC` → K-pointer hypothesis specialization →
`ARM_STEPS_TAC (1--21)` → `ENSURES_FINAL_STATE_TAC` → compress-unfold
+ `GSYM WORD_SUBWORD_JOIN_SELF` + `LIST_8_COMPRESS_NOHW6` destructuring
+ `EL_CONV` + `WORD_ZX_INJ` + 2 `CONV_TAC WORD_RULE` conjuncts for
the new_a / new_e bridges.

The inner period loop (48 fused rounds 0..47, pc+0xc8..pc+0x850)
is handled as period 0 (16 inlined round stanzas, pc+0xc8..pc+0x848)
followed by `ENSURES_WHILE_UP_TAC` over periods 1 and 2 (with X30
as the loop counter). The BODY of the WHILE_UP is a 16-round nested
`ENSURES_SEQUENCE_TAC`/`CONJ_TAC` chain ending with the `sub x30,
x30, #1` at pc+0x848 to reach invariant(i+1). Each round within
the generic-i body uses `SHA256_W_EXTEND` at `n = 16*(i+1)+k`
combined with `SHA256_SCHEDULE_MONO` bridging at slot indices
`{n, n+1, n+9, n+14}` to close the schedule-extension conjunct;
the two state bridges (new_a, new_e) close via plain `WORD_RULE`
because the schedule slots at BODY entry already hold W values
(no M_i→W bridge is needed in the generic body, unlike period 0).

The full proof is **CHEAT-free end-to-end**. `check_axioms()`
reports **3 axioms** -- the three standard HOL Light axioms only:

```
|- ?f. ONE_ONE f /\ ~ONTO f            (* ax_INFINITY *)
|- !P x. P x ==> P ((@) P)             (* ax_SELECT *)
|- !t. (\x. t x) = t                   (* ax_ETA *)
```

### Artefacts (nohw6)

| Path                                                       | Purpose                                  |
|------------------------------------------------------------|------------------------------------------|
| `arm/sha2/sha256_block_data_order_nohw6.S`                 | Optimised assembly                       |
| `arm/proofs/sha256_block_data_order_nohw6.ml`              | Full HOL-Light proof (~5800 lines, CHEAT-free) |
| `include/s2n-bignum.h`                                     | C declaration                            |
| `arm/Makefile`                                             | Build integration                        |
| `benchmarks/benchmark.c`                                   | Benchmark entry                          |
| `tests/test.c`                                             | Cross-check test vs baseline + reference |

### Explorations that did not pan out

One intermediate variant (`nohw3`) was explored and then abandoned:
it unrolled Phase D by 8 rounds with sliding-register naming to
eliminate the 6 state-rotation MOVs per round (going from nohw2's 31
body instructions to 22). Measurements showed **no speedup over
nohw2** on Neoverse-V1, because register-to-register MOVs are handled
by the rename stage at 0 cycles, so the eliminated instructions were
never on the critical path. This confirmed that nohw2's bottleneck is
frontend bandwidth on the serial compression chain, not instruction
count, motivating the schedule/compression interleaving in nohw4.

For nohw5, a first attempt at a *full* ENSURES_WHILE_UP restructure
(iterating all three periods 0..2 rather than keeping period 0
unrolled) was abandoned after three compile iterations failed with
REWRITES_CONV, WORD_RULE, and MATCH_MP_TAC errors in the entry,
body, and back-edge subgoals respectively. The smaller Option B
design -- WHILE over just periods 1 and 2, with the existing
period-0 inline proof preserved -- succeeded on the first complete
compile and was adopted.

For nohw6, an early design variant kept Phase A loads *interleaved*
with the first 16 rounds (each round would `ldr wT, [x1, #off]` +
`rev wT, wT` before running a compression-only body, saving 1-2 ns
of Phase A warm-up latency). This was abandoned for two reasons:

1. The round body's `w1` scratch aliases with `x1` (the data pointer),
   so the first round body would destroy the x1 value before the next
   round could load its word.

2. More fundamentally, the register-resident sliding-schedule window
   *requires* every round (including rounds 0..15) to run the SCHED
   step, because the slot that holds `W[t]` is overwritten to
   `W[t+16]` at round `t`. AWS-LC's stack-based schedule doesn't
   have this constraint (new slots are written to different stack
   offsets). Skipping SCHED in rounds 0..15 produced visibly wrong
   output.

   A safe-scratch workaround (replacing `w1` with `w30` for
   rounds 0..15) benchmarked at 168 ns/block but was ruled out by
   the second constraint.

## Artefacts (baseline nohw)

| Path                                                       | Purpose                          |
|------------------------------------------------------------|----------------------------------|
| `arm/sha2/sha256_block_data_order_nohw.S`                  | Assembly (181 lines, 456 bytes)  |
| `arm/proofs/sha256_block_data_order_nohw.ml`               | Full HOL-Light proof (879 lines) |
| `arm/proofs/sha256_block_scalar.ml`                        | Step 4 single-block proof        |
| `arm/proofs/sha256_schedule_scalar.ml`                     | Step 3 message-schedule proof    |
| `arm/proofs/sha256_core_scalar.ml`                         | Step 2 compression-loop proof    |
| `arm/proofs/sha256_1round_scalar.ml`                       | Step 1 single-round proof        |
| `include/s2n-bignum.h`                                     | C declaration                    |
| `arm/Makefile`                                             | Build integration                |
| `benchmarks/benchmark.c`                                   | Benchmark entry                  |

Commits on branch `sha256-arm-scalar`:

- Step-by-step proof construction: `Step 1 ..` through `Step 5 COMPLETE`
  (see `git log --oneline arm/proofs/sha256_*.ml`).
- Baseline and nohw2:
  - `6703f505` Step 5 COMPLETE: SHA-256 multi-block scalar function
    proved end-to-end.
  - `7ceca4fc` Export `sha256_block_data_order_nohw` and add to
    benchmark suite.
  - `2eeafe4e` Add sha256_block_data_order_nohw2: 1.13x-faster scalar
    SHA-256.
- nohw4:
  - `bc869fc5` Add sha256_block_data_order_nohw4 (WIP proof with CHEAT_TAC).
  - `2f1e449e` sha256_block_data_order_nohw4: complete fused-loop body proof.
- nohw5 (on branch `sha256-arm-scalar-opt`):
  - Early commits through `9a58e3ac` prove Phase A/C/E/F + period p=0
    rounds 0..15 inline (WIP with CHEAT_TAC for periods 1-2 and D-tail).
  - `62b541c2` nohw5: add `LIST_8_COMPRESS_NOHW5` helper lemma for
    WHILE restructure.
  - `151b396b` nohw5: prove D-tail (16 ROUND_NOSCHED at
    pc+0x9d0..pc+0x1090). Reduces axioms from 7 to 4.
  - `bfdec6ac` nohw5: prove periods p=1, p=2 via ENSURES_WHILE_UP_TAC.
    Reduces axioms from 4 to 3 (the three standard HOL axioms only);
    the nohw5 proof is now fully CHEAT-free against FIPS 180-4.
- nohw6 (on branch `sha256-arm-scalar-opt`):
  - Early commits through `66300833` prove Phase A/C/E/F + D-tail
    (WIP with CHEAT_TAC for period loop).
  - `7d21b90b..b2c0183e` prove period 0 rounds 0..15 inline
    (pc+0xc8..pc+0x848).
  - `0165b8f5` install `ENSURES_WHILE_UP_TAC` skeleton for periods
    1, 2 with k!=0, ENTRY (sub+cbnz), BACK-EDGE, EXIT proved; BODY
    still CHEAT. Axioms remain at 4.
  - `77fdb14c` prove BODY round 0 (generic-i, canonical rotation k=0,
    pc+0xc8..pc+0x140).
  - `07db854d` prove BODY round 1 (generic-i, rotation k=1,
    pc+0x140..pc+0x1b8); validates the ARITH_RULE normalization
    pattern for the SCHEDULE_MONO bridge at round indices k>=1.
  - `f4cd8eb7` prove BODY rounds 2..15 + `sub x30, x30, #1` at
    pc+0x848. Final closure normalizes
    `16*(i+1)+16 = 16*((i+1)+1)`, `64*(i+1)+64 = 64*((i+1)+1)`,
    and `2-i = (2-(i+1))+1` to match invariant(i+1). Reduces axioms
    from 4 to 3; the nohw6 proof is now fully CHEAT-free against
    FIPS 180-4.
