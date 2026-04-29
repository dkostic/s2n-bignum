# SHA-256 Scalar (no-HW) Verification Report

## Overview

This report summarises the formal verification of
**`sha256_block_data_order_nohw`** -- a multi-block ARM64 SHA-256
implementation that uses *only* base integer instructions (no SHA-256
crypto extensions, no NEON). It is the scalar complement to
`sha256_block_data_order_hw` (verified in the SHA-256 pilot;
see `pilot-report.md`) and can be linked into the same
`libs2nbignum.a`.

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

Both top-level theorems load without `CHEAT_TAC` on top of the existing
s2n-bignum ARM infrastructure:

```
needs "arm/proofs/sha256_block_data_order_nohw.ml";;
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

| Function                                         | 1 block | 16 blocks |
|--------------------------------------------------|---------|-----------|
| `sha256_block_data_order_hw` (SHA-256 extension) | 38 ns   | 575 ns    |
| `sha256_block_data_order_nohw` (baseline scalar) | 275 ns  | 4395 ns   |
| `sha256_block_data_order_nohw2` (optimised)      | 242 ns  | 3884 ns   |

The baseline scalar variant is intentionally written for
verifiability rather than peak throughput: a single round per loop
iteration, no manual software pipelining, no
message-schedule / compression interleaving.

The `nohw2` variant is a drop-in replacement with the same ABI and
loop structure; the measured speedup is **1.13x** on both 1-block
and 16-block workloads. Its proof
(`arm/proofs/sha256_block_data_order_nohw2.ml`) is a direct port of
the baseline proof with three targeted edits.

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

### Proof changes

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

## Artefacts

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
- Final two commits:
  - `6703f505` Step 5 COMPLETE: SHA-256 multi-block scalar function
    proved end-to-end.
  - `7ceca4fc` Export `sha256_block_data_order_nohw` and add to
    benchmark suite.
