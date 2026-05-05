# SHA-512 ARM HW Verification — Phase 1 Plan

Scope: **Phase 1 only** (`sha512_block_data_order_hw`, using ARMv8.2
FEAT_SHA512). Phase 2 (`sha512_block_data_order_nohw`, scalar) is out of
scope for this session and will be started separately.

## ISA-coverage check — PASS (no stop needed)

All four SHA-512 intrinsics are already modelled in s2n-bignum:

| Layer | Artifact | Location |
|---|---|---|
| Semantics | `sha512h`, `sha512h2`, `sha512su0`, `sha512su1` | `arm/proofs/sha512.ml:41-217` |
| Step functions | `arm_SHA512H`, `arm_SHA512H2`, `arm_SHA512SU0`, `arm_SHA512SU1` | `arm/proofs/instruction.ml:2920-2953` |
| Decoder | bit patterns | `arm/proofs/decode.ml:776-790` |
| Simulator iclasses | mnemonic bit masks | `arm/proofs/simulator_iclasses.ml:270-280` |
| Byte-reverse (for msg-word load) | `arm_REV64_VEC` with `esize=8` | `arm/proofs/instruction.ml:1494` |

Assembler: the toolchain already assembles with
`as -march=armv8.2-a+sha3` (arm/Makefile:52,56,60,63), which accepts the
native mnemonics `sha512h`, `sha512h2`, `sha512su0`, `sha512su1`, and
`rev64 Vd.16b, Vn.16b`. Verified independently by assembling a
test snippet. No `.inst 0x...` raw encoding needed — we will emit the
mnemonics directly.

## Branch & working tree

On branch `sha512-arm-hw`, clean working tree. All work stays on this
branch; commits after each milestone with `CHEAT_TAC` placeholders for
subgoals not yet closed so every commit loads cleanly. `check_axioms()`
is the pass criterion for "CHEAT-free".

## Key SHA-256-vs-SHA-512 register-packing difference

SHA-256 HW: state (8 × int32) packs into **two** Q registers (Q0=ABCD,
Q1=EFGH), **four** 32-bit lanes per Q. Each SHA256H/H2 does **4 rounds**
on that pair. 16-word schedule packs into Q4-Q7 (4 words each).

SHA-512 HW: state (8 × int64) packs into **four** Q registers, **two**
64-bit halves per Q. Following aws-lc's layout:

- `v0 = {a, b}`, `v1 = {c, d}`, `v2 = {e, f}`, `v3 = {g, h}`
  (top 64-bit half holds the "earlier" letter; note aws-lc's asm uses
  ARM's `word_join hi lo` convention where the higher-index half is `hi`)
- Each SHA512H/H2 kernel does **2 rounds**
- Before each SHA512H the asm builds `v5 = ext(v_x, v_y, #8)` to obtain
  the `{f, g}` and `{d, e}` pairs the 2-round recurrence needs
- Schedule packs into v16..v23 (2 × 64-bit words each = 8 Q regs for
  16-word block)
- 80 total rounds / 2 per SHA512H = **40 round groups**

All bridging lemmas reflect this 2-halves-per-Q packing; the existing
`word_join : int64 -> int64 -> int128` suffices (no `word_join4`
equivalent needed). Unpacking uses `word_subword x (0, 64)` /
`word_subword x (64, 64)`.

## Rotation amounts (from FIPS 180-4)

- `Sigma0(x) = ROR 28 x ⊕ ROR 34 x ⊕ ROR 39 x`
- `Sigma1(x) = ROR 14 x ⊕ ROR 18 x ⊕ ROR 41 x`
- `sigma0(x) = ROR  1 x ⊕ ROR  8 x ⊕ SHR  7 x`
- `sigma1(x) = ROR 19 x ⊕ ROR 61 x ⊕ SHR  6 x`

Cross-checked against `sha512.ml` — the `sha512su0` pseudocode uses
`ROR 1, ROR 8, '0000000':W<127:71>` (i.e. the shift-right-by-7 zero-pad
form), and `sha512su1` uses `ROR 19, ROR 61, '000000':X<127:70>` (shift
by 6). Both match.

## Phase-by-phase deliverables

### Phase A — Spec   `arm/proofs/utils/sha512_spec.ml`

Mirrors `sha256_spec.ml` structure. Everything 64-bit:

- `sha512_K : int64 list`  — 80 constants (FIPS 180-4 §4.2.3). Values
  can be copied from `aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/sha512-armv8.S`
  lines 1019-1058 (the `.LK512` table).
- `sha512_H0 : int64 list` — 8 initial hash words (FIPS 180-4 §5.3.5).
- `sha512_Ch`, `sha512_Maj` — same shape as SHA-256 versions, typed at
  `int64`.
- `sha512_Sigma0`, `sha512_Sigma1`, `sha512_sigma0`, `sha512_sigma1` —
  per the rotation amounts above.
- `sha512_extend_schedule`, `sha512_message_schedule n M`  — at `n=64`
  produces all 80 words.
- `sha512_compress_round : int64 -> int64 -> int64 list -> int64 list`,
  `sha512_compress n W state`.
- `sha512_block M H`, `sha512_hash_blocks n blocks H`.

**Validation before moving on**: in a holctl session, compute
`sha512_hash_blocks 1 [padded_abc_block] sha512_H0` via numeric
evaluation and check it equals the NIST "abc" digest:

```
DDAF35A193617ABA CC417349AE204131 12E6FA4E89A97EA2 0A9EEEE64B55D39A
2192992A274FC1A8 36BA3C23A3FEEBBD 454D4423643CE80E 2A9AC94FA54CA49F
```

First spec-side lemmas (must prove immediately, analogous to the
SHA-256 side):

- `LENGTH_SHA512_K: LENGTH sha512_K = 80`
- `LENGTH_SHA512_H0: LENGTH sha512_H0 = 8`
- `LENGTH_SHA512_COMPRESS: !state W i. LENGTH state = 8 ==>
  LENGTH(sha512_compress i W state) = 8`
- `LENGTH_SHA512_BLOCK`, `LENGTH_SHA512_HASH_BLOCKS`.

### Phase B — Bridging   `arm/proofs/utils/sha512_bridge.ml`

The hardest phase. Each intrinsic operates on a 128-bit Q holding
`word_join (hi:int64) (lo:int64)`, and the ARM pseudocode in `sha512.ml`
uses `word_subword y (0,64)` and `word_subword y (64,64)` to extract
halves.

Core lemmas:

- Packing helpers:
  - `WORD_JOIN_HI_LO_SUBWORD`:
    `word_subword (word_join (hi:int64) (lo:int64) : int128) (0,64) = lo /\
     word_subword (word_join hi lo : int128) (64,64) = hi`
  - `WORD_JOIN_INJ`: injective pair equality.
- Equivalence with any existing ARM spec-side definitions
  (there are no `sha_choose`-analogue helpers in sha512.ml, so no
  equivalence to prove — the round-body arithmetic appears only
  inline in `sha512h`/`sha512h2`).
- `SHA512H_BRIDGE`: given two packed hash halves and a
  packed-pair `word_join kw1 kw0` of pre-added K+W, one invocation of
  `sha512h` produces the packed `{g', h'}` of the new state after
  2 rounds of `sha512_compress_round`. Form:

  ```
  SHA512H_BRIDGE:
    !a b c d e f g h kw0 kw1.
      let s0 = [a;b;c;d;e;f;g;h] in
      let s1 = sha512_compress_round kw0 (word 0) s0 in
      let s2 = sha512_compress_round kw1 (word 0) s1 in
      sha512h (word_join (word_add g kw1) (word_add h kw0))   (* d argument, pre-add *)
              (ext-assembled {f, g} pair)                      (* n argument *)
              (ext-assembled {d, e} pair)                      (* m argument *)
      = word_join (EL 6 s2) (EL 7 s2)
  ```

  Expanding `sha512h` via BITBLAST and `WORD_ADD_COMM_ASSOC` normalisation
  (same pattern as `SHA256H_BRIDGE`) should close it.

- `SHA512H2_BRIDGE`: produces packed `{a', b'}`. Uses the kernel pattern
  from lines 85-129 of sha512.ml.
- `SHA512SU_BRIDGE`: given 4 packed pairs from the current 16-word
  schedule state, one `sha512su0` + `sha512su1` combo produces the
  packed pair `{w_i+16, w_i+17}` of the next two schedule words. Maps
  to the FIPS `sigma0`/`sigma1`/add recurrence.

All three bridges are proved by `BITBLAST_THEN` + rewrite with
`WORD_ADD_COMM_ASSOC` to reorder operand chains, mirroring the SHA-256
bridge proofs.

### Phase C — Minimal HW core   `arm/sha2/sha512_2rounds_reg.S` + `arm/proofs/sha512_2rounds_reg.ml`

Smallest meaningful kernel: a few instructions that perform exactly one
SHA512H/SHA512H2 pair (= 2 rounds), register-only. This validates the
bridge lemmas end-to-end before we scale up.

Assembly sketch (native mnemonics; exact register choices match aws-lc):

```
sha512_2rounds_reg:
    ext      v5.16b, v2.16b, v3.16b, #8     // v5 = {f, g}
    ext      v6.16b, v1.16b, v2.16b, #8     // v6 = {d, e}
    sha512h  q3, q5, v6.2d
    add      v4.2d, v1.2d, v3.2d            // {a,b} + {g',h'} -> {c',d'}
    sha512h2 q3, q1, v0.2d                  // -> {a', b'}  (d = v3)
    ret
```

Ensures-arm goal shape (in the proof file):

```
ensures arm
 (\s. aligned_bytes_loaded s (word pc) sha512_2rounds_reg_mc /\
      read PC s = word pc /\
      read Q0 s = word_join b a /\
      read Q1 s = word_join d c /\
      read Q2 s = word_join f e /\
      read Q3 s = word_join (word_add h kw0) (word_add g kw1))
      (* pre-added T1-input; the caller is expected to pre-add kw *)
 (\s. read PC s = word(pc + <exit offset>) /\
      let s0 = [a;b;c;d;e;f;g;h] in
      let s1 = sha512_compress_round kw0 (word 0) s0 in
      let s2 = sha512_compress_round kw1 (word 0) s1 in
      (* after the kernel Q_new_AB = word_join (EL 1 s2) (EL 0 s2),
         Q_new_CD = word_join (EL 3 s2) (EL 2 s2), etc. *))
 (MAYCHANGE [PC; Q3; Q4; Q5; Q6] ,, MAYCHANGE [events])
```

If this closes cleanly we know SHA512H_BRIDGE and SHA512H2_BRIDGE are
correct. Expected proof size: ~100 lines, cut-point-free (straight-line
code).

### Phase D — Full HW core, register-only   `arm/sha2/sha512_block_core.S` + `arm/proofs/sha512_block_core.ml`

Compose 40 round groups (entire 80-round compression) into a
register-only function. Input: state in Q0-Q3, 16 schedule words in
Q16-Q23 (pre-byte-swapped), K table pointer in X3. Output: updated state
in Q0-Q3.

Structure mirrors `sha256_block_core.ml`:

- `GROUP_BRIDGE_H.(i)`, `GROUP_BRIDGE_H2.(i)` for `i = 0..39` (40 of
  each, generated by `Array.init 40 mk_group_bridge_h{,2}`). Each lifts
  `SHA512H_BRIDGE` / `SHA512H2_BRIDGE` from 2 rounds to "round group i
  of compress".
- `EL_W_ALL_LIST`: EL n (sha512_message_schedule 64 M) for n=0..79.
  The first 16 come from `SHA512_SCHEDULE_PREFIX` (same shape as SHA-256
  prefix lemma, substituting 80 for 48), the remaining 64 from the
  sigma-recurrence via a SHA512_W_EXTEND analogue.
- `CUT_POINT_TAC i sname`: after each round group, replace the 4 state
  Q registers with the `sha512_compress (2*(i+1)) W H`-based
  `word_join` form.  Because SHA-512 has 4 state Q registers (vs
  SHA-256's 2), the tactic asserts 4 subgoals per cut instead of 2.
- `POSTCOND_TAC`: connect `sha512_compress 80` to `sha512_block`, same
  pattern as SHA-256.

Expected output: theorem `SHA512_BLOCK_CORE_CORRECT` proving the core
is equivalent to `sha512_block M H`.

### Phase E — Memory wrapper (fold into F)

In the SHA-256 pilot, Phase E (`sha256_block_simple`) existed as a
separate artifact during development but was **deleted** from the final
tree (the intermediate files are only in git history). To avoid
repeating that churn, we skip a standalone `sha512_block_simple.ml` and
roll memory I/O directly into Phase F.

### Phase F — Multi-block loop   `arm/sha2/sha512_block_data_order_hw.S` + `arm/proofs/sha512_block_data_order_hw.ml`

Direct parallel of `sha256_block_data_order_hw.ml`.

Asm structure (our own, not aws-lc's software-pipelined version, because
the pipelining makes the proof much harder and we've committed to
following the SHA-256-hw pilot's straight layout):

```
sha512_block_data_order_hw:
    CFI_START
    // Load state (4 Q regs)
    ldr     q0, [x0]
    ldr     q1, [x0, #16]
    ldr     q2, [x0, #32]
    ldr     q3, [x0, #48]
Lsha512_block_data_order_hw_loop:
    // Load 8 schedule Qs (128 bytes), advance X1
    ldr     q16, [x1]
    ldr     q17, [x1, #16]
    ...
    ldr     q23, [x1, #112]
    add     x1, x1, #128
    sub     x2, x2, #1
    // REV64 byte-swap (v8.0 of SHA-2 uses big-endian words)
    rev64   v16.16b, v16.16b
    ...
    rev64   v23.16b, v23.16b
    // Save state for add-back
    mov     v28.16b, v0.16b
    mov     v29.16b, v1.16b
    mov     v30.16b, v2.16b
    mov     v31.16b, v3.16b
    // 40 round groups: each group follows the 2-round kernel pattern
    // with SHA512SU0 + SHA512SU1 for groups 0..31; last 8 groups drop
    // schedule update.
    ...
    // Add back initial state (4 reg-reg adds)
    add     v0.2d, v0.2d, v28.2d
    add     v1.2d, v1.2d, v29.2d
    add     v2.2d, v2.2d, v30.2d
    add     v3.2d, v3.2d, v31.2d
    cbnz    x2, Lsha512_block_data_order_hw_loop
    str     q0, [x0]
    str     q1, [x0, #16]
    str     q2, [x0, #32]
    str     q3, [x0, #48]
    CFI_RET
```

(One open question for exact register allocation: SHA-512 has 32 SIMD
registers; we may need to stagger the 4-save registers vs. the 8
schedule registers to avoid clashes with the H/H2 working regs. Will
nail down when writing the asm.)

Proof structure:
- `ENSURES_WHILE_UP_TAC num_blocks pc_top pc_back invariant`
- Loop invariant tracks:
  - `sha512_hash_blocks i blocks [a;..;h]` packed across Q0-Q3
  - X1 = `data_ptr + 128 * i`, X2 = `num_blocks - i`, X0/X3 unchanged
  - quantified data memory (unchanged across iterations):
    `!j. j < num_blocks ==>
      read (memory :> bytes128 (word_add data_ptr (word (128*j + 16*l)))) s =
      word_join (word_bytereverse (EL (2*l+1) (EL j blocks)))
                (word_bytereverse (EL (2*l) (EL j blocks)))`
    for `l = 0..7`
  - quantified K-table memory (40 × int128 = 640 bytes):
    `!k. k < 40 ==>
      read (memory :> bytes128 (word_add kptr (word (16*k)))) s =
      word_join (EL (2*k+1) sha512_K) (EL (2*k) sha512_K)`
  - state memory unchanged
- 4 subgoals from `ENSURES_WHILE_UP_TAC`:
  - Init (4 ARM steps — LDR Q0-Q3)
  - Body (full block computation, ~200+ steps with cut-points after
    each round group — longer than SHA-256 hw's 118 steps because 40
    groups × 5-7 instr each + setup/teardown)
  - Back-edge (1 step — CBNZ)
  - Exit (5 steps — CBNZ fall-through + 4 STR Qs)
- `REV64_BITBLAST_TAC` analogue of SHA-256's `REV32_BITBLAST_TAC`:
  `word_bytereverse o word_bytereverse = id` at the 64-bit half level.
- `EXPAND_K_TAC` specializes K at 40 concrete values (not 16 like
  SHA-256).
- `EXPAND_DATA_TAC` specializes data memory at the current block index.

Subroutine wrapper: the chosen asm sketch uses no stack prologue (no
`stp`, no `sub sp` — CFI_START/CFI_RET just emit CFI pseudo-ops, no
stack traffic). So `ARM_ADD_RETURN_NOSTACK_TAC` suffices, same as
SHA-256 hw. If we later discover a stack requirement, we switch to
`ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(..., ...)`.

## Tests & benchmark

- `tests/test.c`: add a SHA-512 test case mirroring the SHA-256 entry:
  - NIST "abc" KAT:
    `abc -> DDAF35A193617ABA CC417349AE204131 12E6FA4E89A97EA2 0A9EEEE64B55D39A
            2192992A274FC1A8 36BA3C23A3FEEBBD 454D4423643CE80E 2A9AC94FA54CA49F`
  - 100+ random single-block cross-checks vs OpenSSL `SHA512_Transform`
  - 10+ random multi-block cross-checks (1..16 blocks).
- `benchmarks/benchmark.c`: add a SHA-512 hw benchmark entry.

## Commit discipline & budget

Commits after every milestone:
1. Phase A spec file + LENGTH lemmas + KAT validation in interactive
   session
2. Phase B bridging lemmas
3. Phase C register kernel
4. Phase D partial (first 10 round groups) with CHEAT_TAC for rest
5. Phase D complete (40 groups + add-back)
6. Phase F with CHEAT_TAC body
7. Phase F body complete
8. Phase F end-to-end (all subgoals closed)
9. Phase F subroutine theorem + CI integration (Makefile, include
   header, collect-signatures)
10. tests/benchmarks

`check_axioms()` is the pass criterion for "CHEAT-free". Progress notes
written to memory after each significant session and whenever hitting
a blocker, with the format from the SHA-256 pilot (specific blockers,
specific next steps).

Budget expectation: comparable to SHA-256 hw pilot, possibly slightly
more due to 40 groups vs 16. The 2-halves-per-Q packing is the main new
bridging obstacle; after that the infrastructure is structurally
identical.
