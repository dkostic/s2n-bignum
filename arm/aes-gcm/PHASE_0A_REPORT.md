# Phase 0a — Disassembly Gap Survey of the AES-128 fork of `aes_gcm_enc_kernel`

## Purpose

This report is the deliverable of Phase 0a of the AES-GCM ARM
verification project (see `~/whole-proofs/orchestrator/state/STATE.md`).
It catalogues the gap (if any) between the AES-128-only fork of
aws-lc's `aes_gcm_enc_kernel` and the s2n-bignum ARM ISA model on the
current branch (`aes-gcm-arm`).

The report is the input that sizes Phase 0b (ISA model additions) and
Phase 0c (cosim gate).

## TL;DR

The AES-128 fork uses **613 instructions** drawn from **32 distinct
mnemonics**. Of these, **30 mnemonics are decoded correctly** by the
current s2n-bignum decoder; **2 are not**:

1. **`MOV <V><d>, <Vn>.D[1]`** (alias of `DUP scalar from element`,
   D-form) — 6 distinct register-pair encodings, 14 occurrences.
2. **`SHL <V><d>, <V><n>, #imm`** (`SHL scalar by immediate`, D-form)
   — 1 distinct encoding (`shl d8, d8, #56`), 4 occurrences.

Total decoder rejections: **18 instructions** (≈ 3 % of the kernel).

Phase 0b should add the two decoder rows plus, if needed, the
matching `arm_*_GEN`/`arm_*_VEC` semantics. Phase 0c will then need
two new bit-pattern rows in `arm/proofs/simulator_iclasses.ml` for
cosim coverage.

## Method

The fork `arm/aes-gcm/aes_gcm_enc_kernel_aes128.S` was generated from
the verbatim aws-lc source `arm/aes-gcm/aes_gcm.S` by statically
removing the AES-192/256 dispatch cascades and the entire decrypt
kernel. See "AES-128 fork surgery" below for the precise line ranges.

The fork was built to `aes_gcm_enc_kernel_aes128.o` via
`arm/aes-gcm/Makefile` (native `as` on aarch64). For each instruction
emitted by `aarch64-linux-gnu-objdump -d`, the 32-bit opcode word was
fed to the s2n-bignum decoder via

```ocaml
let tm = mk_comb (`decode`, mk_comb (`word:num->32 word`,
                                     mk_small_numeral opcode)) in
DECODE_CONV tm
```

(equivalent to what `define_assert_from_elf` does internally per
instruction). The probe was run against the `simrt` `holctl` server
(s2n-arm checkpoint, base.ml loaded). Results were classified as
`OK` (decoder returned `SOME ast`), `NONE` (decoder returned
`NONE`), or `FAIL` (decoder raised `PURE_DECODE_CONV: decode (word
N)`). All 18 non-OK cases were `FAIL`s; no `NONE`s were observed.

A spot-check exemplar per mnemonic was also cross-checked against
the aws-lc comments to confirm each decoded AST matches what the
mnemonic claims. The full per-mnemonic exemplar table is in §
"Decoded AST cross-check" below.

## AES-128 fork surgery (deleted aws-lc line ranges)

Ranges below refer to 1-indexed line numbers in the unmodified
`aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/aesv8-gcm-armv8.S`
(1519 lines total). All deletions are wholesale (no partial-line
edits inside the AES-128 path).

| Cascade / region | aws-lc lines | Description |
|---|---|---|
| A — `cmp` before first cascade | 124 | `cmp x17, #12` setting flags for AES-128/192/256 dispatch |
| A — branches + dead AES-192/256 rounds | 163-199 | `b.lt .Lenc_finish_first_blocks` + 16 dead AES-192 `aese/aesmc` (rounds 9-10 across blocks 0-3) + `b.eq .Lenc_finish_first_blocks` + 16 dead AES-256 `aese/aesmc` (rounds 11-12) |
| B — `cmp` before second cascade | 378 | identical `cmp x17, #12` inside `.Lenc_main_loop` |
| B — branches + dead AES-192/256 rounds | 381-417 | structure identical to cascade A, leading into `.Lenc_main_loop_continue` |
| C — `cmp` before third cascade | 585 | identical `cmp x17, #12` inside `.Lenc_prepretail` |
| C — branches + dead AES-192/256 rounds | 597-633 | structure identical to cascade A, leading into `.Lenc_finish_prepretail` |
| Decrypt kernel (entire) | 768-1517 | `aes_gcm_dec_kernel` (out of scope per BRIEF.md) |

Total deleted: 864 source lines. Fork size: 671 lines (vs. 1519 in
the original — banner + Makefile-style header overhead accounts for
the difference between (1519 − 864) = 655 raw kept and 671 emitted).

The AES-128 path itself was not touched: an `objdump -d` diff (kept
in the commit message of `c4a41bc5`) shows three deletions of the
exact pattern `cmp x17, #0xc ; b.lt <Lenc_*> ; <16 aese/aesmc> ;
b.eq <Lenc_*> ; <16 aese/aesmc>`, plus shifted branch-target offsets
where the shorter path renumbers PCs. No instructions in the AES-128
flow were edited, added, or reordered.

## Instruction inventory

The 613-instruction AES-128 fork uses these mnemonics (counts from
`aarch64-linux-gnu-objdump -d`):

| Count | Mnemonic | Decoded | Decoder AST (representative) |
|------:|----------|---------|------------------------------|
| 120 | `aese` | OK | `arm_AESE Q<d> Q<n>` |
| 108 | `aesmc` | OK | `arm_AESMC Q<d> Q<n>` |
| 101 | `eor` | OK | `arm_EOR_VEC Q<d> Q<n> Q<m> 128` (and `arm_EOR W*` for scalar) |
| 46 | `fmov` | OK | `arm_FMOV_ItoF Q<d> X<n> <lane>` (and `arm_FMOV_FtoI` for the reverse direction) |
| 27 | `pmull` | OK | `arm_PMULL_VEC Q<d> Q<n> Q<m> 64` |
| 26 | `mov` | **MIXED** | `arm_MOV X<d> X<n>` for GPR moves (OK) **vs** scalar lane-extract `mov d<d>, v<n>.d[1]` **(FAIL)** |
| 22 | `ldp` | OK | `arm_LDP X<d1> X<d2> X<base> (Immediate_Offset (iword (&n)))` |
| 18 | `ldr` | OK | `arm_LDR Q<d>/W<d>/X<d> X<base> (Immediate_Offset (word n))` |
| 17 | `add` | OK | `arm_ADD X<d> X<n> (Shiftedreg X<m> LSL k)` (and friends) |
| 15 | `pmull2` | OK | `arm_PMULL2_VEC Q<d> Q<n> Q<m> 64` |
| 14 | `rev64` | OK | `arm_REV64_VEC Q<d> Q<n> 8` |
| 13 | `rev` | OK | `arm_REV W<d> W<n>` |
| 13 | `st1` | OK | `arm_STR Q<d> X<base> (Postimmediate_Offset (word k))` (alias) |
| 12 | `orr` | OK | `arm_ORR W<d> W<n> W<m>` and shifted-reg variants |
| 11 | `ext` | OK | `arm_EXT Q<d> Q<n> Q<m> <pos>` |
| 9 | `movi` | OK | `arm_MOVI D<d> (word k)` (and Q-variant) |
| 8 | `stp` | OK | `arm_STP …` (Pre/Immediate/Postimmediate offsets) |
| 6 | `cmp` | OK | `arm_CMP X<n> X<m>` (and immediate variant) |
| 5 | `sub` | OK | `arm_SUB X<d> X<n> (rvalue (word k))` |
| 4 | `shl` | **FAIL** | scalar D-form: `shl d<d>, d<n>, #<imm>` — see Gap 2 |
| 3 | `b.gt` | OK | `arm_BGT (word offset)` |
| 2 | `lsr` | OK | `arm_LSR X<d> X<n> <shift>` |
| 2 | `ld1` | OK | decoded as `arm_LDR Q<d> X<base> No_Offset` (alias is fine) |
| 2 | `trn2` | OK | `arm_TRN2 Q<d> Q<n> Q<m> 64 128` |
| 2 | `trn1` | OK | `arm_TRN1 Q<d> Q<n> Q<m> 64 128` |
| 2 | `b.ge` | OK | `arm_BGE (word offset)` |
| 1 | `ldur` | OK | decoded as `arm_LDR Q<d> X<base> (Immediate_Offset (word k))` (alias is fine) |
| 1 | `and` | OK | `arm_AND X<d> X<n> (rvalue (word k))` |
| 1 | `b.lt` | OK | `arm_BLT (word offset)` (loop back-edge `b.lt .Lenc_main_loop`) |
| 1 | `b` | OK | `arm_B (word offset)` |
| 1 | `str` | OK | `arm_STR W<d> X<base> (Immediate_Offset (word k))` |
| 1 | `ret` | OK | `arm_RET X30` |

## Gaps

### Gap 1: `MOV <V><d>, <Vn>.D[1]` (scalar lane-extract, D-form)

This is an alias of the ARMv8 instruction "DUP scalar from element"
(C7.2.30 in the ARM ARM, encoding **`AdvSIMD_dup_element`** with
`scalar=1`). The encoding is

```
01011110 imm5 0 00001 Rn Rd            (bits 31:21 = 01011110000)
```

Concretely all 14 occurrences in the fork have `imm5 = 0b11000` (i.e.
size = 64-bit, index = 1), so they all extract `<Vn>.d[1]` into the
scalar D register `<Vd>`. Note that lane-extracting `<Vn>.d[0]` would
have `imm5 = 0b01000` and would also be rejected — same row.

**Status of underlying semantics.** s2n-bignum already defines
`arm_DUP_GEN` (`arm/proofs/instruction.ml:1190`) but it sources from a
**general-purpose register** (`XREG'`/`WREG'`), not a vector lane. We
need either:

- a new combinator `arm_DUP_GEN_FROM_ELEM Rd Rn esize datasize index`
  that reads `Rn:128 word`, extracts the `index`-th element of size
  `esize`, and broadcasts/stores into `Rd`; OR
- a tighter combinator `arm_MOV_VEC_LANE_TO_SCALAR Rd Rn esize index`
  for the special case `datasize=64, scalar=1` (the only form this
  kernel uses).

A single combinator covers both cases since `mov d<d>, v<n>.d[idx]`
is the `datasize=64, esize=64, scalar=1` slice of DUP-from-element.

**Decoder rows that need to be added** (in `arm/proofs/decode.ml`,
near the existing `DUP (general)` row at line 533):

```ocaml
| [01:2; 0b011110:6; imm5:5; 0b000001:6; Rn:5; Rd:5] ->
  // DUP scalar from element (alias: MOV <V><d>, <Vn>.<T>[<index>])
  let size = word_ctz imm5 in
  if size > 3 then NONE else
  let esize = 8 * 2 EXP size in
  let index = val (word_ushr imm5 (size + 1)) in
  // datasize is 64 for the scalar form
  SOME (arm_DUP_GEN_FROM_ELEM (DREG' Rd) (QREG' Rn) esize 64 index)
```

(The `(DREG' Rd)` choice mirrors the existing `(DREG' Rd)` for the
64-bit half of the `MOVI`/`SSHLL` scalar forms at decode.ml:811. The
exact API of the new `arm_DUP_GEN_FROM_ELEM` combinator is for Phase
0b to settle; this decoder snippet is illustrative.)

**Distinct opcodes seen in the fork (all `imm5=0b11000`, i.e.
`v<n>.d[1]`):**

| Opcode | Disassembly |
|---|---|
| `0x5e18062a` | `mov d10, v17.d[1]` |
| `0x5e180488` | `mov d8, v4.d[1]` |
| `0x5e1804a4` | `mov d4, v5.d[1]` |
| `0x5e1804c8` | `mov d8, v6.d[1]` |
| `0x5e1804e4` | `mov d4, v7.d[1]` |
| `0x5e180496` | `mov d22, v4.d[1]` |

Each appears between 1 and 4 times. **Total occurrences: 14.**

These are the GHASH per-block "mid 64-bit lane extract" steps that
feed into the `pmull` / `pmull2` Karatsuba reduction. Verifying the
GHASH bridge (Phase 3b) will require this combinator to commute
correctly with `word_subword … (64,64)` on the source register.

### Gap 2: `SHL <V><d>, <V><n>, #<imm>` (scalar by immediate, D-form)

This is the ARMv8 instruction "SHL — scalar by immediate" (C7.2.260
in the ARM ARM, encoding **`AdvSIMD_shf_imm_scalar`** with
`opcode=0b01010`, `op=0b1010101`). Encoding:

```
01011111 immh immb 01010 1 Rn Rd      (bits 31:23 = 010111110)
```

Specifically the only variant the fork emits is `shl d8, d8, #56`
(opcode `0x5f785508`), which is the GHASH MODULO-reduction's
`mod_constant = 0xc2 << 56` step (the ISO/IEC GHASH irreducible
polynomial constant, applied as a 56-bit left-shift of `0xc2` to
position the constant at the top byte of the 64-bit accumulator
lane).

**Status of underlying semantics.** s2n-bignum already defines
`arm_SHL_VEC` (`arm/proofs/instruction.ml:1519`); its `datasize=64`
branch already does the right thing for sub-64-bit element sizes.
But for the scalar D-form (`esize=64, datasize=64`) it is
*explicitly excluded* by the existing decoder row at decode.ml:817
(`if bit 3 immh /\ ~q then NONE`). The architectural spec for the
scalar form treats `esize=64, datasize=64, scalar=1` as a separate
encoding row (bit 30 = 1 + bit 28 = 1 instead of bit 30 = q +
bit 28 = 0 for the vector form).

**Two implementation paths:**

- (A) Reuse `arm_SHL_VEC Rd Rn amt 64 64` directly — the semantics
  match: `usimd1 (\x. word_shl x amt) n` on a 1-element 64-bit
  vector is the scalar shift. Just add a separate decoder row that
  emits this, with the source/dest registers wrapped via `DREG'`.

- (B) Add a dedicated `arm_SHL_SCALAR Rd Rn amt` combinator. Trivial
  lemma `arm_SHL_SCALAR Rd Rn amt = arm_SHL_VEC Rd Rn amt 64 64`
  bridges to existing reasoning.

**Recommendation: (A).** It re-uses an existing combinator (no new
HOL definitions, no `ARM_OPERATION_CLAUSES` registration needed),
and downstream proofs already have rewriting machinery for
`arm_SHL_VEC`. Only the decoder row is new.

**Decoder row that needs to be added** (in `arm/proofs/decode.ml`,
adjacent to the existing vector SHL row at line 814):

```ocaml
| [01:2; 0b111110:6; immh:4; immb:3; 0b010101:6; Rn:5; Rd:5] ->
  // SHL scalar by immediate (D-form only)
  if ~(bit 3 immh) then NONE  // scalar form requires esize = 64
  else
    let esize = 64 in
    let amt = val(word_join immh immb:7 word) - esize in
    SOME (arm_SHL_VEC (DREG' Rd) (DREG' Rn) amt esize 64)
```

**Distinct opcodes seen in the fork:**

| Opcode | Disassembly | Occurrences |
|---|---|---|
| `0x5f785508` | `shl d8, d8, #56` | 4 |

This is the GHASH polynomial-reduction `mod_constant` shift. Each
occurrence pairs with a subsequent `pmull v4.1q, v9.1d, v8.1d`
(Karatsuba reduction step) and `eor` chain.

## Decoded AST cross-check

For each of the 32 distinct mnemonics, the first instance was
decoded and the AST inspected. Where the AST differs in shape from
the mnemonic name (e.g. `ld1` decoded as `arm_LDR …`), the difference
is a documented decoder alias (s2n-bignum normalises certain
instruction forms into a canonical combinator). All 30 OK mnemonics
were verified to land on a sensible AST; no "decoded, but to the
wrong shape" cases were found.

The two FAIL cases (`mov d, v.d[1]` and `shl d, d, #imm`) were
already discussed above.

| Mnemonic | First-instance opcode | AST |
|---|---|---|
| `add`    | `0x8b111113` | `arm_ADD X19 X8 (Shiftedreg X17 LSL 4)` |
| `aese`   | `0x4e284a40` | `arm_AESE Q0 Q18` |
| `aesmc`  | `0x4e286800` | `arm_AESMC Q0 Q0` |
| `and`    | `0x927ae4a5` | `arm_AND X5 X5 (rvalue (word 0xffff…ffc0))` |
| `b`      | `0x14000036` | `arm_B (word 216)` |
| `b.ge`   | `0x54002c2a` | `arm_BGE (word 1412)` |
| `b.gt`   | `0x540001ec` | `arm_BGT (word 60)` |
| `b.lt`   | `0x54ffea2b` | `arm_BLT (word 2096452)` (back-edge) |
| `cmp`    | `0xeb05001f` | `arm_CMP X0 X5` |
| `eor`    | `0x6e291e31` | `arm_EOR_VEC Q17 Q17 Q9 128` |
| `ext`    | `0x6e0b416b` | `arm_EXT Q11 Q11 Q11 64` |
| `fmov`   | `0x9e670142` | `arm_FMOV_ItoF Q2 X10 0` |
| `ld1`    | `0x4c407200` | `arm_LDR Q0 X16 No_Offset` (alias) |
| `ldp`    | `0xa9403a6d` | `arm_LDP X13 X14 X19 (Immediate_Offset (iword (&0)))` |
| `ldr`    | `0xb940f111` | `arm_LDR W17 X8 (Immediate_Offset (word 240))` |
| `ldur`   | `0x3cdf027f` | `arm_LDR Q31 X19 (Immediate_Offset (word 0xffff…fff0))` (alias) |
| `lsr`    | `0xd343fc25` | `arm_LSR X5 X1 3` |
| `mov`    | `0x910003fd` | `arm_ADD X29 SP (rvalue (word 0))` (canonical encoding for `mov reg, sp`) |
| `movi`   | `0x0f06e448` | `arm_MOVI D8 (word 14033993530586874562)` (= `0xc2c2c2c2c2c2c2c2`) |
| `orr`    | `0x2a0b016b` | `arm_ORR W11 W11 W11` |
| `pmull`  | `0x0eefe08b` | `arm_PMULL_VEC Q11 Q4 Q15 64` |
| `pmull2` | `0x4eefe089` | `arm_PMULL2_VEC Q9 Q4 Q15 64` |
| `ret`    | `0xd65f03c0` | `arm_RET X30` |
| `rev`    | `0x5ac0098c` | `arm_REV W12 W12` |
| `rev64`  | `0x4e20096b` | `arm_REV64_VEC Q11 Q11 8` |
| `shl`    | `0x5f785508` | **FAIL** (Gap 2) |
| `st1`    | `0x4c9f7044` | `arm_STR Q4 X2 (Postimmediate_Offset (word 16))` (alias) |
| `stp`    | `0xa9b87bfd` | `arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &128)))` |
| `str`    | `0xb9000e09` | `arm_STR W9 X16 (Immediate_Offset (word 12))` |
| `sub`    | `0xd10004a5` | `arm_SUB X5 X5 (rvalue (word 1))` |
| `trn1`   | `0x4ecf29c9` | `arm_TRN1 Q9 Q14 Q15 64 128` |
| `trn2`   | `0x4ecf69d1` | `arm_TRN2 Q17 Q14 Q15 64 128` |

`mov` is shown as MIXED in the inventory: GPR-form moves
(`mov x<d>, x<n>`, `mov x29, sp`) decode correctly. The scalar
lane-extract form (`mov d<d>, v<n>.d[1]`) fails. The mnemonic
collides because ARM uses `mov` as the assembler alias for both;
the instructions have entirely different opcodes.

## Recommendations for Phase 0b

Phase 0b should add:

1. **One decoder row + one new combinator** for `MOV <V><d>,
   <Vn>.D[index]` (alias of `DUP_scalar_from_element` D-form). The
   combinator can be named `arm_DUP_GEN_FROM_ELEM` or similar; it
   reads from a Q register source, takes `(esize, index)` arguments,
   and writes the extracted element to a D-register destination. For
   this kernel only `(esize=64, index=1)` is exercised, but the
   row should not over-specialise — the same row decodes
   `(esize=8/16/32, index=any)` at no extra cost.

2. **One decoder row** for `SHL <V><d>, <V><n>, #imm` (D-form, scalar
   by immediate). No new combinator needed — re-use existing
   `arm_SHL_VEC Rd Rn amt 64 64` with `Rd, Rn` as `DREG'`.

3. **Two new bit-pattern strings** in
   `arm/proofs/simulator_iclasses.ml` (one per row) for cosim
   coverage in Phase 0c.

The brief's mention of `REV32 vector` and PR #406 is **not
applicable here**: the AES-128 fork uses `rev64` (already modeled,
decoded as `arm_REV64_VEC Q… Q… 8`) but never `rev32` vector.
Likewise, **`MOVI` is fully modeled**: the kernel emits `movi v8.8b,
#0xc2` (8-bit form, broadcast to D-reg) and `movi v8.8b, #0`, both
of which decode correctly to `arm_MOVI D8 (word k)`.

## Estimated Phase 0b/0c effort

- **Phase 0b**: 1 short session — both gaps are localised
  decoder additions + (for Gap 1) one new ~5-line combinator
  + ARM_OPERATION_CLAUSES wiring.
- **Phase 0c**: 1 short session — two new iclass rows, run
  `cosimulate_instructions`, gate on agreement.

Nothing here justifies multiple sessions of ISA-model work. Phase 1
(KAT gate) is reachable in 2-3 sessions from this point.

---

*Generated 2026-05-29 in session 001 (orchestrator-driven).
Re-run by re-executing the probe at `/tmp/probe_aesgcm.ml` against a
post-base.ml `holctl` server. The aws-lc source line numbers cited
are stable for the version vendored at
`aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/aesv8-gcm-armv8.S`
(1519 lines, kernel sizes 752 / 750 bytes for enc / dec
respectively).*
