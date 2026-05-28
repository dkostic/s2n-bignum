# How the MD5 x86-64 Proof Was Done

## What we proved
Five theorems in `x86/proofs/md5_block_asm_data_order.ml` (HEAD `8a0f48ab`, 18984 lines) connecting aws-lc's `md5_block_asm_data_order` to a freshly authored HOL Light spec `md5_hash_blocks num_blocks blocks initial_state`:

- `MD5_BLOCK_ASM_DATA_ORDER_CORRECT` (core ensures-form spec)
- `_NOIBT_SUBROUTINE_CORRECT` + `_SUBROUTINE_CORRECT` (SysV ABI)
- `_NOIBT_WINDOWS_SUBROUTINE_CORRECT` + `_WINDOWS_SUBROUTINE_CORRECT` (Windows ABI)

Validated end-to-end by cold-load on a fresh `s2n-x86` checkpoint, RFC 1321 KAT (`md5("") = d41d…427e`, `md5("abc") = 9001…7f72`), and a grep-clean sweep for `cheat`, `mk_thm`, `SORRY_TAC`, etc.

## Process
56 prover sessions across 7 days, dispatched by an orchestrator running prover/reviewer/advisor subagents. The work split into 13 phases:

| Phase | What landed |
|---|---|
| 1 | KAT gate, asm dropped in, byte list frozen |
| 2 | Spec (`md5_compress`, `md5_block`, `md5_hash_blocks`) |
| 3–8 | Per-step `MD5_STEP_n_CORRECT` lemmas, the four round functions |
| 9 | **Single-block body** (sessions 026–049, by far the longest phase) |
| 10 | Multi-block loop (`MD5_LOOP_CORRECT`) |
| 11 | Function entry + ABI wrapper |
| 12 | Windows ABI variant |
| 13 | Final validation + memory notes |

## What was hard

**Phase 9 absorbed 17 sessions.** The first attempt (sessions 026–029) tried let-form cut predicates with full chain values inlined — the term grew polynomially with chain length and `ENSURES_SEQUENCE_TAC` simply timed out. The pivot was to **spec-form cut predicates** using `EL i (md5_compress n W [a;b;c;d])` as the boundary representation, then incrementally compose:

- **TEST_R1** (PRELUDE+R1, session 037)
- **TEST_R1_R2** (sessions 040–041, broken open by an advisor consult that prescribed a standalone 4-conjunct bridge lemma `MD5_F_LET_TO_EL_4WAY`)
- **TEST_R1_R2_R3** (sessions 042–045, second advisor consult diagnosed the bulk-`let_CONV` polynomial blowup; the fix was interleaving `ONCE_DEPTH_CONV let_CONV` with `ABBREV_TAC` one step at a time)
- **TEST_R1_R2_R3_R4** + **FULL** (sessions 046–047)
- **`MD5_BLOCK_BODY_CORRECT`** (session 049)

**Phase 10 took 4 sessions** because the proof was first found *interactively on a live server* (`top_thm()` returns the theorem) but didn't reproduce on cold-load. Sessions 051–052 fixed three cold-vs-warm divergences (`BETA_RULE` preprocess for lambda hyps, `MAP_EVERY` over a 16-case `THENL`, and proper `FIRST_X_ASSUM` usage). Session 053 used a **marker-bisect** technique — wrap each closing tactic as `(close_tac THEN MARK "label")` and identify the failing subgoal by which marker prints (the inverted-from-intuition semantics: a printed MARK means the close didn't close). The actual bug was a missing `MULT_CLAUSES; WORD_ADD_0` in a `MAP_EVERY` rewrite list (k=0 case couldn't collapse `4*0 = 0` and `word_add x (word 0) = x`).

**Phases 11 and 12** each landed in a single session, but each required an inline GEN-style adaptation of the framework's stack-wrapper tactic (`X86_PROMOTE_RETURN_STACK_TAC` / `WINDOWS_X86_WRAP_STACK_TAC`) because MD5's epilogue has an extra `add rsp 40` between the pops and `ret` — off by one from the framework's hardcoded `epilog_len = n+1` formula.

## Lessons captured

Seven non-obvious gotchas now live in `~/.claude/projects/.../memory/feedback_md5_proof_lessons.md`:

1. **Marker semantics inversion** — `(close_tac THEN MARK)` only fires MARK if the close left residual subgoals.
2. **`MAP_EVERY` rewrite lists** over indexed memory reads need `MULT_CLAUSES; WORD_ADD_0` for the k=0 case.
3. **Bulk `DEPTH_CONV let_CONV`** is polynomial in chain length; safe ≤16 lets, OOMs at 30+. Default to interleaved `ONCE_DEPTH_CONV let_CONV + ABBREV_TAC` for long chains.
4. **Windows wrapper epilog brittleness** — `WINDOWS_X86_WRAP_STACK_TAC`'s `epilog_len = 3 + n` doesn't accommodate functions with extra `add rsp` between pops and ret; inline a GEN-style adaptation.
5. **Stack-wrapper var ordering** — match the core theorem's variable order before adding `stackpointer`/`returnaddress`.
6. **Symbolic `LENGTH`** — expand `LENGTH foo_tmc` to a literal numeral so `NONOVERLAPPING_TAC` and `READ_OVER_WRITE_ORTHOGONAL_TAC` can match assumption ranges.
7. **`holctl` `Sys.chdir`** — the `[ERROR] Bad input` is a known cosmetic false flag; the eval still runs.

## Process observations

- The orchestrator/prover/reviewer/advisor pattern worked well. **Three advisor consults** (sessions 036, 041, 044) each correctly diagnosed structural issues that the prover couldn't see from inside the iteration loop.
- **Incremental commits** were load-bearing — when sessions hit the 2.5h kill threshold mid-debug, banked commits (4 in session 047, 2 in session 044) survived even when in-flight work was lost. Stash + durable `/tmp` artifact copies preserved continuity across kills.
- **The hardest sessions were the diagnostic ones**, not the proof-construction ones. Cold-vs-warm divergence (Phase 10) and term-size pathologies (Phase 9) are not problems you can pattern-match from the SHA-256 pilot; each needed empirical bisection.

The proof is now ~26 commits ahead of `origin/main`, unpushed.
