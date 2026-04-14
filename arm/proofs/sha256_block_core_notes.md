# SHA-256 Block Core Proof - Progress Notes

## Status: Symbolic execution COMPLETE, postcondition matching TODO

## Key findings (2026-04-14)

### Proof setup works
1. `define_from_elf` loads sha256_block_core.o (109 instructions, 436 bytes)
2. `ARM_MK_EXEC_RULE` decodes all 109 instructions
3. EXPAND_CASES_CONV correctly expands `!i. i < 16 ==> ...` K table precondition
4. K values remain as `EL n sha256_K` (symbolic) - this is fine, matches spec

### Simplification pattern per round group
After each round group (7 or 5 steps):
1. `RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32])` - simplifies ADD V.4S output
2. `RULE_ASSUM_TAC(REWRITE_RULE[SHA256H_BRIDGE_flat; SHA256H2_BRIDGE_flat; SHA256_COMPRESS_ROUND_PREADD; SHA256_COMPRESS_ROUND_KW_SYM; SHA256SU_BRIDGE_flat])` - bridges hardware to spec

### Timing per step
- Steps 1-9 (saves + group 0): ~30ms each
- Steps 10-16 (group 1): ~50ms each
- Steps 17-23 (group 2): ~60-90ms each
- Steps 24-30 (group 3): ~130ms-900ms (growing)
- Groups 4-7: in progress (expected slower)

### Term structure after bridging
Q0 after N round groups shows N*4 nested sha256_compress_round applications:
```
word_join4 (EL 0 (sha256_compress_round w_k (EL k sha256_K) (...nested...)))
           (EL 1 ...)
           (EL 2 ...)
           (EL 3 ...)
```

Q4/5/6/7 (message schedule registers) show sha256_sigma0/sigma1 expressions
matching the message schedule definition.

### Observation: K/W argument order
SHA256_COMPRESS_ROUND_KW_SYM swaps the arguments. After bridging+PREADD+KW_SYM,
the compress_round calls have `sha256_compress_round w_i (EL j sha256_K) state`
rather than `sha256_compress_round (EL j sha256_K) w_i state`.
This means the W comes first, K second. Need to account for this when matching
the postcondition against sha256_compress which uses `sha256_compress_round (EL n sha256_K) (EL n W) state`.

### PROVEN: Full symbolic execution with postcondition T
- SHA256_BLOCK_CORE_EXEC_TEST proved successfully
- Total execution time: ~45 minutes (109 instructions)
- Memory usage stable at 0.6-0.7% (no explosion)
- Checkpoint saved as s2n-arm-sha256

### CRITICAL: Do NOT apply bridging during symbolic execution
The first approach (RULE_ASSUM_TAC(REWRITE_RULE BRIDGE_RULES) after each group)
causes the terms to grow exponentially. After 4 round groups, the bridging rewrite
takes >15 minutes and doesn't terminate.

The correct approach: do ADD simplification only during execution, then apply
bridging at the very end for postcondition matching.

### CRITICAL: SHA256_COMPRESS_ROUND_KW_SYM is a looping rewrite
KW_SYM is symmetric (f K W = f W K). Never use it in REWRITE_RULE.
Apply it targeted with ONCE_REWRITE_RULE or pattern-match manually.

### TODO: Postcondition matching
The postcondition `sha256_block M H` expands to:
```
MAP2 word_add (sha256_compress 64 (sha256_message_schedule 48 M) H) H
```

Need to prove that:
1. The nested sha256h/sha256h2 chain equals sha256_compress 64
2. The sha256su0/sha256su1 chain equals sha256_message_schedule 48
3. The add-back (word_join4 of word_add) matches MAP2 word_add

Possible approach: prove a separate bridging theorem that connects the
hardware composition to sha256_block, possibly using concrete evaluation
to verify the algebraic identity.

### Key insight from interactive testing (2026-04-14, session 2)

**Applying SHA256H_BRIDGE during execution causes term duplication.**
The bridge converts sha256h(wj4 a b c d, ...) to wj4(EL 0 (CR^4 [a;b;c;d;e;f;g;h]), ..., EL 7 ...).
Each EL independently carries the full inner state expression. After 2 groups,
Q0 has 8x repetition of the inner state. After 16 groups it's astronomical.

**Correct approach: work from the SPEC side.**
Instead of converting sha256h → compress_round (forward bridge),
convert compress_round → sha256h (reverse bridge = GSYM SHA256H_BRIDGE).
Start from sha256_block, unfold to compress_round^64, then fold back into
16 sha256h calls. The result should syntactically match the symbolic execution.

**Practical strategy: prove equivalence via intermediate representation.**
Define sha256_hw_compress that directly composes sha256h calls, matching
the assembly structure. Prove:
1. sha256_hw_compress = sha256_compress 64 (via bridging, one group at a time)
2. The symbolic execution produces sha256_hw_compress (by construction)
3. Therefore the symbolic execution = sha256_compress 64

This avoids ever having both representations in the same term.
