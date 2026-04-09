# AI-Assisted Optimization of Formally Verified Cryptographic Code

## What this is

An agentic workflow that takes existing formally verified assembly implementations from [s2n-bignum](https://github.com/awslabs/s2n-bignum), attempts to optimize them, and produces machine-checked proofs that the optimized code is correct — all with minimal human intervention.

s2n-bignum is a collection of hand-written, performance-tuned assembly routines for cryptographic arithmetic (used in AWS-LC). Every function has a formal correctness proof in HOL Light. The proofs verify that the assembly computes the right mathematical result for all inputs, checked against a formal model of the CPU's instruction set.

The challenge: modifying any of this code — even reordering two independent instructions — invalidates the proof. Re-proving correctness is labor-intensive and requires deep expertise in both assembly optimization and interactive theorem proving. This creates a bottleneck: the code is hard to evolve.

## What we demonstrated

We built and exercised an end-to-end pipeline where an AI agent:

1. **Analyzes** an existing implementation (`bignum_montmul_p256` — Montgomery multiplication mod P-256, a performance-critical inner loop for ECDSA/ECDH)
2. **Generates** an optimized variant (instruction reordering to improve pipeline utilization)
3. **Validates** correctness via 10 million randomized test cases
4. **Benchmarks** the new code against the original using `perf` and `llvm-mca`
5. **Produces a machine-checked HOL Light proof** that the new code computes the correct result
6. **Integrates** the new implementation into the s2n-bignum build system, test suite, and benchmark harness

The proof was built and verified through the project's official build system (`make p256/bignum_montmul_p256_reordered.correct`), producing the same kind of `.correct` artifact as every other function in the library.

## What this enables

Today, optimizing a single s2n-bignum function requires a developer who understands x86/ARM microarchitecture, Montgomery arithmetic, and HOL Light proof engineering. There are very few such people. Changes take days to weeks.

With this workflow, an AI agent can:

- **Try many optimization strategies in parallel** — instruction reordering, register allocation changes, compiler-driven optimization via C intrinsics — and discard the ones that don't improve performance, before investing in the proof
- **Adapt existing proofs** to new code variants. For instruction reorderings, the proof tactics work unchanged — only the byte sequence needs updating. For deeper changes, the agent can modify the proof interactively using `holctl`
- **Scale across the library** — the same workflow applies to all ~300 functions in s2n-bignum

The immediate practical value is not that the agent will find dramatic speedups in already-optimized code (the existing code is very good). It's that the agent can:

- **Port optimizations across architectures** — apply ARM NEON tricks to x86 AVX, or vice versa
- **Tune for new microarchitectures** — when a new CPU ships (e.g., Granite Rapids), re-optimize the entire library for its pipeline characteristics
- **Maintain proof coverage** as the code evolves — the proof is the expensive part, and the agent can handle it
- **Explore the design space** — try algorithmic variants (different curve representations, different multiplication strategies) that humans wouldn't attempt because the proof cost is too high

## What we learned

- **The existing s2n-bignum code is near-optimal** for current hardware. `bignum_montmul_p256` runs at 37.5 cycles, within 10% of the theoretical minimum. The agent confirmed this through bottleneck analysis.
- **Compilers cannot reproduce the hand-written code quality.** Neither GCC nor Clang generates `adcx`/`adox` dual carry chains from intrinsics. Clang's output is 15% slower; GCC's is catastrophically bad.
- **Adapting existing proofs is far more practical than proving equivalence.** For instruction reorderings, the existing proof works with zero tactic changes — only the byte sequence in `define_assert_from_elf` needs updating. The symbolic execution engine doesn't care about instruction order, only data dependencies.
- **The proof infrastructure works well for AI agents.** `holctl` provides a clean interface for interactive proof development, with structured JSON output, session isolation, and DMTCP checkpointing for fast restarts.

## What's needed next

1. **Target functions with more optimization headroom** — newer additions (ML-KEM, ML-DSA, SHA-3) and functions that haven't been SLOTHY-optimized
2. **ARM support** — the ARM equivalence proof infrastructure is more mature and has existing examples to follow
3. **Batch mode** — run the workflow unattended across many functions overnight
4. **Deeper optimizations** — algorithmic changes (different curve formulas, Karatsuba decomposition) that require proof modifications, not just byte sequence updates
