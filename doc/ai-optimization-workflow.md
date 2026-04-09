# s2n-bignum Optimization Workflow — Agent Guide

This document describes the end-to-end workflow for optimizing a formally verified assembly function in s2n-bignum and producing a machine-checked HOL Light proof of the optimized version.

## Prerequisites

- s2n-bignum repo at `/home/ubuntu/workspace/s2n-bignum`
- HOL Light at `/home/ubuntu/workspace/hol-light` (built with `HOLLIGHT_USE_MODULE=1`)
- `holctl` CLI tool (at `~/.local/bin/holctl`)
- DMTCP checkpoints: `s2n-x86` and/or `s2n-arm`
- Tools: `gcc`, `clang`, `perf`, `llvm-mca-18`, `objdump`
- Optional: `uiCA` at `/tmp/uiCA/uiCA.py` (x86 throughput analyzer)

## Repository Structure

```
s2n-bignum/
├── x86/                    # x86 implementations
│   ├── p256/               # P-256 curve functions
│   │   ├── bignum_montmul_p256.S      # Assembly source
│   │   └── bignum_montmul_p256.o      # Built by Makefile
│   ├── proofs/             # HOL Light proofs
│   │   ├── base.ml         # Proof infrastructure (loaded by s2n-x86 checkpoint)
│   │   ├── equiv.ml        # Equivalence proof infrastructure
│   │   └── bignum_montmul_p256.ml     # Correctness proof
│   └── Makefile
├── arm/                    # ARM implementations (same structure)
├── include/s2n-bignum.h    # C declarations
├── tests/test.c            # Functional tests
├── benchmarks/benchmark.c  # Performance benchmarks
└── tools/
    └── collect-signatures.py  # Cross-arch consistency checker
```

## Workflow Stages

### Stage 1: Analyze the Target Function

Read and understand the existing implementation:

```bash
# Read the assembly
cat x86/p256/bignum_montmul_p256.S

# Read the existing proof to understand the proof structure
cat x86/proofs/bignum_montmul_p256.ml

# Build the .o and get instruction count
cd x86 && make p256/bignum_montmul_p256.o
objdump -d p256/bignum_montmul_p256.o | wc -l

# Static analysis with llvm-mca (use --mcpu matching the target)
objdump -d --no-show-raw-insn p256/bignum_montmul_p256.o | \
  grep -v "push\|pop\|ret$\|^$\|file\|Dis\|section\|montmul\|nop" | \
  sed 's/^[[:space:]]*[0-9a-f]*:[[:space:]]*//' > /tmp/core.s
llvm-mca-18 --mcpu=graniterapids --iterations=100 --bottleneck-analysis /tmp/core.s

# Benchmark baseline
cd ../benchmarks && make && ./benchmark bignum_montmul_p256
```

Key things to identify:
- Algorithm structure (what mathematical operation, what reduction strategy)
- Instruction count and types (how many mulx, adcx/adox, memory ops)
- Bottleneck (port pressure vs data dependencies vs frontend)
- Register usage (which registers are free, if any)
- Proof structure (what tactics are used, what step ranges)

### Stage 2: Generate Optimized Variant

Several strategies, in order of proof difficulty:

#### Strategy A: Instruction Reordering (easiest to prove)

Swap independent instructions to improve pipeline utilization. Two instructions are independent if they read/write disjoint registers and neither depends on the other's output.

Example: `xor r14d, r14d` and `mov rdx, [rcx+8]` touch different registers and can be freely swapped.

**Proof impact**: Zero tactic changes needed. The symbolic execution engine produces the same expressions regardless of instruction order for independent instructions.

#### Strategy B: Compiler-Driven (C intrinsics)

Write the algorithm in C using intrinsics (`_mulx_u64`, `_addcarryx_u64`, etc.) and compile with `gcc -O3 -march=native` and `clang -O3 -march=native`.

```bash
gcc -O3 -march=native -mbmi2 -madx -c impl.c -o impl_gcc.o
clang -O3 -march=native -mbmi2 -madx -c impl.c -o impl_clang.o
```

**Known limitation**: Neither GCC nor Clang generates `adcx`/`adox` dual carry chains from `_addcarryx_u64` intrinsics. For functions that rely on dual carry chains (most s2n-bignum multiplications), the compiler output will be slower. This strategy works better for simpler functions or functions that don't use ADX.

**Proof impact**: The compiler output is a completely different instruction sequence. You must adapt the proof significantly or write a new one.

#### Strategy C: Manual Assembly Optimization

Modify the assembly directly — different register allocation, algorithmic micro-optimizations, fusing operations in composite functions.

**Proof impact**: Depends on the change. Register renaming needs no tactic changes. Algorithmic changes require proof modifications.

### Stage 3: Validate Correctness

Always test before investing in the proof.

```bash
# Build the new .o
gcc -I ../include -c new_function.S -o new_function.o

# Write a quick test that compares against the original
cat > /tmp/test.c << 'EOF'
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
extern void original(uint64_t*, const uint64_t*, const uint64_t*);
extern void optimized(uint64_t*, const uint64_t*, const uint64_t*);
int main() {
    uint64_t x[4], y[4], z1[4], z2[4];
    srand(42);
    for (int i = 0; i < 10000000; i++) {
        for (int j = 0; j < 4; j++) {
            x[j] = ((uint64_t)rand()<<32)|rand();
            y[j] = ((uint64_t)rand()<<32)|rand();
        }
        original(z1, x, y);
        optimized(z2, x, y);
        if (z1[0]!=z2[0]||z1[1]!=z2[1]||z1[2]!=z2[2]||z1[3]!=z2[3]) {
            printf("MISMATCH at i=%d\n", i);
            return 1;
        }
    }
    printf("10M tests PASS\n");
}
EOF
gcc -O2 test.c original.o optimized.o -o test && ./test
```

**Gate**: If tests fail, fix the optimization or discard it. Do not proceed to benchmarking or proof.

### Stage 4: Benchmark

```bash
# Quick rdtsc-based benchmark
# Or use the s2n-bignum benchmark harness after integration (Stage 6)
perf stat -e cycles,instructions -r 5 ./benchmark_binary
```

**Gate**: If no performance improvement, consider whether the change is still worth proving (e.g., for code clarity or maintainability). For pure optimization work, discard and try a different strategy.

### Stage 5: Produce the HOL Light Proof

This is the most important stage. There are two approaches:

#### Approach A: Adapt the Existing Proof (recommended)

This works when the optimized code has the same algorithmic structure as the original. The proof file is a copy of the original with:

1. **Updated byte sequence** in `define_assert_from_elf` — must match the new `.o` file exactly
2. **Renamed symbols** — all occurrences of the function name in definitions and theorem names
3. **Same proof tactics** — if the optimization preserves the data flow (e.g., instruction reordering), the tactics work unchanged

Steps:

```python
# 1. Copy the original proof
cp x86/proofs/bignum_foo.ml x86/proofs/bignum_foo_opt.ml

# 2. Rename all symbols
sed -i 's/bignum_foo/bignum_foo_opt/g' x86/proofs/bignum_foo_opt.ml
sed -i 's/BIGNUM_FOO/BIGNUM_FOO_OPT/g' x86/proofs/bignum_foo_opt.ml

# 3. Get the byte sequence from the new .o
holctl start --name tmp --checkpoint s2n-x86
holctl eval tmp 'Sys.chdir "/path/to/s2n-bignum"'
holctl --full eval tmp 'print_literal_from_elf "x86/p256/bignum_foo_opt.o"'
holctl stop tmp

# 4. Replace the byte list in define_assert_from_elf

# 5. Remove Windows ABI sections (unless you also built a .obj)

# 6. Build and verify
cd x86 && make p256/bignum_foo_opt.correct
```

The `make *.correct` target:
- Assembles the `.S` into `.o` and `.obj` (Windows)
- Compiles the proof `.ml` into a native binary using HOL Light's module system
- Runs the binary, which executes all `prove(...)` calls
- Writes the output to `.correct`

**When tactics need changes**: If the optimization changes the number of instructions or the data flow, you'll need to update:
- Step ranges in `X86_ACCSTEPS_TAC` (e.g., `(1--96)` becomes `(1--98)`)
- The `sum_sNN` variable names in `ABBREV_TAC` (they're named after the step that produced them)
- The accumulator step lists for the final correction (e.g., `[98;100;103;105;106]`)

Use `holctl` for interactive debugging:

```bash
holctl start --name debug --checkpoint s2n-x86
holctl eval debug 'Sys.chdir "/path/to/s2n-bignum"'
holctl eval debug 'loadt "x86/proofs/bignum_foo_opt.ml"'
# If it fails, use holctl interactively to step through the proof
```

#### Approach B: Equivalence Proof

Prove that the new code produces the same output as the original for all inputs. This uses the infrastructure in `x86/proofs/equiv.ml` (or `arm/proofs/equiv.ml`).

This approach is more complex and currently has limitations on x86:
- The x86 equivalence infrastructure is less mature than ARM's
- Handling push/pop (stack frame) requires careful nonoverlapping assumptions
- No existing x86 equivalence proofs to use as templates

For ARM, there are many working examples in `arm/proofs/` (search for files that `needs "arm/proofs/equiv.ml"`).

The equivalence approach is better when:
- The optimization changes the algorithm significantly
- You want to prove the new code equivalent to the old without understanding the mathematical proof
- The original proof is very complex and hard to adapt

### Stage 6: Integrate into s2n-bignum

Files to create/modify:

| File | Action |
|------|--------|
| `x86/p256/bignum_foo_opt.S` | Create: the optimized assembly |
| `x86/proofs/bignum_foo_opt.ml` | Create: the HOL Light proof |
| `x86/Makefile` | Add `.o` to the OBJ list |
| `include/s2n-bignum.h` | Add `extern void bignum_foo_opt(...)` declaration |
| `tests/test.c` | Add test function and dispatch entry |
| `benchmarks/benchmark.c` | Add benchmark function and dispatch entry |
| `tools/collect-signatures.py` | Add to `onlyInX86` array (if x86-only) |

Build and verify:

```bash
cd x86
make -j$(nproc)                              # Build library
cd ../tests && make && ./test bignum_foo_opt  # Run tests
cd ../benchmarks && make && ./benchmark bignum_foo_opt  # Benchmark
cd ../x86 && make p256/bignum_foo_opt.correct # Run proof
```

## Tool Reference

### holctl (HOL Light server management)

```bash
holctl start --name NAME --checkpoint s2n-x86   # Start server (~2s)
holctl eval NAME 'EXPRESSION'                    # Evaluate OCaml/HOL
holctl --raw eval NAME 'EXPRESSION'              # Raw output (no JSON)
holctl --full eval NAME 'EXPRESSION'             # No output truncation
holctl --timeout 600 eval NAME 'EXPRESSION'      # Custom timeout
holctl goal NAME 'TERM'                          # Set proof goal
holctl tactic NAME 'TACTIC'                      # Apply tactic
holctl back NAME                                 # Undo last tactic
holctl search NAME 'PATTERN'                     # Search theorems
holctl stop NAME                                 # Stop server
```

### llvm-mca (static analysis)

```bash
# Throughput and bottleneck analysis
llvm-mca-18 --mcpu=graniterapids --iterations=100 --bottleneck-analysis input.s

# Timeline view (see instruction-level scheduling)
llvm-mca-18 --mcpu=graniterapids --iterations=1 --timeline input.s

# Summary only
llvm-mca-18 --mcpu=graniterapids --iterations=100 --summary-view input.s
```

### perf (real hardware measurement)

```bash
sudo sysctl kernel.perf_event_paranoid=-1  # Enable (once)
perf stat -e cycles,instructions,cache-misses -r 5 ./binary
```

### uiCA (x86 throughput predictor)

```bash
# Requires .o file input. Supported archs: SNB,IVB,HSW,BDW,SKL,SKX,KBL,CFL,CLX,ICL,TGL,RKL
python3 /tmp/uiCA/uiCA.py -arch ICL file.o
python3 /tmp/uiCA/uiCA.py -arch ICL file.o -TPonly  # Just the number
```

Note: uiCA does not support `mulx` instructions (marks them as "X"). Its predictions are unreliable for BMI2-heavy code. Use `llvm-mca` instead.

## Key Lessons from the Trial Run

1. **The existing s2n-bignum code is near-optimal.** `bignum_montmul_p256` runs at 37.5 cycles vs ~24 cycle theoretical minimum (limited by multiplier throughput). Don't expect dramatic speedups on already-optimized functions.

2. **Compilers can't match hand-written crypto assembly.** Neither GCC nor Clang generates `adcx`/`adox` dual carry chains. The compiler-driven strategy is unlikely to beat the original for multiplication-heavy functions.

3. **Adapting the existing proof is far easier than equivalence proofs.** For instruction reorderings, the proof works with zero tactic changes — only the byte sequence needs updating. This is because `X86_ACCSTEPS_TAC` does symbolic execution that doesn't depend on instruction order for independent instructions.

4. **Test before proving.** The proof is the most expensive step (minutes to hours). Testing takes seconds. Always validate correctness with randomized tests first.

5. **Store-load fusion across operation boundaries doesn't help.** In composite functions like `p256_montjadd`, the CPU's out-of-order engine already hides store-forwarding latency. Keeping values in registers across operations saves no measurable time.

6. **The `collect-signatures.py` script enforces cross-architecture consistency.** If you add an x86-only function, add it to the `onlyInX86` array. Same for ARM-only functions and `onlyInArm`.

7. **The proof build requires `HOLLIGHT_USE_MODULE=1`.** Rebuild HOL Light with this flag to get `hol_lib.cmxa`, which the `make *.correct` target needs.

## Optimization Targets

Functions most likely to benefit from optimization:
- **Newer additions** (ML-KEM, ML-DSA, SHA-3) that haven't been as heavily hand-tuned
- **`_alt` variants** that use plain `mul`/`adc` instead of `mulx`/`adcx`/`adox` — these have more scheduling freedom
- **Composite functions** (`p256_montjadd`, `p256_montjdouble`, etc.) where operation ordering or fusion might help
- **Functions being ported to a new microarchitecture** where pipeline characteristics differ
