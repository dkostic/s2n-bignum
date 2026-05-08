#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

"""Extract the `.Loop6x` fast-path (AES-128, no counter wrap, more-blocks
branch) of `aesni_gcm_encrypt.S` into a straight-line, VEX-only standalone
routine suitable for Milestone 7's register-only proof.

The filtered output retains every SIMD/VEX instruction on the fast path and
every memory load/store that participates in the cryptographic body.  The
interleaved scalar plumbing is dropped because it only updates loop
state that does not affect the ciphertext/ghash/counter outputs of the
current iteration:

  * `addl $100663296,%ebx ; jc .Lhandle_ctr32`  — CTR32 wrap probe, not
    taken in the fast path.
  * `xorq/cmpq/setnc/negq/andq/leaq`  — end-of-input probe, setting up
    `%r14` for NEXT iteration's plaintext-stash address.
  * `movbeq N(%r14),%r1[23] ; movq %r1[23],M(%rsp)` pairs — stash the
    NEXT iteration's plaintext blocks into a scratch stack frame for
    that iteration's GHASH accumulator, not consumed by the current
    iteration's outputs.
  * `prefetcht0 N(%rdi)`  — memory hints.
  * `leaq 96(%rdi),%rdi ; leaq 96(%rsi),%rsi`  — advance input/output
    pointers for the NEXT iteration.
  * `addq $0x60,%rax ; subq $0x6,%rdx ; jc .L6x_done`  — loop-count
    update (we take the fall-through, 'more blocks remain').
  * `cmpl $11,%r10d ; jb .Lenc_tail`  — AES-128 ↦ take the branch to
    the tail block; in the extracted body, the two bypass branches for
    AES-192 and AES-256 (lines 503-535 of the source) are dropped.
  * The `.Lhandle_ctr32`, `.Lenc_tail` label-block branches are
    linearised by splicing the fast-path continuation in place.
  * The next-iteration register-setup block at lines 604/606/608/610/
    612/614/615 (vpxor/vmovdqa/vmovdqu 32(%rsp)) is dropped — those
    instructions belong to the NEXT iteration's entry fan-out.

Output addressing:

  * `-N(%rsi)` stores at lines 603..613 are rewritten to `(96-N)(%rsi)`
    to compensate for dropping the leaq 96(%rsi),%rsi pointer advance.
    The caller passes %rsi pointing at the output buffer origin.

The script emits the extracted body to stdout, annotated with
source-line comments to preserve traceability.
"""

import re
import sys
from pathlib import Path

SOURCE_START = 310   # .Loop6x__... label
SOURCE_END   = 616   # trailing jmp .Loop6x (dropped)

# Body regions on the fast path: pre-resume head, .Lresume body,
# .Lenc_tail body, more-blocks exit.
#
# Each region is (start_line, end_line, kind).  end_line is inclusive.
# The regions are processed in order and concatenated.
REGIONS = [
    # Pre-resume head at top of .Loop6x (drop 310 label, 311-312 probe/branch).
    (313, 316, "pre-resume"),
    # .Lresume body (drop 318 label, drop 500-501 aes-len probe/branch).
    (319, 499, "resume-body"),
    # .Lenc_tail body (drop 560 label, drop 599-601 loop-count probe/branch).
    (561, 597, "enc-tail"),
    # More-blocks path (drop 616 jmp .Loop6x; keep only ciphertext stores).
    (603, 613, "ciphertext-stores"),
]

# Scalar mnemonics on the fast path that do not contribute to the
# cryptographic body.  Matched at the start of the instruction after
# leading whitespace.
SCALAR_DROP = {
    "addl", "addq", "andq", "cmpl", "cmpq", "decl", "je", "jb", "jc",
    "jmp", "jnz", "leaq", "movbeq", "movq", "negq", "prefetcht0",
    "setnc", "subq", "xorq",
}

# Instructions to include even though they touch non-XMM state or address
# memory; they are all VEX-encoded SIMD ops.
def is_simd_or_branch_label(line: str) -> bool:
    t = line.strip()
    if not t or t.startswith("//") or t.startswith("#") or t.startswith("/*"):
        return False
    if t.endswith(":"):
        return False
    first = t.split(None, 1)[0]
    return first not in SCALAR_DROP


RSI_STORE_RE = re.compile(r"(-\d+)\(%rsi\)")

def rewrite_rsi_store(insn: str) -> str:
    """Rewrite negative `-N(%rsi)` to positive `(96-N)(%rsi)` for the
    fast-path ciphertext stores, because we dropped `leaq 96(%rsi),%rsi`."""
    def sub(m):
        off = int(m.group(1))
        # Original code used -96 -> offset 0, -80 -> 16, ..., -16 -> 80.
        new = 96 + off
        return f"{new}(%rsi)"
    return RSI_STORE_RE.sub(sub, insn)


def main(argv):
    if len(argv) != 3:
        print("usage: extract_stitched_6x.py <input.S> <output.S>",
              file=sys.stderr)
        return 2
    src = Path(argv[1]).read_text().splitlines()
    out = []
    out.append("// ===========================================================================")
    out.append("// Stitched 6-way AES-128-CTR + GHASH loop body, standalone-artefact form.")
    out.append("//")
    out.append("// Milestone 7 of the AES-GCM x86 verification plan.  Produced from the")
    out.append("// `.Loop6x__aesni_gcm_encrypt_aesni_ctr32_ghash_6x_0` body of")
    out.append("// `aesni_gcm_encrypt.S` by `tools/extract_stitched_6x.py`: retain every VEX")
    out.append("// SIMD instruction on the fast path (AES-128, no CTR32 wrap, more-blocks")
    out.append("// remain), drop the interleaved scalar plumbing that only updates state for")
    out.append("// the NEXT iteration, and rewrite the post-leaq rsi-offsets to positive form.")
    out.append("//")
    out.append("// ABI (System V):")
    out.append("//   %rdi  plaintext pointer       (6 blocks at rdi+{0,16,..,80})")
    out.append("//   %rsi  ciphertext pointer      (6 blocks at rsi+{0,16,..,80})")
    out.append("//   %rcx  key schedule - 128      (k_i at (16*i - 128)(%rcx))")
    out.append("//   %r9   Htable + 32             (H-power i at (16*i - 32)(%r9))")
    out.append("//   %r8   counter-block output    (16 bytes, inc32^6 icb after body)")
    out.append("//   %r11  constants pointer       (16(%r11)=reduction poly, 32(%r11)=+1)")
    out.append("//")
    out.append("// Entry register state (per the original `.Loop6x` entry fan-out):")
    out.append("//   xmm9  = k0 XOR counter lane 0")
    out.append("//   xmm10..xmm14 = counter lanes 1..5 (pre-AddRoundKey)")
    out.append("//   xmm15 = k0 (round-0 key)")
    out.append("//   xmm7  = GHASH high-half accumulator (prior iter)")
    out.append("//   xmm8  = GHASH low-half accumulator  (prior iter)")
    out.append("//   xmm4  = prior-iter reduction residue")
    out.append("//   xmm2  = +1 constant for counter increment")
    out.append("//   stack 16..112(%rsp) = prior-iter ciphertext blocks for GHASH")
    out.append("//")
    out.append("// Exit state (after the 6 ciphertext stores):")
    out.append("//   memory at rsi+{0,16,..,80} = 6 ciphertext blocks")
    out.append("//   memory at (%r8)            = inc32^6 icb (new counter block)")
    out.append("//   xmm4..xmm8                 = new GHASH register halves")
    out.append("// ===========================================================================")
    out.append("")
    out.append("        .text")
    out.append("        .globl  aesni_gcm_stitched_6x_core")
    out.append("        .type   aesni_gcm_stitched_6x_core,@function")
    out.append("        .align  16")
    out.append("aesni_gcm_stitched_6x_core:")
    out.append("")

    for start, end, kind in REGIONS:
        out.append(f"        // --- region {kind} : source lines {start}-{end} ---")
        for lineno in range(start, end + 1):
            line = src[lineno - 1]
            if not is_simd_or_branch_label(line):
                continue
            insn = line.strip()
            if kind == "ciphertext-stores":
                insn = rewrite_rsi_store(insn)
                # Of the 12 instructions at lines 603-614, keep only the six
                # vmovdqu stores (603,605,607,609,611,613).  The six in-between
                # vpxor/vmovdqa at 604,606,608,610,612,614 set up the NEXT
                # iteration's register fan-out.
                if not insn.startswith("vmovdqu"):
                    continue
                if ",%xmm" in insn.split(",")[-1]:
                    # vmovdqu  MEM,%xmmK is a load, not a store — skip.
                    continue
            out.append(f"        {insn}")
        out.append("")

    out.append("        ret")
    out.append("        .size   aesni_gcm_stitched_6x_core,.-aesni_gcm_stitched_6x_core")
    out.append("")

    Path(argv[2]).write_text("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
