#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

"""Extract the `.Loop6x` fast-path (AES-128, no counter wrap, more-blocks
branch) of `aesni_gcm_encrypt.S` into a straight-line, VEX-only standalone
routine suitable for Milestone 7's register-only proof.

The filtered output retains every SIMD/VEX instruction on the fast path,
every memory load/store that participates in the cryptographic body, and
the pointer-advance `leaq` instructions that carry state across iterations
of the loop wrapper (two for %rdi/%rsi, one for %r14/r12 stash pointer).
It ALSO admits the scalar r14-advance probe and the movbeq/movq stash
pairs that populate sp+32..sp+112 with byte-reversed ciphertext for the
NEXT iteration's GHASH fold (see feedback_stash_offset_trace.md: the
stash is off-by-TWO from M8-CT production).

The MOVBE instruction is admitted verbatim — the s2n-bignum x86
decoder gained MOVBE support in the same change that introduced this
extractor widening.

The remaining interleaved scalar plumbing is dropped because it only
updates loop state that does not affect the ciphertext/ghash/counter
outputs of the current iteration:

  * `addl $100663296,%ebx ; jc .Lhandle_ctr32`  — CTR32 wrap probe, not
    taken in the fast path.
  * `prefetcht0 N(%rdi)`  — memory hints.
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

Admitted scalar insns (used by Stage B3a's stashed_ct_preserved
invariant):

  * Lines 341-361: end-probe `xorq %r12,%r12 ; cmpq %r14,%r15 ;
    setnc %r12b ; negq %r12 ; andq $0x60,%r12` (6 insns) sets
    %r12 to 0x60 when %r14 < %r15, else 0.
  * Line 367: `leaq (%r14,%r12,1),%r14` (1 insn) advances r14 by 0
    or 96 accordingly.
  * Lines 373/375/408/412/430/435/452/456/475/477/495/497: the
    12 movbeq reads (emitted verbatim, 5 bytes each).
  * Lines 377/379/416/418/438/440/459/461/480/482/582/589: the
    12 movq stores to (%rsp)+{32,40,48,56,64,72,80,88,96,104,112,120}.

Output addressing:

  * `leaq 96(%rdi),%rdi` (line 583) and `leaq 96(%rsi),%rsi` (line 590)
    are preserved so that RDI and RSI advance by 96 across each
    wrapper iteration.  The `-N(%rsi)` stores at lines 603..613 are
    emitted verbatim; they resolve correctly because the preceding
    `leaq` has already advanced %rsi by 96.

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

# Scalar mnemonics that are ALWAYS dropped because they belong to loop
# plumbing NOT on the per-iter data path (CTR32 wrap probe, loop-count
# probe, AES-variant probe, prefetch hints, unconditional branches).
#
# Scalar mnemonics that are ADMITTED for Stage B3a are handled via
# SCALAR_ADMIT below — NOT listed here.  The `movq` and `movbeq`
# mnemonics are admitted by dedicated logic in main() (movq: line
# whitelist; movbeq: line whitelist, emitted verbatim now that the
# s2n-bignum decoder supports MOVBE — see feedback_movbe_decoder_added).
SCALAR_DROP = {
    "addl", "addq", "cmpl", "decl", "je", "jb", "jc",
    "jmp", "jnz", "prefetcht0", "subq",
}

# Admitted scalar r14-advance probe (lines 341-361 of the source).
# These set %r12 to 0 or 0x60 depending on whether %r14 < %r15, and
# are followed by `leaq (%r14,%r12,1),%r14` (whitelisted below) that
# advances %r14 by the same amount.  See
# feedback_stash_offset_trace.md.
SCALAR_ADMIT_LINES = {
    341,  # xorq  %r12,%r12
    342,  # cmpq  %r14,%r15
    350,  # setnc %r12b
    354,  # negq  %r12
    361,  # andq  $0x60,%r12
}

# Lines carrying `movq %r1[23],N(%rsp)` stash stores (complement of the
# movbeq reads).  Admitted unconditionally — the plain `movq` mnemonic is
# in SCALAR_DROP by default (it is widely used for unrelated plumbing,
# e.g. `movq %rsi,%r14` at line 84 of the source, which is OUTSIDE our
# region range anyway), so we whitelist these 12 line numbers explicitly.
MOVQ_STASH_LINES = {
    377, 379, 416, 418, 438, 440, 459, 461, 480, 482, 582, 589,
}

# Lines carrying `movbeq N(%r14),%r1[23]` stash reads.  Admitted
# verbatim now that the s2n-bignum decoder supports MOVBE.
MOVBE_STASH_LINES = {
    373, 375, 408, 412, 430, 435, 452, 456, 475, 477, 495, 497,
}

# Pointer-advance leaqs to preserve.  Matched against the instruction with
# all whitespace collapsed to single spaces; keeps RDI/RSI advances by 96
# and the r14 stash-pointer advance at source line 367.
LEAQ_KEEP = {
    "leaq 96(%rdi),%rdi",
    "leaq 96(%rsi),%rsi",
    "leaq (%r14,%r12,1),%r14",
}


def _normalize(insn: str) -> str:
    """Collapse whitespace runs to single spaces for LEAQ_KEEP matching."""
    return " ".join(insn.split())


def is_simd_or_branch_label(line: str, lineno: int) -> bool:
    t = line.strip()
    if not t or t.startswith("//") or t.startswith("#") or t.startswith("/*"):
        return False
    if t.endswith(":"):
        return False
    first = t.split(None, 1)[0]
    if first == "leaq":
        return _normalize(t) in LEAQ_KEEP
    if first == "movbeq":
        return lineno in MOVBE_STASH_LINES
    if first == "movq":
        return lineno in MOVQ_STASH_LINES
    # Admit r14-probe scalar insns by line number (xorq/cmpq/setnc/negq/andq).
    if lineno in SCALAR_ADMIT_LINES:
        return True
    return first not in SCALAR_DROP




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
            if not is_simd_or_branch_label(line, lineno):
                continue
            insn = line.strip()
            if kind == "ciphertext-stores":
                # The `leaq 96(%rsi),%rsi` at line 590 has already advanced
                # rsi, so the original `-N(%rsi)` offsets resolve correctly.
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
