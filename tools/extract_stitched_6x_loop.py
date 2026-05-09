#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

"""Extract the `.Loop6x` fast-path of `aesni_gcm_encrypt.S` as a loop,
for Milestone 8's bulk-loop correctness proof.

Builds on `extract_stitched_6x.py` (Milestone 7): keeps the same 166
filtered SIMD instructions as the loop body, then appends the loop
plumbing so that the whole routine executes the 6-block body k times
where k is dictated by RDX's initial value:

  loop_top:
      <M7 body, 166 insns, bytes [0, 0x348)>
      subq    $0x6, %rdx
      jc      done_exit
      <7 insns: 6 counter-rotation vpxor/vmovdqa + vmovdqu xmm7 reload>
      jmp     loop_top
  done_exit:
      ret

The back-edge shape (`jc` to a forward label, fall-through to
counter-rotation + unconditional `jmp` back) matches
`ENSURES_WHILE_UP2_TAC`.  The body byte layout [0, 0x348) is byte-for-byte
identical with Milestone 7's `aesni_gcm_stitched_6x_mc`, so M7's theorem
composes into this proof via `X86_BIGSTEP_TAC` without re-proving the
body.
"""

import sys
from pathlib import Path

# The counter-rotation and xmm7 reload at source lines 604/606/608/610/
# 612/614/615 of aesni_gcm_encrypt.S (interleaved with the ciphertext
# stores in the original, but hoisted after them in the extracted body
# since the stores are register-value-independent of the rotations).
#
# Uses 32(%rsp) for xmm7 reload to match the encrypt source's stack
# layout.
COUNTER_ROTATION_INSNS = [
    "vpxor   %xmm15,%xmm1,%xmm9",     # k0 XOR new-counter = next-iter xmm9
    "vmovdqa %xmm0,%xmm10",           # lane 1 for next iter
    "vmovdqa %xmm5,%xmm11",           # lane 2
    "vmovdqa %xmm6,%xmm12",           # lane 3
    "vmovdqa %xmm7,%xmm13",           # lane 4 (note: xmm7 is OVERWRITTEN by reload below)
    "vmovdqa %xmm3,%xmm14",           # lane 5
    "vmovdqu 0x20(%rsp),%xmm7",       # reload prior-iter GHASH high from stash slot
]


def main(argv):
    if len(argv) != 3:
        print("usage: extract_stitched_6x_loop.py <m7.S> <output.S>",
              file=sys.stderr)
        return 2

    # Read M7's filtered body .S file and inline it up to (but not
    # including) the trailing `ret` at `pc = 0x348`.
    body = Path(argv[1]).read_text().splitlines()

    out = []
    out.append("// ===========================================================================")
    out.append("// Stitched 6-way AES-128-CTR + GHASH bulk loop, standalone-artefact form.")
    out.append("//")
    out.append("// Milestone 8 of the AES-GCM x86 verification plan.  Wraps Milestone 7's")
    out.append("// `aesni_gcm_stitched_6x_core` body in the `.Loop6x` back-edge of aws-lc's")
    out.append("// aesni_gcm_encrypt.  Produced by `tools/extract_stitched_6x_loop.py`:")
    out.append("// takes M7's 166-instruction filtered fast-path body verbatim, then")
    out.append("// appends the loop-count test (subq/jc), 7 counter-rotation/stash-reload")
    out.append("// instructions, and an unconditional back-edge (jmp).  The body byte")
    out.append("// layout [0, 0x348) is byte-for-byte identical with M7, so M7's theorem")
    out.append("// composes via X86_BIGSTEP_TAC.  The loop-count convention is descending")
    out.append("// by 6 on each iteration, exits on CF set (underflow).")
    out.append("//")
    out.append("// ABI (System V):")
    out.append("//   %rdi  plaintext pointer          (advances by 96 per iter externally;")
    out.append("//                                     in this artefact, plaintext is held")
    out.append("//                                     constant across the loop invariant —")
    out.append("//                                     see M8 proof for the encode of the")
    out.append("//                                     per-iteration pointer offset)")
    out.append("//   %rsi  ciphertext pointer         (same)")
    out.append("//   %rcx  key schedule - 128")
    out.append("//   %r9   Htable + 32")
    out.append("//   %r8   counter-block output")
    out.append("//   %r11  constants pointer")
    out.append("//   %rdx  remaining 16-byte blocks (decremented by 6 each iter, exit on CF)")
    out.append("// ===========================================================================")
    out.append("")
    out.append("        .text")
    out.append("        .globl  aesni_gcm_stitched_6x_loop_core")
    out.append("        .type   aesni_gcm_stitched_6x_loop_core,@function")
    out.append("        .align  16")
    out.append("aesni_gcm_stitched_6x_loop_core:")
    out.append("")

    # Emit the M7 body verbatim (everything between the entry label and
    # the trailing `ret` + `.size`).  Scan for the start/end markers.
    in_body = False
    for line in body:
        stripped = line.strip()
        if stripped.startswith("aesni_gcm_stitched_6x_core:"):
            in_body = True
            continue
        if in_body:
            if stripped.startswith("ret") or stripped.startswith(".size"):
                break
            out.append(line)

    # Counter-rotation + stash reload + back-edge.  The `jc .Ldone_exit`
    # is a short forward jump; `jmp aesni_gcm_stitched_6x_loop_core`
    # is a near unconditional back-edge.
    out.append("        // --- region back-edge : loop plumbing ---")
    out.append("        subq    $0x6, %rdx")
    out.append("        jc      .Ldone_exit")
    for insn in COUNTER_ROTATION_INSNS:
        out.append(f"        {insn}")
    out.append("        jmp     aesni_gcm_stitched_6x_loop_core")
    out.append("")
    out.append(".Ldone_exit:")
    out.append("        ret")
    out.append("        .size   aesni_gcm_stitched_6x_loop_core,.-aesni_gcm_stitched_6x_loop_core")
    out.append("")

    Path(argv[2]).write_text("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
