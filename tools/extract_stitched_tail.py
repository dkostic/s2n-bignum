#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

"""Extract the GHASH finalisation tail of aesni_gcm_encrypt.S (Milestone 9).

Scope: source lines 618-799 of aesni_gcm_encrypt.S — everything from
`.L6x_done__...:` (the `jc` target reached when the outer loop count
underflows) through the final `vmovdqu %xmm8, (%r12)` tag write.  The
function prologue/epilogue (`pushq`/`popq`/`vzeroupper`/stack fixup) is
kept out of this artefact: it will be handled by the top-level M10 proof
that wraps prologue → warmups → bulk loop → tail → epilogue.

Structure of the extracted tail:

  .L6x_done_entry:                         ; pc + 0x0
      vpxor   16(%rsp), %xmm8, %xmm8       ; fold prior-iter ghash-lo
      vpxor   %xmm4, %xmm8, %xmm8          ; fold prior-iter karatsuba residue

  .L6x_exit:                               ; identical semantics; keep label
      ; 6-way GHASH Horner fold consuming sp+32..sp+112 (last-iter
      ; plaintext stash) and ymm9..14 (last-iter ciphertext lanes) plus
      ; carry reductions at 16(%r11) / 128-32(%r9) etc.
      ; 6 ciphertext stores at -96(%rsi)..-16(%rsi) interleaved.
      ; Terminates with the final polynomial reduction, bswap, and
      ; vmovdqu %xmm8, (%r12) tag write.

ABI expected at entry:
  %rsi     = optr + 96*iter_count (advanced by the bulk loop's final iter)
  %rdi     = iptr + 96*iter_count
  %rcx     = key schedule - 128
  %r9      = Htable + 32
  %r8      = counter-block output
  %r11     = constants (bswap at 0(%r11); reduction at 16(%r11); +1 at 32(%r11))
  %rbp     = original rsp + saved GPRs; 16(%rbp) holds tag-output pointer
  %rsp     = sptr (stack frame carrying 16(%rsp) ghash-lo stash,
                   32..112(%rsp) last-iter plaintext stash)
  ymm4, ymm7, ymm8 = last-iter Karatsuba accumulator halves + residue
  ymm9..ymm14     = last-iter 6 ciphertext lanes (post-vaesenclast,
                    pre-bswap / pre-store)
  ymm15            = k0 (round-0 key)

Exit state:
  memory at (output_tag_ptr) = nist_ghash h ... (the final tag)
  memory at -96(%rsi)..-16(%rsi) = 6 ciphertext blocks from the last
                                   iter (already encoded in ct_preserved
                                   via M8's post at j ∈ {6*(iter_count-1)
                                   .. 6*iter_count-1}).

Known gap w.r.t. M8's post (2026-05-12): M8 does NOT pin ymm4/7/8/9..14
or sp+16 at exit, and the M7 extractor dropped the `movbeq/movq` stash
plumbing that writes sp+32..sp+112.  So a standalone M9 against the
current M7/M8 is vacuous.  See the Stage-B3-enrichment plan.
"""

import sys
from pathlib import Path

SOURCE_START = 618   # .L6x_done__... label line
SOURCE_END = 799     # vmovdqu %xmm8, (%r12)

# The label at 618 and the `jmp .Lexit` at 622 are dropped; both target
# lines become unconditional fall-through.
DROP_LINES = {618, 622, 623}

# Scalar fallbacks on the tail's straight-line path.  `movq 16(%rbp), %r12`
# at line 797 is kept — it is the tag-output-pointer load.
SCALAR_DROP = set()


def is_simd_or_keeper(line: str) -> bool:
    t = line.strip()
    if not t or t.startswith("//") or t.startswith("#") or t.startswith("/*"):
        return False
    if t.endswith(":"):
        return False
    if t.startswith(".align") or t.startswith(".size") or t.startswith(".cfi"):
        return False
    first = t.split(None, 1)[0]
    return first not in SCALAR_DROP


def main(argv):
    if len(argv) != 3:
        print("usage: extract_stitched_tail.py <encrypt.S> <output.S>",
              file=sys.stderr)
        return 2
    src = Path(argv[1]).read_text().splitlines()
    out = []
    out.append("// ===========================================================================")
    out.append("// Stitched 6-way GHASH finalisation tail, standalone-artefact form.")
    out.append("//")
    out.append("// Milestone 9 of the AES-GCM x86 verification plan.  Extracted from the")
    out.append("// .L6x_done__...  .Lexit__... blocks of aesni_gcm_encrypt.S (source lines")
    out.append("// 618-799) by tools/extract_stitched_tail.py: keep every SIMD instruction")
    out.append("// + the movq 16(%rbp),%r12 that loads the tag-output pointer.  The")
    out.append("// `jmp .Lexit` at line 622 is elided (fall-through into the same code).")
    out.append("//")
    out.append("// ABI at entry (inherited from the bulk loop's exit):")
    out.append("//   %rdi  = iptr + 96*iter_count         (unused by tail, consumed by")
    out.append("//                                         the enclosing function's")
    out.append("//                                         epilogue)")
    out.append("//   %rsi  = optr + 96*iter_count         (the 6 vmovdqu %xmmK,-N(%rsi)")
    out.append("//                                         stores write the last iter's")
    out.append("//                                         ciphertext lanes)")
    out.append("//   %rcx  = key schedule - 128")
    out.append("//   %r9   = Htable + 32")
    out.append("//   %r8   = counter-block output")
    out.append("//   %r11  = constants ptr (bswap/reduction/+1)")
    out.append("//   %rbp  = saved frame ptr; 16(%rbp) = tag-output pointer")
    out.append("//   %rsp  = sptr                         (16(%rsp) = ghash-lo stash;")
    out.append("//                                         32..112(%rsp) = last-iter")
    out.append("//                                         plaintext stash)")
    out.append("//   xmm4  = last-iter Karatsuba residue")
    out.append("//   xmm7  = last-iter Karatsuba accumulator high")
    out.append("//   xmm8  = last-iter Karatsuba accumulator low")
    out.append("//   xmm9..xmm14 = last-iter 6 ciphertext lanes (post-vaesenclast)")
    out.append("//   xmm15 = k0 (round-0 key)")
    out.append("//")
    out.append("// Exit state:")
    out.append("//   mem at 16(%rbp)-resolved tag ptr = final GHASH tag")
    out.append("//   mem at -96(%rsi)..-16(%rsi) = 6 ciphertext lanes (also subsumed by")
    out.append("//                                  the outer ct_preserved invariant)")
    out.append("// ===========================================================================")
    out.append("")
    out.append("        .text")
    out.append("        .globl  aesni_gcm_stitched_tail_core")
    out.append("        .type   aesni_gcm_stitched_tail_core,@function")
    out.append("        .align  16")
    out.append("aesni_gcm_stitched_tail_core:")
    out.append("")

    for lineno in range(SOURCE_START, SOURCE_END + 1):
        if lineno in DROP_LINES:
            continue
        line = src[lineno - 1]
        if not is_simd_or_keeper(line):
            continue
        insn = line.strip()
        # Rewrite `vxorps` -> `vpxor`: identical 128-bit semantics, but the
        # s2n-bignum decoder only recognises vpxor.  Same trick the inliner
        # uses for vmovups -> vmovdqu.
        if insn.startswith("vxorps"):
            insn = "vpxor" + insn[len("vxorps"):]
        out.append(f"        {insn}")

    out.append("")
    out.append("        ret")
    out.append("        .size   aesni_gcm_stitched_tail_core,.-aesni_gcm_stitched_tail_core")
    out.append("")

    Path(argv[2]).write_text("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
