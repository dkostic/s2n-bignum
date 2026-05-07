#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
"""
Inline private helper functions into public AES-GCM entry points.

The aws-lc file ``crypto/fipsmodule/aesni-gcm-x86_64.S`` defines two public
entry points (``aesni_gcm_encrypt`` / ``aesni_gcm_decrypt``) that invoke
three private helpers (``_aesni_ctr32_ghash_6x`` and ``_aesni_ctr32_6x``)
via ``call``.  The s2n-bignum proof infrastructure cannot verify
``call``-using code (single-entry / single-exit ``ensures`` contract; see
aes-gcm-x86-plan.md §1.1a), so we produce a version with the helpers
inlined into their call sites.

What this tool does, in one pass:

  1. Parse the input ``.S`` file into labelled blocks.
  2. For each ``call <helper>`` in a public entry point, copy the helper's
     body (from its entry label to its terminating ``ret``, exclusive),
     rewriting every local label ``.Lxxx`` to a fresh name
     ``.Lxxx__<entry>_<site>`` so labels stay unique after inlining.
  3. Delete the helper definitions (no longer reachable).
  4. Rewrite every ``vmovups`` mnemonic to ``vmovdqu``.  The two
     instructions are functionally identical for 128-bit unaligned moves
     and have identical cycle cost on Haswell+ Intel and all AMD Zen;
     the VEX encoding of ``vmovups`` is not in the s2n-bignum decoder
     while ``vmovdqu`` is.  See aes-gcm-x86-plan.md §§2.3, 3.1.

The output is a single-entry ``.S`` file per public function.  Callers
should verify the output assembles cleanly (``cc -c``) and passes the
aws-lc AES-GCM test vectors before trusting it for proof work.

Usage:
    inline_x86_calls.py INPUT.S OUTPUT_DIR

The tool writes ``OUTPUT_DIR/aesni_gcm_encrypt.S`` and
``OUTPUT_DIR/aesni_gcm_decrypt.S``.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass, field


# -----------------------------------------------------------------------------
# Helper symbols that should be inlined and removed.  Entry-point symbols that
# should be preserved as public functions (but have their calls inlined).
# -----------------------------------------------------------------------------

HELPERS = ("_aesni_ctr32_ghash_6x", "_aesni_ctr32_6x")
ENTRY_POINTS = ("aesni_gcm_encrypt", "aesni_gcm_decrypt")


# -----------------------------------------------------------------------------
# Line types.
# -----------------------------------------------------------------------------

RE_LABEL = re.compile(r"^(\.?[A-Za-z_][A-Za-z0-9_]*):\s*$")
RE_LOCAL_LABEL = re.compile(r"^(\.L[A-Za-z0-9_]+):\s*$")
RE_LOCAL_LABEL_REF = re.compile(r"(\.L[A-Za-z0-9_]+)")
RE_CALL = re.compile(r"^\s*call\s+([A-Za-z_][A-Za-z0-9_]*)\s*$")
RE_TYPE_DIRECTIVE = re.compile(r"^\.type\s+([A-Za-z_][A-Za-z0-9_]*)\s*,\s*@function\s*$")
RE_SIZE_DIRECTIVE = re.compile(r"^\.size\s+([A-Za-z_][A-Za-z0-9_]*)\s*,")
RE_FUNCTION_NAME = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):\s*$")
RE_VMOVUPS = re.compile(r"\bvmovups\b")

# "rep ret" encoded as .byte 0xf3,0xc3
RE_BYTE_RET = re.compile(r"^\s*\.byte\s+0xf3\s*,\s*0xc3\s*$")


@dataclass
class Function:
    """A sliced view of an assembly file's function, named by its public label."""
    name: str
    # Index range in the original lines list, [start_idx, end_idx) where
    #   start_idx points at the first line of the function body (i.e. the
    #     line AFTER the "name:" label; the ".type" directive and ".align"
    #     sit before the label).
    #   end_idx points at the line AFTER the terminating ret / last body
    #     instruction (exclusive).  We place it just BEFORE ".cfi_endproc".
    body_start: int = 0
    body_end: int = 0
    # Index of the ".type name,@function" line (for deletion / keeping).
    type_line: int = -1
    # Index of the "name:" label line.
    label_line: int = -1
    # Index of ".cfi_startproc" and ".cfi_endproc" if present.
    cfi_start_line: int = -1
    cfi_end_line: int = -1
    # Index of ".size name,.-name" if present.
    size_line: int = -1
    # Indices of call instructions to private helpers inside this function.
    #   [(call_line_idx, helper_name), ...]  in source order.
    helper_calls: list = field(default_factory=list)


# -----------------------------------------------------------------------------
# Source parsing
# -----------------------------------------------------------------------------


def parse_functions(lines: list[str]) -> dict[str, Function]:
    """Slice the file into functions keyed by their public label name.

    We key off the .type <name>,@function directive (present for every
    public/private function in the aws-lc-generated AES-GCM file).
    """
    funcs: dict[str, Function] = {}
    pending_types: dict[int, str] = {}
    for i, line in enumerate(lines):
        m = RE_TYPE_DIRECTIVE.match(line.strip())
        if m:
            pending_types[i] = m.group(1)

    # For each type directive, find its matching label, body, and endings.
    for type_idx, name in pending_types.items():
        fn = Function(name=name, type_line=type_idx)
        # Label: next "name:" line.
        for j in range(type_idx + 1, len(lines)):
            if lines[j].strip() == f"{name}:":
                fn.label_line = j
                break
        else:
            continue

        # cfi_startproc: usually the very next non-blank line after the label.
        for j in range(fn.label_line + 1, len(lines)):
            stripped = lines[j].strip()
            if stripped == "":
                continue
            if stripped == ".cfi_startproc" or stripped.startswith(".cfi_startproc "):
                fn.cfi_start_line = j
                fn.body_start = j + 1
                break
            else:
                # No cfi_startproc; body starts at this line.
                fn.body_start = j
                break

        # cfi_endproc: appears before the next .size directive.
        # .size line: ".size <name>,.-<name>" — matches our function.
        for j in range(fn.body_start, len(lines)):
            stripped = lines[j].strip()
            m = RE_SIZE_DIRECTIVE.match(stripped)
            if m and m.group(1) == name:
                fn.size_line = j
                # body_end = line before .cfi_endproc (if present) or before .size.
                k = j - 1
                while k > fn.body_start and lines[k].strip() == "":
                    k -= 1
                if lines[k].strip().startswith(".cfi_endproc"):
                    fn.cfi_end_line = k
                    fn.body_end = k
                else:
                    fn.body_end = j
                break

        if fn.body_end == 0:
            # Malformed; skip.
            continue

        # Find call sites for the helpers.
        for j in range(fn.body_start, fn.body_end):
            m = RE_CALL.match(lines[j])
            if m and m.group(1) in HELPERS:
                fn.helper_calls.append((j, m.group(1)))

        funcs[name] = fn

    return funcs


_RET_MARKER = "###RET###\n"

# Match e.g. ``16+8(%rsp)`` or ``48+8(%rsp)`` — used by the helpers to refer
# to caller-relative stack slots across the ``call`` boundary (the caller
# stored at offset N, and `call` decremented RSP by 8, so the helper
# references N+8).  After inlining there is no pushed return address, so we
# rewrite these to plain ``N(%rsp)``.
RE_RSP_PLUS8 = re.compile(r"(\b\d+)\+8\(%rsp\)")


def rewrite_helper_stack_offsets(lines: list[str]) -> list[str]:
    """Rewrite ``N+8(%rsp)`` -> ``N(%rsp)`` in every line.

    The aws-lc private helpers (_aesni_ctr32_ghash_6x in particular) are
    written assuming they were reached via a ``call`` instruction that
    decremented RSP by 8.  Their references to caller-frame stack slots
    therefore use ``caller_offset + 8(%rsp)`` notation.  After inlining,
    no return address was pushed, so those references need the ``+ 8``
    removed.  We assume the assembler will literally subtract 0x8 from
    the displacement, yielding the original caller offset.
    """
    return [RE_RSP_PLUS8.sub(r"\1(%rsp)", line) for line in lines]


def helper_body_lines(
    lines: list[str],
    fn: Function,
) -> list[str]:
    """Extract the helper body lines from body_start to body_end, with the
    terminating ret (``.byte 0xf3,0xc3``) replaced by a ``###RET###`` sentinel
    that the caller (after label renaming) swaps for the real jmp.

    Both private helpers have exactly one ret.  In _aesni_ctr32_ghash_6x
    the ret is the final instruction, so the jmp is effectively a nop
    (falls through to exit_label placed just after the inlined block).
    In _aesni_ctr32_6x the ret sits in the middle of the body, with a
    ``.Lhandle_ctr32_2`` cold path after it; the fast path exits via the
    ret, and the cold path is reached only via a jc from earlier in the
    body.  After inlining, the cold path is physically right next to
    the fast-path exit; without rewriting the ret to a jmp, the fast
    path would fall through and re-enter the cold path, restarting the
    AES loop indefinitely.
    """
    ret_idx = -1
    for j in range(fn.body_start, fn.body_end):
        if RE_BYTE_RET.match(lines[j]):
            ret_idx = j
            break
    if ret_idx < 0:
        raise RuntimeError(f"Could not locate ret in helper {fn.name!r}")

    body = list(lines[fn.body_start:ret_idx])
    body.append(_RET_MARKER)
    body.extend(lines[ret_idx + 1:fn.body_end])
    return body


def rename_local_labels(
    body: list[str],
    suffix: str,
) -> list[str]:
    """Rewrite every .Lxxx (label definition OR reference) in `body` to
    .Lxxx__<suffix>, so helpers inlined at multiple call sites don't clash.

    Returns a new list of lines.  Does NOT touch non-.L labels (those are
    function names — we shouldn't be seeing them here).
    """
    out = []
    for line in body:
        new = RE_LOCAL_LABEL_REF.sub(
            lambda m: f"{m.group(1)}__{suffix}",
            line,
        )
        out.append(new)
    return out


def rewrite_vmovups(lines: list[str]) -> list[str]:
    """Replace every `vmovups` mnemonic with `vmovdqu`.  Preserves all
    surrounding whitespace and operands.  Does NOT touch any other mnemonic.
    """
    return [RE_VMOVUPS.sub("vmovdqu", line) for line in lines]


# -----------------------------------------------------------------------------
# Building the inlined output for one entry point.
# -----------------------------------------------------------------------------

def build_inlined(
    lines: list[str],
    funcs: dict[str, Function],
    entry_name: str,
) -> list[str]:
    """Produce the full inlined .S file (as a list of lines, newline-
    terminated) for the given public entry point.

    The output keeps the header comments / directives up to the first
    function, then emits ONLY the public entry point's function with all
    `call <helper>` substituted for the helper body.  Helper definitions
    and other entry points are NOT included.
    """
    entry = funcs[entry_name]
    out: list[str] = []

    # --- Header: everything before the first .type directive.
    first_type_idx = min(fn.type_line for fn in funcs.values())
    out.extend(lines[:first_type_idx])

    # --- Trimmed "Inlined by ..." banner comment.
    out.append("// --------------------------------------------------------------------------\n")
    out.append(f"// {entry_name}: monolithic, single-entry form.\n")
    out.append("//\n")
    out.append("// Produced by tools/inline_x86_calls.py from the aws-lc source at\n")
    out.append("// crypto/fipsmodule/aesni-gcm-x86_64.S.  Semantics preserved; the\n")
    out.append("// private helpers _aesni_ctr32_ghash_6x / _aesni_ctr32_6x have been\n")
    out.append("// spliced inline at each call site with per-site label renaming, and\n")
    # The inliner also rewrites vmovups -> vmovdqu below; avoid putting the
    # pre-rewrite mnemonic here or it will be edited along with the code.
    out.append("// every legacy-SSE-domain 128-bit unaligned move rewritten to vmovdqu\n")
    out.append("// (functionally equivalent; see aes-gcm-x86-plan.md §§2.3, 3.1).\n")
    out.append("// --------------------------------------------------------------------------\n")
    out.append("\n")

    # --- Directives right before the function label:
    # In the aws-lc .S file these are, in order:
    #   .globl  <name>
    #   .hidden <name>
    #   .type   <name>,@function
    #   .align  32
    #   <name>:
    # We want to keep the .globl/.hidden directives too since they mark the
    # symbol as exported.  Walk backwards from type_line to pick them up.
    k = entry.type_line - 1
    pre_directive_idxs: list = []
    while k >= 0:
        stripped = lines[k].strip()
        if (
            stripped.startswith(".globl")
            or stripped.startswith(".hidden")
            or stripped == ""
        ):
            pre_directive_idxs.insert(0, k)
            k -= 1
        else:
            break
    # Drop any leading blank lines (we emit our own banner).
    while pre_directive_idxs and lines[pre_directive_idxs[0]].strip() == "":
        pre_directive_idxs.pop(0)
    for j in pre_directive_idxs:
        out.append(lines[j])
    # --- .type, .align, label.
    out.append(lines[entry.type_line])
    # .align line sits between .type and the label.
    for j in range(entry.type_line + 1, entry.label_line):
        out.append(lines[j])
    out.append(lines[entry.label_line])
    if entry.cfi_start_line >= 0:
        # Include any blank/whitespace lines between label and cfi_startproc.
        for j in range(entry.label_line + 1, entry.cfi_start_line + 1):
            out.append(lines[j])

    # --- Body: walk the entry function, inlining call sites as we go.
    call_counts: dict[str, int] = {}
    body_idx = entry.body_start
    while body_idx < entry.body_end:
        line = lines[body_idx]
        m = RE_CALL.match(line)
        if m and m.group(1) in HELPERS:
            helper_name = m.group(1)
            helper = funcs.get(helper_name)
            if helper is None:
                raise RuntimeError(f"Helper {helper_name!r} called but not defined.")
            # Generate a unique per-call-site suffix and exit label.
            n = call_counts.get(helper_name, 0)
            call_counts[helper_name] = n + 1
            suffix = f"{entry_name}_{helper_name[1:]}_{n}"  # strip leading underscore
            exit_label = f".Lexit__{suffix}"
            body = helper_body_lines(lines, helper)
            body = rewrite_helper_stack_offsets(body)
            body = rename_local_labels(body, suffix)
            # Swap the ret marker for an actual jmp to the exit label AFTER
            # renaming, so the suffix doesn't get double-applied to the
            # jmp target.
            body = [f"\tjmp\t{exit_label}\n" if l == _RET_MARKER else l
                    for l in body]
            # Drop any leading .cfi directives from the helper body — they
            # refer to the callee's frame, which doesn't exist in the inlined
            # context.
            body = [l for l in body if not l.strip().startswith(".cfi_")]
            out.append(f"\t// ===== inlined {helper_name} call #{n} =====\n")
            out.extend(body)
            out.append(f"{exit_label}:\n")
            out.append(f"\t// ===== end inlined {helper_name} #{n} =====\n")
            body_idx += 1
        else:
            out.append(line)
            body_idx += 1

    # --- cfi_endproc + .size + trailing data (.Lbswap_mask etc.).
    if entry.cfi_end_line >= 0:
        out.append(lines[entry.cfi_end_line])
    if entry.size_line >= 0:
        out.append(lines[entry.size_line])

    # --- Trailing rodata (shared constants after the last function).
    # These appear after the last .size directive in the source, and are
    # referenced by .Lbswap_mask etc. within each function.  Include
    # everything from "last size directive + 1" to end of file.
    last_size_idx = max(fn.size_line for fn in funcs.values() if fn.size_line >= 0)
    out.extend(lines[last_size_idx + 1:])

    # --- Finally, rewrite vmovups -> vmovdqu across the entire output.
    out = rewrite_vmovups(out)

    return out


# -----------------------------------------------------------------------------
# Entry point.
# -----------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    parser.add_argument("input", help="aws-lc aesni-gcm-x86_64.S")
    parser.add_argument("output_dir", help="directory to write inlined .S files")
    args = parser.parse_args()

    with open(args.input, "r") as f:
        lines = f.readlines()

    funcs = parse_functions(lines)
    missing = [name for name in (*HELPERS, *ENTRY_POINTS) if name not in funcs]
    if missing:
        sys.exit(f"Missing expected symbols in {args.input}: {missing}")

    os.makedirs(args.output_dir, exist_ok=True)

    for entry_name in ENTRY_POINTS:
        inlined = build_inlined(lines, funcs, entry_name)
        out_path = os.path.join(args.output_dir, f"{entry_name}.S")
        with open(out_path, "w") as f:
            f.writelines(inlined)
        sys.stderr.write(f"wrote {out_path}\n")


if __name__ == "__main__":
    main()
