#!/bin/bash
# Build a DMTCP checkpoint with s2n-bignum x86 base PLUS the AES-GCM
# dependency stack (karatsuba_pmul, polyval_ghash, ghash_nist_bridge,
# fips197, gcm) pre-loaded.  Mirrors make-s2n-checkpoint.sh but
# targets the x86 checkpoint and layers `needs` calls for the AES
# specs on top of x86/proofs/base.ml.
#
# Note: hol.sh has HOLLIGHT_DIR baked in at build time, so HOLDIR
# here MUST be the path hol.sh was built for (typically
# /home/ubuntu/workspace/whole-proofs/hol-light on this host).  The
# S2N_BIGNUM_DIR can be any in-tree s2n-bignum checkout — the
# load_path will be patched at checkpoint-create time.  The resulting
# checkpoint lives at $HOLDIR/hol-s2n-x86-aes.ckpt and is invoked via:
#
#   HOL_LIGHT_DIR=$HOLDIR holctl start --name <n> --checkpoint s2n-x86-aes
#
# (Even if HOLDIR matches the holctl default, the checkpoint is
# named s2n-x86-aes to distinguish it from the base s2n-x86.)
#
# Usage:
#   HOL_LIGHT_DIR=/path/to/hol-light S2N_BIGNUM_DIR=/path/to/s2n-bignum \
#       bash make-s2n-x86-aes-checkpoint.sh
#   or: nohup bash make-s2n-x86-aes-checkpoint.sh &> /tmp/s2n-x86-aes-ckpt.log &

set -euo pipefail

HOLDIR="${HOL_LIGHT_DIR:?Set HOL_LIGHT_DIR=/path/to/hol-light}"
S2NDIR="${S2N_BIGNUM_DIR:?Set S2N_BIGNUM_DIR=/path/to/s2n-bignum}"
CKPT_NAME="hol-s2n-x86-aes"
CKPT_DIR="${HOLDIR}/${CKPT_NAME}.ckpt"
DONE_MARKER="/tmp/s2n-x86-aes-ckpt-done"

export PATH="$HOME/.local/bin:$PATH"

echo "=== Starting $CKPT_NAME checkpoint build at $(date) ==="
echo "    HOLDIR=$HOLDIR"
echo "    S2NDIR=$S2NDIR"
rm -f "$DONE_MARKER"
rm -rf "$CKPT_DIR" "${HOLDIR}/${CKPT_NAME}"

cd "$HOLDIR"
eval $(opam env --switch . 2>/dev/null) || true

FIFO=$(mktemp -u --suffix=".hol_stdin")
mkfifo "$FIFO"

# Hold FIFO open until checkpoint files appear, then close to let everything exit
(
  exec 3>"$FIFO"
  while true; do
    if [ -f "$CKPT_DIR/dmtcp_restart_script.sh" ] && \
       ls "$CKPT_DIR"/ckpt_ocamlrun_*.dmtcp 1>/dev/null 2>&1; then
      sleep 2  # let dmtcp finish writing
      break
    fi
    sleep 2
  done
  exec 3>&-
) &
KEEPER_PID=$!

# Init OCaml string:
#   - set load_path to the AES-GCM s2n-bignum tree
#   - load x86/proofs/base.ml (existing s2n-x86 baseline)
#   - leave gcm_run_kats at its default (false) so gcm.ml loads quickly
#   - needs gcm.ml (for fips197 + GCM spec), ghash_nist_bridge.ml (for
#     nist_ghash + POLYVAL bridge — transitively loads polyval_ghash
#     and polyval), and karatsuba_pmul.ml explicitly (it's not in the
#     `needs` chain of the other two, but Milestone 1+'s
#     VPCLMULQDQ-bridge work wants PMUL_KARATSUBA and related lemmas)
INIT_STMT="load_path := \"${S2NDIR}\" :: !load_path; \
needs \"x86/proofs/base.ml\"; \
needs \"common/gcm.ml\"; \
needs \"common/karatsuba_pmul.ml\"; \
needs \"common/ghash_nist_bridge.ml\""

setsid bash make-checkpoint.sh "$CKPT_NAME" "$INIT_STMT" <"$FIFO" 2>&1

if [ -f "$CKPT_DIR/dmtcp_restart_script.sh" ] && \
   ls "$CKPT_DIR"/ckpt_ocamlrun_*.dmtcp 1>/dev/null 2>&1; then
  echo "SUCCESS" > "$DONE_MARKER"
  echo "=== Checkpoint created successfully at $(date) ==="
  ls -lh "$CKPT_DIR"
else
  echo "FAILED" > "$DONE_MARKER"
  echo "=== Checkpoint FAILED at $(date) ==="
  ls -lh "$CKPT_DIR" 2>/dev/null
  exit 1
fi

kill $KEEPER_PID 2>/dev/null || true
rm -f "$FIFO"
