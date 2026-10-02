#!/bin/sh
# Restore the witness files (lean/data/<key>/w*.txt or witnesses.txt) from data/witnesses/*.tar.xz.
# The Lean instances read them with include_str, so this must run before `lake build`
# (and before verifier/f038_a4_audit.py, which checks their SHA-256 against each MANIFEST).
set -e
cd "$(dirname "$0")/.."
for a in data/witnesses/*.tar.xz; do
  xz -dc "$a" | tar -C lean/data -xf -
  echo "unpacked $(basename "$a" .tar.xz)"
done
