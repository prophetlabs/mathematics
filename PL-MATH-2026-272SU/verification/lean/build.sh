#!/bin/zsh
# Compile every module in dependency order, then print the axioms of the main theorems.
# Uses the Mathlib build whose LEAN_PATH is stored in .leanpath (see README.md).
set -e
cd "$(dirname "$0")"
rm -rf build && mkdir -p build/OC
for mod in Basic ThmC Lemma1 Lemma2 Bound Prefix Closing Steps Main Edges Count; do
  echo "== OC/$mod"
  ./mk.sh "OC/$mod" 2>&1 | grep -E "error|sorry" && { echo "FAILED in OC/$mod"; exit 1; } || true
  [ -f "build/OC/$mod.olean" ] || { echo "FAILED: no build/OC/$mod.olean"; exit 1; }
done
env LEAN_PATH="$(cat .leanpath):$(pwd)/build" lean --root=. Check.lean
