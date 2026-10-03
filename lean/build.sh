#!/bin/sh
# Build and verify the whole development.
#
# `lake env lean` refuses files outside its own root, so we borrow the Mathlib
# of an unrelated project (same toolchain, v4.30.0-rc2) and drive `lean`
# directly through `lake env sh`, putting our own .oleans on LEAN_PATH.
#
# A lakefile here would be tidier but would need its own Mathlib checkout —
# 7.1GB — which is not worth paying for build ergonomics alone. If this
# development ever becomes a standalone package, revisit.
#
# Usage: lean/build.sh [output-dir]      (default /tmp/cf-oleans)
set -e

MATHLIB_PROJECT=${MATHLIB_PROJECT:-$HOME/git/experiments/waarnar/loop-experiment/lean}
SRC=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-/tmp/cf-oleans}

if [ ! -d "$MATHLIB_PROJECT/.lake/packages/mathlib" ]; then
  echo "no Mathlib build at $MATHLIB_PROJECT" >&2
  echo "set MATHLIB_PROJECT to a project with a built Mathlib on toolchain $(cat "$SRC/../lean-toolchain" 2>/dev/null || echo v4.30.0-rc2)" >&2
  exit 1
fi

mkdir -p "$OUT"

# Palindrome, Lagrange and Sturmian are mutually independent; Quadratic imports
# Palindrome, and SqrtN imports Palindrome, Lagrange and Sturmian.
for f in Palindrome Lagrange Sturmian Quadratic; do
  echo "--- $f.lean"
  cd "$MATHLIB_PROJECT" && lake env sh -c \
    "cd '$SRC' && LEAN_PATH=\$LEAN_PATH:'$OUT' lean -o '$OUT/$f.olean' $f.lean"
done

echo "--- SqrtN.lean"
cd "$MATHLIB_PROJECT" && lake env sh -c \
  "cd '$SRC' && LEAN_PATH=\$LEAN_PATH:'$OUT' lean SqrtN.lean"
