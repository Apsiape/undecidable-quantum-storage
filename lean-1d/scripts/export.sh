#!/usr/bin/env bash
# Exports the closure of the 43 target theorems (plus the kernel's primitive constants, as the
# comparator does) from a built module, using the exporter bundled with the Lean toolchain.
# usage: scripts/export.sh <Module> <outfile>
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
MOD=$1
OUT=$2
BIN="$(lean --print-prefix)/bin"
BUILTINS=(Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub
  Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft
  Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam
  autoParam semiOutParam outParam)
mapfile -t TARGETS < scripts/targets.txt
lake env "$BIN/leanexport" "$MOD" -- "${TARGETS[@]}" "${BUILTINS[@]}" > "$OUT"
[ -s "$OUT" ] || { echo "empty export: $OUT" >&2; exit 1; }
