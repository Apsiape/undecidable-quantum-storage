#!/usr/bin/env bash
# Builds the library and runs every check from this directory:
#   Mathlib cache, build, official comparator (sandboxed; checks all 54 theorems against
#   Challenge.lean, the permitted axioms, and the nanoda and Lean kernels), axiom audit,
#   fresh exports, leanchecker and nanoda replays, and the secondary export comparison.
# Each step must succeed; "ALL CHECKS PASS" is printed only if every step passed.
# Needs the Lean 4.35.0 toolchain (lean, lake, leanexport, leanchecker, nanoda_bin), git, python3
# and bubblewrap (`bwrap` on PATH or COMPARATOR_BWRAP). Output: $CHECK_OUT (default ./check-output).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
OUT="${CHECK_OUT:-$ROOT/check-output}"
mkdir -p "$OUT"
BIN="$(lean --print-prefix)/bin"
STATUS="$OUT/status.txt"
: > "$STATUS"
fail() { echo "CHECK FAIL: $1" | tee -a "$STATUS"; exit 1; }
run() {  # run <label> <logfile> <command...>
  local label=$1 log=$2
  shift 2
  local start rc=0
  start=$(date +%s)
  "$@" > "$log" 2>&1 || rc=$?
  echo "$label: exit $rc, $(( $(date +%s) - start )) s" | tee -a "$STATUS"
  if [ "$rc" -ne 0 ]; then tail -n 20 "$log"; fail "$label"; fi
}
run "lake exe cache get" "$OUT/cache-get.log" lake exe cache get
run "lake build" "$OUT/build.log" lake build
run "lake comparator" "$OUT/comparator.log" lake comparator --config comparator.json
grep -q "Your solution is okay!" "$OUT/comparator.log" || fail "comparator verdict line missing"
run "axiom audit" "$OUT/axiom-audit.log" lake env lean -j1 Flagship1D/Audit.lean
n_print=$(grep -c "^#print axioms" Flagship1D/Audit.lean)
n_audit=$(grep -c "depends on axioms" "$OUT/axiom-audit.log")
[ "$n_audit" -eq "$n_print" ] || fail "axiom audit printed $n_audit of $n_print lines"
while read -r t; do
  grep -qF "'$t' depends on axioms" "$OUT/axiom-audit.log" || fail "axiom audit has no line for $t"
done < scripts/targets.txt
if grep "depends on axioms" "$OUT/axiom-audit.log" \
    | sed -e 's/.*\[//' -e 's/\]//' | tr ',' '\n' | sed 's/ //g' \
    | grep -v -x -e propext -e Classical.choice -e Quot.sound | grep -q .; then
  fail "axiom audit found a non-standard axiom"
fi
run "export Challenge" "$OUT/export-challenge.log" scripts/export.sh Flagship1D.Challenge "$OUT/Challenge.ndjson"
run "export Solution" "$OUT/export-solution.log" scripts/export.sh Flagship1D.Solution "$OUT/Solution.ndjson"
run "leanchecker" "$OUT/leanchecker.log" "$BIN/leanchecker" --from-export "$OUT/Solution.ndjson"
grep -q "accepts the solution" "$OUT/leanchecker.log" || fail "leanchecker verdict line missing"
cat > "$OUT/nanoda.json" <<JSON
{
  "use_stdin": false,
  "export_file_path": "$OUT/Solution.ndjson",
  "num_threads": 1,
  "nat_extension": true,
  "string_extension": true,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true
}
JSON
run "nanoda" "$OUT/nanoda.log" "$BIN/nanoda_bin" "$OUT/nanoda.json"
run "secondary export comparison" "$OUT/secondary-check.log" \
  python3 -I -B scripts/compare_exports.py "$OUT/Challenge.ndjson" "$OUT/Solution.ndjson" scripts/targets.txt
run "export checker self-test" "$OUT/compare-selftest.log" python3 -I -B scripts/test_compare_exports.py
(cd "$OUT" && sha256sum Challenge.ndjson Solution.ndjson) > "$OUT/export-digests.txt"
echo "ALL CHECKS PASS" | tee -a "$STATUS"
