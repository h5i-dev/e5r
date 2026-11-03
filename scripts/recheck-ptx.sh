#!/usr/bin/env bash
# One command that rechecks everything the PTX verification claims
# (docs/verification/ptx.md, "Reproduce"):
#
#   1. parser, round trip, ptxas agreement and fuzz tests (cargo, release);
#   2. every Lean proof and refutation from scratch, and the axiom audit of
#      every Ptx.* declaration (scripts/check-lean-ptx.sh);
#   3. `e5r-verify ptx check` on every benchmark, against the verdict in
#      benchmarks/expected.txt;
#   4. the mutation controls (mutants/run.py): no mutant may be proved;
#   4b. the supplied-proof route (proofs/controls.sh): two supplied proofs
#      accepted, every negative control refused;
#   5. the GPU differential test (scripts/check-ptx-difftest.sh), skipped
#      with a note when there is no GPU;
#   6. the cross-check of the float rounding core against lean-ieee754
#      (scripts/check-ptx-ieee-crosscheck.sh), skipped with a note when its
#      Mathlib dependency has not been fetched.
#
# E5R_VERIFY=path skips the cargo build and test (CI passes its dev build).
# Lean runs with LEAN_NUM_THREADS=2 and a 10 GB cgroup cap unless overridden.
set -euo pipefail
cd "$(dirname "$0")/.."
root=verification/ptx
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
if [[ -z "${E5R_VERIFY:-}" ]]; then
  CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}" cargo test --release -p e5r-ptx -p e5r-verify -q
  CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}" cargo build --release -p e5r-verify
  export E5R_VERIFY=./target/release/e5r-verify
fi
echo "== Lean proofs and axiom audit"
./scripts/check-lean-ptx.sh | tail -3

echo "== ptx check on the benchmarks"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
fail=0
while read -r ptx spec want; do
  [[ -z $ptx || $ptx == \#* ]] && continue
  set +e
  "$E5R_VERIFY" ptx check "$root/benchmarks/$ptx" --spec "$root/benchmarks/specs/$spec" >"$out/r.json"
  rc=$?
  set -e
  got=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$out/r.json")
  printf '%-28s %-12s exit %d (want %s)\n' "$ptx" "$got" "$rc" "$want"
  [[ $got == "$want" ]] || fail=1
done <"$root/benchmarks/expected.txt"
((fail)) && { echo "recheck: a benchmark verdict changed" >&2; exit 1; }

echo "== mutation controls"
python3 $root/mutants/run.py "$E5R_VERIFY" "$out/mutants" | tail -1

echo "== supplied proofs and their negative controls"
$root/proofs/controls.sh "$E5R_VERIFY" | tail -1

echo "== GPU differential test"
set +e
./scripts/check-ptx-difftest.sh >"$out/diff.log" 2>&1
rc=$?
set -e
case $rc in
  0) grep "^difftest:" "$out/diff.log" ;;
  77) echo "skipped: no GPU on this machine" ;;
  *) cat "$out/diff.log" >&2; exit 1 ;;
esac
echo "== cross-check of the rounding core against lean-ieee754"
if [[ -d $root/../ptx-ieee-crosscheck/.lake/packages/mathlib/.lake/build ]]; then
  ./scripts/check-ptx-ieee-crosscheck.sh 2>&1 | grep -E "^axiom audit"
else
  echo "skipped: Mathlib not fetched (scripts/check-ptx-ieee-crosscheck.sh fetches it, about 8 GB)"
fi
echo "recheck: all PTX verification claims rechecked"
