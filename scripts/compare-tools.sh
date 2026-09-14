#!/usr/bin/env bash
# r12e measured against the other reverse engineering tools on this machine.
#
# Not a test: it needs rizin, and Ghidra with a JVM if that is asked for. The
# numbers it prints are recorded in docs/benchmarks.md and docs/scorecard.md,
# and checked against scripts/bench-budget.json by scripts/check-bench-budget.py.
#
# Ghidra is opt-in: set GHIDRA_INSTALL_DIR to an installation and it joins the
# table. Without it the run says so rather than printing a two-tool table as
# though a third had never been wanted.
#
# Usage: scripts/compare-tools.sh [binary...]
#
#   scripts/compare-tools.sh                      # the default corpus
#   scripts/compare-tools.sh /bin/ls              # one binary
#   RUNS=1 scripts/compare-tools.sh               # the fast loop
#
# Env: R12E                the r12e executable (default target/release/r12e)
#      RIZIN               the rizin executable (default whatever is on PATH)
#      GHIDRA_INSTALL_DIR  a Ghidra installation; Ghidra is left out without one
#      OUT                 where the JSON goes (default target/bench-tools.json,
#                          which is gitignored; it is a measurement, not a baseline)
#      RUNS                runs per binary, fastest kept (default 3)
#      SLOW_RUNS           runs per binary for Ghidra, which is slow (default 2)
#      SKIP                comma-separated tools to leave out
#      TIMEOUT             seconds before one invocation is a timeout (default 1800)
#      APPEND              non-empty to merge into an existing OUT rather than
#                          replace it, for measuring a long corpus in parts
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

r12e=${R12E:-target/release/r12e}
rizin=${RIZIN:-rizin}
out=${OUT:-target/bench-tools.json}

[ -x "$r12e" ] || {
  echo "build first: cargo build --release" >&2
  exit 2
}

# Measure a copy, not the build output. A run takes tens of minutes and
# anything rebuilding this workspace meanwhile would replace the binary
# underneath it, so half the table would describe one build and half another
# with nothing in the output saying so. The copy is deleted on the way out and
# its hash is recorded with the numbers.
snapshot=$(mktemp -t r12e-bench-XXXXXX)
trap 'rm -f "$snapshot"' EXIT
cp "$r12e" "$snapshot"
chmod +x "$snapshot"
[ -x "$rizin" ] || command -v "$rizin" > /dev/null || {
  echo "no rizin: install it or set RIZIN. See docs/benchmarks.md." >&2
  exit 2
}
command -v readelf > /dev/null || {
  echo "no readelf: the symbol-table oracle needs binutils" >&2
  exit 2
}

ghidra=${GHIDRA_INSTALL_DIR:-}
if [ -n "$ghidra" ] && [ ! -x "$ghidra/support/analyzeHeadless" ]; then
  echo "GHIDRA_INSTALL_DIR=$ghidra has no support/analyzeHeadless" >&2
  exit 2
fi

targets=("$@")
if [ ${#targets[@]} -eq 0 ]; then
  # The default corpus: fixtures with symbols and their stripped twins, which
  # is what makes recall and false positives separable, plus the system
  # binaries the scorecard already uses, so the numbers are about real
  # programs and not only about toys.
  for f in hello.a64.O2 hello.a64.O2.stripped \
           hello.static.a64 hello.static.a64.stripped \
           hello.go hello.go.stripped \
           cpp-hierarchy.a64.O2.rtti cpp-hierarchy.a64.O2.rtti.stripped \
           panicky driver.x64.O2; do
    [ -f "fixtures/build/$f" ] && targets+=("fixtures/build/$f")
  done
  for f in /bin/ls /usr/bin/objdump /bin/bash \
           /usr/lib/aarch64-linux-gnu/libc.so.6 \
           /usr/lib/aarch64-linux-gnu/libstdc++.so.6 \
           /usr/lib/aarch64-linux-gnu/libcrypto.so.3; do
    [ -f "$f" ] && targets+=("$f")
  done
fi

# Not exec: the trap has to run and delete the snapshot.
python3 scripts/compare_tools.py \
  --r12e "$snapshot" \
  --r12e-name "$r12e" \
  --rizin "$rizin" \
  --ghidra "$ghidra" \
  --runs "${RUNS:-3}" \
  --slow-runs "${SLOW_RUNS:-2}" \
  --skip "${SKIP:-}" \
  --timeout "${TIMEOUT:-1800}" \
  ${APPEND:+--append} \
  --json "$out" \
  "${targets[@]}"
