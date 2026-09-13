#!/usr/bin/env bash
# r12e measured against DecBench, the third-party decompiler benchmark.
#
# Not a test: it needs a DecBench checkout, a Python virtualenv with decbench
# and its dependencies installed (angr, pyjoern, which downloads a 1.8 GB Joern
# on first use), a JDK, and the network the first time it compiles a corpus
# project from source. A single project at one optimization level takes tens of
# minutes, most of it Joern parsing the source. The numbers it prints are
# recorded by hand in docs/decbench.md and docs/scorecard.md.
#
# Usage: scripts/decbench.sh [results-tree] [project] [opt-levels] [decompilers]
#
#   scripts/decbench.sh                       # zlib, O0, r12e alone
#   scripts/decbench.sh /tmp/db zlib O0 r12e,angr,ghidra
#
# Env: DECBENCH_REPO   the DecBench checkout (default ~/Ref/decbench)
#      DECBENCH_VENV   virtualenv with decbench installed (default ~/.venvs/decbench)
#      R12E            the r12e executable (default target/release/r12e)
#      GHIDRA_INSTALL_DIR  needed only when ghidra is one of the decompilers
set -euo pipefail

tree=${1:-${DECBENCH_TREE:-/tmp/decbench-r12e}}
project=${2:-zlib}
opts=${3:-O0}
decs=${4:-r12e}

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
decbench=${DECBENCH_REPO:-$HOME/Ref/decbench}
venv=${DECBENCH_VENV:-$HOME/.venvs/decbench}
r12e=${R12E:-$repo/target/release/r12e}

[ -d "$decbench/decbench" ] || {
  echo "no DecBench checkout at $decbench; set DECBENCH_REPO" >&2
  exit 1
}
[ -x "$venv/bin/python" ] || {
  echo "no virtualenv at $venv; set DECBENCH_VENV. Create one with:" >&2
  # -e writes an egg-info into the source tree, so install from a copy and
  # leave the benchmark checkout as upstream shipped it.
  echo "  cp -a $decbench /tmp/decbench-work" >&2
  echo "  python3 -m venv $venv && $venv/bin/pip install -e /tmp/decbench-work" >&2
  exit 1
}
[ -x "$r12e" ] || {
  echo "build first: cargo build --release" >&2
  exit 1
}

# Importing the out-of-tree backend would otherwise leave a __pycache__ in
# scripts/, which is not ours to litter.
export DECBENCH_REPO="$decbench" R12E="$r12e" PYTHONDONTWRITEBYTECODE=1
python="$venv/bin/python"

# The corpus projects are built from their own upstream sources, so the first
# run downloads and builds; later runs find the tree and skip straight to
# decompiling.
for opt in ${opts//,/ }; do
  if [ -z "$(ls "$tree/$opt/$project/compiled"/*.i 2> /dev/null || true)" ]; then
    echo "== compiling $project at $opt (first run only) =="
    "$python" "$repo/scripts/decbench_run.py" --compile "$tree" "$project" "$opt"
  fi
done

echo "== decompiling and evaluating: $project $opts [$decs] =="
"$python" "$repo/scripts/decbench_run.py" "$tree" "$project" "$opts" "$decs"
