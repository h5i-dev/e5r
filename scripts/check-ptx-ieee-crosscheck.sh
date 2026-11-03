#!/usr/bin/env bash
# Build the cross-check of the PTX model's rounding core against lean-ieee754
# (verification/ptx-ieee-crosscheck, docs/verification/ptx.md) and run its
# axiom audit. lean-ieee754 is pinned at 529ed78 and needs Mathlib; the first
# run fetches it and Mathlib's prebuilt cache (about 8 GB under .lake/).
# Lean runs with LEAN_NUM_THREADS=2 under a 7 GB cgroup cap (override with
# PTX_LEAN_MEMORY) when systemd-run is available.
set -euo pipefail
cd "$(dirname "$0")/../verification/ptx-ieee-crosscheck"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
mem="${PTX_LEAN_MEMORY:-7G}"
cap=()
if command -v systemd-run >/dev/null && systemd-run --scope --quiet -p MemoryMax=1G true 2>/dev/null; then
  cap=(systemd-run --scope --quiet -p "MemoryMax=$mem" -p MemorySwapMax=0 --)
fi
if [[ ! -d .lake/packages/mathlib/.lake/build ]]; then
  lake exe cache get
fi
"${cap[@]}" lake build
"${cap[@]}" lake env lean Audit.lean
grep -n "^theorem" Crosscheck/*.lean | sed 's/ :.*//' 
