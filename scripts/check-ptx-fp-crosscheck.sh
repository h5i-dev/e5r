#!/usr/bin/env bash
# Independent fp-lean arithmetic cross-check; production never fetches this dependency.
set -euo pipefail
cd "$(dirname "$0")/../verification/ptx-fp-crosscheck"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cap=()
if command -v systemd-run >/dev/null && systemd-run --scope --quiet -p MemoryMax=1G true 2>/dev/null; then
  cap=(systemd-run --scope --quiet -p "MemoryMax=${PTX_FP_LEAN_MEMORY:-4G}" -p MemorySwapMax=0 --)
fi
# A timeout also bounds first-time theorem builds. Override for slower hosts.
limit="${PTX_FP_TIMEOUT:-1200}"
timeout "$limit" "${cap[@]}" lake build
timeout "$limit" "${cap[@]}" lake env lean Audit.lean
timeout "$limit" "${cap[@]}" lake build ArithmeticAudit
timeout "$limit" "${cap[@]}" lake env lean ArithmeticAudit.lean
timeout "$limit" "${cap[@]}" lake exe crosscheck-runner
