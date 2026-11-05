#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
source demos/verified-packing/env.sh
case "${1:-proof}" in
  setup) exec bash demos/ptx-equivalence/run.sh setup ;;
  proof)
    "$E5R_VERIFY" ptx check "$here/edited.ptx" --spec "$here/equivalence.json" \
      --proof "$here/equivalence.lean" --keep "$E5R_DEMO_SCRATCH/accepted/stencil" \
      --timeout 900 --memory-mb 5120 --out "$here/results/proof.json"
    ;;
  test) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/experiment.py" ;;
  negative) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/negative.py" ;;
  benchmark) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/experiment.py" benchmark ;;
  profile) exec flock /mnt/scratch/e5r-gpu-benchmark.lock bash "$here/profile.sh" ;;
  report) exec python3 "$here/report.py" ;;
  coalesced|tiled|paired2)
    script=coalesced.py
    if [[ "$1" != coalesced ]]; then script="$1-experiment.py"; fi
    case "${2:-test}" in
      test) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/$script" ;;
      benchmark) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/$script" benchmark ;;
      profile) exec flock /mnt/scratch/e5r-gpu-benchmark.lock bash "$here/profile.sh" "$1" ;;
      report) exec python3 "$here/coalesced-report.py" ;;
      *) exit 64 ;;
    esac
    ;;
  *) echo 'usage: run.sh setup|proof|test|negative|benchmark|profile|report' >&2; exit 64 ;;
esac
