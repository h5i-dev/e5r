#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
source demos/verified-packing/env.sh
case "${1:-proof}" in
  setup) exec bash demos/ptx-equivalence/run.sh setup ;;
  proof)
    exec "$E5R_VERIFY" ptx check "$here/edited.ptx" --spec "$here/equivalence.json" \
      --proof "$here/equivalence.lean" --keep "$E5R_DEMO_SCRATCH/accepted/stencil" \
      --timeout 900 --memory-mb 5120 --out "$here/results/proof.json"
    ;;
  scalar2-proof|paired2-proof|wide-branch-proof)
    name=${1%-proof}
    exec "$E5R_VERIFY" ptx check "$here/$name.ptx" --spec "$here/$name-equivalence.json" \
      --proof "$here/$name-equivalence.lean" --keep "$E5R_DEMO_SCRATCH/accepted/$name" \
      --timeout 900 --memory-mb 5120 --out "$here/results/$name-proof.json"
    ;;
  test) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/experiment.py" ;;
  negative) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/negative.py" ;;
  paired2-negative) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/negative.py" --paired2 ;;
  wide-branch-negative) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/negative.py" --wide-branch ;;
  benchmark) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/experiment.py" benchmark ;;
  profile) exec flock /mnt/scratch/e5r-gpu-benchmark.lock bash "$here/profile.sh" ;;
  report) exec python3 "$here/report.py" ;;
  cache) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/cache-regimes.py" ;;
  coalesced|tiled|paired2|paired2-pointer|wide-input|wide-branch)
    script=coalesced.py
    if [[ "$1" != coalesced ]]; then script="$1-experiment.py"; fi
    case "${2:-test}" in
      test) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/$script" ;;
      benchmark) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/$script" benchmark ;;
      profile)
        variant=$1
        if [[ "$variant" == paired2-pointer ]]; then variant=pointer2; fi
        if [[ $# -gt 2 ]]; then
          exec flock /mnt/scratch/e5r-gpu-benchmark.lock bash "$here/profile.sh" "$variant" "$3" "${4:-256}"
        fi
        exec flock /mnt/scratch/e5r-gpu-benchmark.lock bash "$here/profile.sh" "$variant"
        ;;
      report) exec python3 "$here/coalesced-report.py" ;;
      *) exit 64 ;;
    esac
    ;;
  *) echo 'usage: run.sh setup|proof|scalar2-proof|paired2-proof|wide-branch-proof|test|negative|paired2-negative|wide-branch-negative|cache|benchmark|profile|report, or VARIANT test|benchmark|profile|report' >&2; exit 64 ;;
esac
