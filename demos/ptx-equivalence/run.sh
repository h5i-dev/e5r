#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
source demos/verified-packing/env.sh
case "${1:-proof}" in
  setup)
    export E5R_DEMO_REQUIREMENTS="$here/requirements.txt"
    exec bash demos/verified-packing/setup.sh
    ;;
  proof)
    "$E5R_VERIFY" ptx check "$here/optimized.ptx" --spec "$here/equivalence.json" \
      --proof "$here/equivalence.lean" --keep "$E5R_DEMO_SCRATCH/accepted/equivalence" \
      --timeout 600 --memory-mb 4096 --out "$here/results/proof.json"
    ;;
  test) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/validate.py" ;;
  negative) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/negative.py" ;;
  benchmark) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/benchmark.py" ;;
  report) exec "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/report.py" ;;
  *) echo 'usage: run.sh setup|proof|test|negative|benchmark|report' >&2; exit 64 ;;
esac
