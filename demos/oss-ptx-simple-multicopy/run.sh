#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
source "$here/env.sh"
case "${1:-proof}" in
  setup)
    /usr/bin/python3.12 -m venv "$E5R_OSS_SCRATCH/venv"
    "$E5R_OSS_SCRATCH/venv/bin/pip" install -r "$here/requirements.txt"
    cargo build --release -p e5r-verify
    (cd verification/ptx && lake build Ptx proofcheck)
    ;;
  build-upstream) exec bash "$here/build-upstream.sh" ;;
  proof)
    "$CARGO_TARGET_DIR/release/e5r" ptx check "$here/edited.ptx" --spec "$here/equivalence.json" \
      --proof "$here/equivalence.lean" --keep "$E5R_OSS_SCRATCH/proof" \
      --timeout 600 --memory-mb 4096 --out "$here/results/proof.json"
    ;;
  negative) exec "$E5R_OSS_SCRATCH/venv/bin/python" "$here/negative.py" ;;
  test) exec "$E5R_OSS_SCRATCH/venv/bin/python" "$here/gpu.py" test ;;
  benchmark) exec "$E5R_OSS_SCRATCH/venv/bin/python" "$here/gpu.py" benchmark ;;
  *) echo 'usage: run.sh setup|build-upstream|proof|negative|test|benchmark' >&2; exit 64 ;;
esac
