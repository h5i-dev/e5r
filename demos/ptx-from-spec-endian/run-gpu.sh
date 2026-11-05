#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export SCRATCH=${SCRATCH:-/mnt/scratch/e5r-ptx-from-spec}
export CUDA_PATH=${CUDA_PATH:-/usr/local/cuda}
export LD_LIBRARY_PATH="$CUDA_PATH/lib64${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export CUPY_CACHE_DIR="$SCRATCH/cupy-cache"
if [[ ${1:-} == --wrapper-tests ]]; then
  shift
  exec "$SCRATCH/venv312/bin/python" "$here/test-wrapper.py" --scratch "$SCRATCH" "$@"
fi
exec "$SCRATCH/venv312/bin/python" "$here/gpu.py" --scratch "$SCRATCH" "$@"
