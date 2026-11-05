#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
export SCRATCH=${SCRATCH:-/mnt/scratch/e5r-ptx-from-spec}
mkdir -p "$SCRATCH"
export CARGO_TARGET_DIR="$SCRATCH/cargo-target"
CARGO_BUILD_JOBS=2 cargo build --manifest-path "$repo/Cargo.toml" --release -p e5r-verify
# Copy source only. Every generated Lean file/build artifact stays on scratch.
python3 - "$repo/verification/ptx" "$SCRATCH/lean-project" <<'PY'
from pathlib import Path
import shutil, sys
src, dst = map(Path, sys.argv[1:])
shutil.copytree(src, dst, dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('.lake', '__pycache__'))
PY
if [[ ${1:-} != --proof-only ]]; then
  python3.12 -m venv "$SCRATCH/venv312"
  "$SCRATCH/venv312/bin/pip" install -r "$here/requirements.txt"
  "${NVCC:-/usr/local/cuda/bin/nvcc}" -O3 -std=c++17 -arch=sm_86 -cubin "$here/baseline.cu" -o "$SCRATCH/baseline.cubin"
  "${PTXAS:-/usr/local/cuda/bin/ptxas}" -arch=sm_86 "$here/endian_xor.ptx" -o "$SCRATCH/endian_xor.cubin"
fi
