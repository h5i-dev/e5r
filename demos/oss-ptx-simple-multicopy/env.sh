#!/usr/bin/env bash
export E5R_OSS_SCRATCH=${E5R_OSS_SCRATCH:-/mnt/scratch/e5r-oss-ptx}
export CARGO_TARGET_DIR="$E5R_OSS_SCRATCH/cargo"
export CARGO_BUILD_JOBS=2
export LEAN_NUM_THREADS=2
export CUPY_CACHE_DIR="$E5R_OSS_SCRATCH/cache/cupy"
export CUDA_CACHE_PATH="$E5R_OSS_SCRATCH/cache/cuda"
export TMPDIR="$E5R_OSS_SCRATCH/tmp"
export LD_LIBRARY_PATH="$E5R_OSS_SCRATCH/venv/lib/python3.12/site-packages/nvidia/cuda_nvrtc/lib:$E5R_OSS_SCRATCH/venv/lib/python3.12/site-packages/nvidia/cuda_runtime/lib:${LD_LIBRARY_PATH:-}"
mkdir -p "$TMPDIR" "$CUPY_CACHE_DIR" "$CUDA_CACHE_PATH"
