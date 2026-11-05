#!/usr/bin/env bash
# Source from scripts to keep all heavyweight state outside the worktree.
export E5R_DEMO_SCRATCH=${E5R_DEMO_SCRATCH:-/mnt/scratch/e5r-ptx-demo}
export CARGO_TARGET_DIR="$E5R_DEMO_SCRATCH/cargo"
export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export CUDA_CACHE_PATH="$E5R_DEMO_SCRATCH/cache/cuda"
export CUPY_CACHE_DIR="$E5R_DEMO_SCRATCH/cache/cupy"
export PIP_CACHE_DIR="$E5R_DEMO_SCRATCH/cache/pip"
export TMPDIR="$E5R_DEMO_SCRATCH/tmp"
mkdir -p "$TMPDIR"
export LD_LIBRARY_PATH="$E5R_DEMO_SCRATCH/venv/lib/python3.12/site-packages/nvidia/cuda_nvrtc/lib:$E5R_DEMO_SCRATCH/venv/lib/python3.12/site-packages/nvidia/cuda_runtime/lib:${LD_LIBRARY_PATH:-}"
export E5R_VERIFY="$CARGO_TARGET_DIR/release/e5r"
