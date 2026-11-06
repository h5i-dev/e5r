#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
repo="$E5R_OSS_SCRATCH/cuda-samples"
if [[ ! -d "$repo/.git" ]]; then
  git clone https://github.com/NVIDIA/cuda-samples.git "$repo"
fi
[[ $(git -C "$repo" rev-parse HEAD) == 0ec046d5e99d7214cc8e9fbac2cc1e66f3019878 ]] || git -C "$repo" checkout --detach 0ec046d5e99d7214cc8e9fbac2cc1e66f3019878
cmp "$repo/cpp/0_Introduction/simpleMultiCopy/simpleMultiCopy.cu" "$here/upstream/simpleMultiCopy.cu"
cmake -S "$repo/cpp/0_Introduction/simpleMultiCopy" -B "$E5R_OSS_SCRATCH/upstream-build" \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_CUDA_ARCHITECTURES=86 -DCMAKE_CUDA_FLAGS=--keep \
  -DCMAKE_INSTALL_PREFIX="$E5R_OSS_SCRATCH/upstream-install"
cmake --build "$E5R_OSS_SCRATCH/upstream-build" -j2 --verbose
# --keep preserves the normal build's PTX. Do not overwrite the frozen proof subject.
sha256sum "$E5R_OSS_SCRATCH/upstream-build/simpleMultiCopy.ptx"
nvcc -O3 -arch=sm_86 -std=c++17 --ptx "$here/tuned.cu" -o "$E5R_OSS_SCRATCH/tuned.ptx"
cmp "$E5R_OSS_SCRATCH/tuned.ptx" "$here/tuned.ptx"
ptxas -arch=sm_86 "$here/edited.ptx" -o "$E5R_OSS_SCRATCH/edited.cubin"
ptxas -arch=sm_86 "$here/tuned.ptx" -o "$E5R_OSS_SCRATCH/tuned.cubin"
