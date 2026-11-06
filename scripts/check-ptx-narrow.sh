#!/usr/bin/env bash
# Narrow integer PTX: independent Python reference = GPU JIT = ptxas cubin
# = Rust interpreter = Lean semantics, including every output canary byte.
set -euo pipefail
cd "$(dirname "$0")/.."
cuda=${CUDA_HOME:-/usr/local/cuda}
ptxas_bin=${PTXAS:-$cuda/bin/ptxas}
if ! command -v nvidia-smi >/dev/null || ! nvidia-smi -L >/dev/null 2>&1 || [[ ! -x $ptxas_bin ]]; then
  echo "narrow: GPU or ptxas unavailable, skipped" >&2
  exit 77
fi
if [[ -z ${E5R_VERIFY:-} ]]; then
  CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-1} cargo build --release -p e5r-verify
  E5R_VERIFY=${CARGO_TARGET_DIR:-target}/release/e5r
fi
out=${NARROW_OUT:-$(mktemp -d)}
mkdir -p "$out"
python3 verification/ptx/difftest/narrow.py "$out"
"$ptxas_bin" -arch=sm_86 "$out/diff.ptx" -o "$out/diff.cubin"
gcc -O2 -Wall -o "$out/gpurun" verification/ptx/difftest/gpurun.c -I"$cuda/include" -lcuda
"$E5R_VERIFY" ptx export --namespace Diff.Kernels --name narrow.ptx "$out/diff.ptx" \
  >verification/ptx/Diff/Kernels.lean
(cd verification/ptx && LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1} lake build ptxdiff -q)
verification/ptx/.lake/build/bin/ptxdiff "$out/cases.txt" >"$out/model.txt"
"$E5R_VERIFY" ptx run --cases "$out/cases.txt" "$out/diff.ptx" >"$out/interp.txt"
# Hold the shared GPU lock and refuse every pre-existing compute process.
# This process creates no CUDA context itself; all existing PIDs are foreign.
python3 - "$out" <<'PY'
import fcntl
import pathlib
import subprocess
import sys
p = pathlib.Path(sys.argv[1])
with open('/mnt/scratch/e5r-gpu-benchmark.lock', 'w') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    foreign = subprocess.check_output(['nvidia-smi', '--query-compute-apps=pid', '--format=csv,noheader'], text=True).strip()
    if foreign:
        raise SystemExit('refusing GPU run: existing compute PIDs ' + foreign)
    for kind, module in [('gpu-jit', 'diff.ptx'), ('gpu-cubin', 'diff.cubin')]:
        with open(p / (kind + '.txt'), 'w') as output:
            subprocess.run([str(p / 'gpurun'), str(p / module), str(p / 'cases.txt')], stdout=output, check=True)
expected = (p / 'expected.txt').read_bytes()
for kind in ['gpu-jit', 'gpu-cubin', 'interp', 'model']:
    if (p / (kind + '.txt')).read_bytes() != expected:
        raise SystemExit(kind + ' differs from independent Python expected bytes')
print('narrow: all ' + str(len(expected.splitlines())) + ' launches match in Python, GPU JIT, ptxas cubin, Rust, and Lean')
PY
