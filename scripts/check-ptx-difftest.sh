#!/usr/bin/env bash
# Differential test of the PTX instruction semantics against a real GPU
# (docs/verification-ptx.md, "Differential testing").
#
# 1. difftest/gen.py writes one kernel per instruction form of the subset and
#    the launches with their input bytes (fixed seed).
# 2. gpurun runs every launch on the GPU twice: from the PTX text (driver JIT)
#    and from a ptxas cubin.
# 3. ptxdiff runs the same launches with the Lean definitions themselves
#    (Ptx.Semantics.stepMem, compiled by Lean).
# 4. The interpreter of e5r-ptx runs them too. All four outputs must be identical byte for byte. Each misaligned-access
#    launch must fault in the model and be refused by the GPU.
#
# Needs a CUDA GPU, the driver, nvcc's ptxas and gcc. Without a GPU it exits 77
# (skipped) instead of passing.
set -euo pipefail
cd "$(dirname "$0")/.."
root=verification/ptx
cuda=${CUDA_HOME:-/usr/local/cuda}
ptxas_bin=${PTXAS:-$cuda/bin/ptxas}
if ! command -v nvidia-smi >/dev/null || ! nvidia-smi -L >/dev/null 2>&1 || [[ ! -x $ptxas_bin ]]; then
  echo "difftest: no GPU or no ptxas, skipped" >&2
  exit 77
fi
if [[ -z "${E5R_VERIFY:-}" ]]; then
  CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}" cargo build --release -p e5r-verify
  E5R_VERIFY=./target/release/e5r-verify
fi
out=${DIFFTEST_OUT:-$(mktemp -d)}
mkdir -p "$out"
python3 $root/difftest/gen.py "$out"
"$ptxas_bin" -arch=sm_86 "$out/diff.ptx" -o "$out/diff.cubin"
gcc -O2 -Wall -o "$out/gpurun" $root/difftest/gpurun.c -I"$cuda/include" -lcuda
"$E5R_VERIFY" ptx export --namespace Diff.Kernels --name difftest/diff.ptx "$out/diff.ptx" \
  >$root/Diff/Kernels.lean
(cd $root && LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} lake build ptxdiff -q)

"$out/gpurun" "$out/diff.ptx" "$out/cases.txt" >"$out/gpu-jit.txt"
"$out/gpurun" "$out/diff.cubin" "$out/cases.txt" >"$out/gpu-cubin.txt"
$root/.lake/build/bin/ptxdiff "$out/cases.txt" >"$out/model.txt"
# the untrusted interpreter the counterexample search uses, on the same cases
"$E5R_VERIFY" ptx run --cases "$out/cases.txt" "$out/diff.ptx" >"$out/interp.txt"
n=$(wc -l <"$out/cases.txt")
for g in gpu-jit gpu-cubin interp; do
  if [[ $(wc -l <"$out/$g.txt") -ne $n ]] || ! cmp -s "$out/$g.txt" "$out/model.txt"; then
    python3 - "$out/$g.txt" "$out/model.txt" "$out/forms.txt" <<'EOF' >&2
import sys
g, m, f = (open(p).read().splitlines() for p in sys.argv[1:])
forms = dict(l.split("\t", 1) for l in f)
bad = [(a, b) for a, b in zip(g, m) if a != b]
for a, b in bad[:10]:
    k = a.split()[1]
    print(f"difftest: {k} ({forms.get(k)}): gpu {a[:120]} model {b[:120]}")
print(f"difftest: {len(bad)} of {len(m)} launches differ, {len(g)} gpu lines")
EOF
    exit 1
  fi
done
echo "difftest: $n launches, $(grep -c . "$out/forms.txt") kernels: model = GPU (JIT) = GPU (ptxas cubin) = interpreter, byte for byte"

faults=0
while read -r line; do
  k=$(cut -d' ' -f2 <<<"$line")
  printf '%s\n' "$line" >"$out/one.txt"
  model=$($root/.lake/build/bin/ptxdiff "$out/one.txt")
  set +e
  gpu=$("$out/gpurun" "$out/diff.ptx" "$out/one.txt" 2>/dev/null)
  rc=$?
  set -e
  if [[ $model != "fault $k" || $rc -eq 0 || $gpu != "error $k "* ]]; then
    echo "difftest: $k: model '$model', gpu '$gpu' (exit $rc)" >&2
    exit 1
  fi
  faults=$((faults + 1))
done <"$out/faults.txt"
echo "difftest: $faults misaligned launches: model faults, GPU refuses ($(cut -d' ' -f3 <<<"$gpu"))"
nvidia-smi --query-gpu=name,driver_version --format=csv,noheader
"$ptxas_bin" --version | tail -1
