#!/usr/bin/env bash
# PTX verification (docs/verification/ptx.md): regenerate every kernel module
# from its .ptx with the release e5r-verify and refuse a stale committed copy,
# assemble every benchmark with ptxas when it is installed, build the Lean
# project from scratch, and audit the axioms of the main theorems.
#
#   scripts/check-lean-ptx.sh            check
#   scripts/check-lean-ptx.sh --update   rewrite the generated modules first
#
# E5R_VERIFY names an existing e5r-verify binary (CI builds its own, in the
# dev profile); otherwise this builds the release one (CONTRIBUTING.md: never
# target/debug on the maintainer's machine).
set -euo pipefail
cd "$(dirname "$0")/.."
root=verification/ptx
update=0
[[ "${1:-}" == "--update" ]] && update=1

if [[ -z "${E5R_VERIFY:-}" ]]; then
  CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}" cargo build --release -p e5r-verify
  E5R_VERIFY=./target/release/e5r-verify
fi
bin=$E5R_VERIFY

# benchmark path (under $root/benchmarks) and Lean module name
kernels=(
  "correct/vadd_nvcc.ptx VAddNvcc"
  "correct/saxpy.ptx Saxpy"
  "correct/sum.ptx Sum"
  "buggy/vadd_nobound.ptx VAddNoBound"
  "buggy/vadd_tid.ptx VAddTid"
  "buggy/vadd_sub.ptx VAddSub"
  "correct/reduce_nvcc.ptx ReduceNvcc"
  "correct/reduce_atomic_nvcc.ptx ReduceAtomicNvcc"
  "correct/scan_nvcc.ptx ScanNvcc"
)

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
stale=0
for k in "${kernels[@]}"; do
  read -r ptx mod <<<"$k"
  out="$root/Ptx/Kernels/$mod.lean"
  "$bin" ptx --namespace "Ptx.Kernels.$mod" --name "benchmarks/$ptx" "$root/benchmarks/$ptx" >"$tmp/$mod.lean"
  if ((update)); then
    cp "$tmp/$mod.lean" "$out"
  elif ! cmp -s "$tmp/$mod.lean" "$out"; then
    echo "stale: $out does not match benchmarks/$ptx (run with --update after review)" >&2
    stale=1
  fi
done
((stale)) && exit 1
echo "generated modules: ${#kernels[@]} current"

ptxas_bin="${PTXAS:-$(command -v ptxas || echo /usr/local/cuda/bin/ptxas)}"
if [[ -x "$ptxas_bin" ]]; then
  for f in "$root"/benchmarks/correct/*.ptx "$root"/benchmarks/buggy/*.ptx; do
    "$ptxas_bin" -arch=sm_86 "$f" -o "$tmp/out.cubin"
  done
  echo "ptxas: every benchmark assembles ($("$ptxas_bin" --version | tail -1))"
else
  echo "ptxas: not installed, assembly check skipped"
fi

# Lean memory and parallelism are capped: a Lean process was OOM-killed at
# 15 GB on the development machine. With systemd the cap is a cgroup limit
# (MemoryMax, no swap); without it only the thread count is capped.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
capped() {
  if command -v systemd-run >/dev/null && systemd-run --scope --quiet -p MemoryMax=64M true 2>/dev/null; then
    systemd-run --scope --quiet -p MemoryMax="${PTX_LEAN_MEMORY:-10G}" -p MemorySwapMax=0 -- "$@"
  else
    "$@"
  fi
}
cd "$root"
rm -rf .lake/build
capped lake build
capped lake env lean Audit.lean >"$tmp/axioms.txt"
cat "$tmp/axioms.txt"
grep -q "^axiom audit: [0-9]* declarations in Ptx.\*, standard axioms only" "$tmp/axioms.txt"
if grep -E "sorryAx|ofReduceBool|trustCompiler|_native" "$tmp/axioms.txt"; then
  echo "axiom audit: forbidden axiom" >&2
  exit 1
fi
bad=$(tr '\n' ' ' <"$tmp/axioms.txt" | grep -o "depends on axioms: \[[^]]*\]" |
  sed 's/.*\[//; s/\]//' | tr ',' '\n' | tr -d ' ' |
  grep -vxE "propext|Quot.sound|Classical.choice" || true)
if [[ -n "$bad" ]]; then
  echo "axiom audit: unexpected axioms: $bad" >&2
  exit 1
fi
n=$(grep -c "depends on axioms\|does not depend on any axioms" "$tmp/axioms.txt")
echo "axiom audit: every Ptx.* declaration and $n main theorems, standard axioms only"
