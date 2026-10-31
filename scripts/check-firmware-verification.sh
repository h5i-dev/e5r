#!/usr/bin/env bash
# Recheck every binary-level firmware proof from source, with the pinned
# toolchains, and run the model's differential tests and negative controls.
# docs/firmware-verification.md describes what each step establishes.
#
# Needs on PATH: elan (Lean is selected by verification/rv32/lean-toolchain),
# rustup with toolchain 1.98.1 and the riscv32imac-unknown-none-elf target,
# riscv64 binutils (CROSS_COMPILE prefix, default riscv64-linux-gnu-),
# qemu-riscv32 and qemu-system-riscv32 8.2.2.
#
# E5R_VERIFY names an existing e5r-verify binary (CI builds its own, in the
# dev profile). Otherwise this builds the release one, as this checkout must.
set -euo pipefail
cd "$(dirname "$0")/.."
verify=verification/rv32

if [ -z "${E5R_VERIFY:-}" ]; then
  CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2} cargo build --release -p e5r-verify
  E5R_VERIFY=target/release/e5r-verify
fi
export E5R_VERIFY

# CI's workspace RUSTFLAGS (-D warnings) override the firmware's target
# rustflags, dropping -Tmemory.x and -Tlink.x. Build the pinned ELF with its
# checked-in Cargo configuration; encoded flags take precedence as well.
# Keep this after the host verifier build so that still uses CI's flags.
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS

python3 "$verify/tools/gen_board.py" --check
python3 "$verify/tools/gen_board.py" --check "$verify/boards/test/qemu-user-rv32.json"

results="$verify/build/results"
mkdir -p "$results"
status=0
for job in "$verify"/jobs/*.json; do
  name=$(basename "$job" .json)
  echo "== job $name"
  if "$E5R_VERIFY" check "$job" --out "$results/$name.json" > /dev/null; then
    "$E5R_VERIFY" verify-result "$results/$name.json"
  else
    status=1
    python3 -c "import json,sys; r=json.load(open(sys.argv[1])); print(r['status'], r.get('message',''))" \
      "$results/$name.json"
  fi
done

echo "== negative controls"
python3 "$verify/tools/test_job_controls.py" || status=1
echo "== instruction-level differential test against QEMU"
python3 "$verify/tools/run_isa_differential.py" ${ISA_SEEDS:-1 2 3 4} || status=1
echo "== whole-firmware replay against QEMU sifive_e"
python3 "$verify/tools/run_firmware_replay.py" || status=1

if [ "$status" -ne 0 ]; then
  echo "firmware verification: FAILED (see above)"
  exit 1
fi
echo "firmware verification: every job proved, every control and differential test passed"
