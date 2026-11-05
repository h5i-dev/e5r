# Unified verification validation

This report covers the shared-core migration on branch `unified-verification`.
The commands use release Rust builds, pinned Lean 4.35.0 and isolated scratch
outputs. Production dependencies remain Lean core and local shared support only.
The independent fp-lean evaluation has not been imported.

## Reproduce

```sh
export CARGO_TARGET_DIR=/mnt/scratch/e5r-unified-verification/cargo-target
export CARGO_BUILD_JOBS=2
export TMPDIR=/mnt/scratch/e5r-unified-verification
export LEAN_NUM_THREADS=1
cargo build --release -p e5r-verify
export E5R_VERIFY="$CARGO_TARGET_DIR/release/e5r"
cargo test --release -p e5r-verify -p e5r-ptx -- --test-threads=1
cargo clippy --release -p e5r-verify --all-targets -- -D warnings
python3 scripts/test-unified-artifacts.py --bin "$E5R_VERIFY" --out "$TMPDIR/artifacts-new"
E5R_PTX_KEEP_BUILD=1 bash scripts/check-lean-ptx.sh
```

`--out` for artifact tests must not already exist. On a fresh checkout run
`lake update` in each production Lean project once if a local Lake version
requires manifest initialization. The committed path manifests fetch no external
Lean packages. Build output can be redirected by symlinking each project's
`.lake/build` to its own directory on scratch storage before building.

Backend suites:

```sh
# These jobs need the pinned Rust 1.98.1 toolchain and RV32 target.
for job in verification/rv32/jobs/*.json; do
  "$E5R_VERIFY" check "$job" --out "$TMPDIR/$(basename "$job")"
done
python3 verification/rv32/tools/test_job_controls.py
# Full existing suites, including optional execution oracles:
bash scripts/check-firmware-verification.sh
bash scripts/recheck-ptx.sh
```

The PTX CLI defaults to 6144 MiB per command. For a shared host use
`--memory-mb 4096` on checks and `E5R_CHECK_MEMORY_MIB=4096` for the library
script; very small caps can stop a valid proof. Run Lean-heavy suites serially.
The runner samples aggregate RSS and can overshoot between samples.

## Coverage and executed evidence

Implementation milestone: final backend validation is in progress. A skipped
oracle does not establish agreement. The final report will replace pending rows.

| Check | Executed result |
| --- | --- |
| Shared Rust library, process-group limits, cancellation and policy controls | 37 passed |
| Shared integration: pinned Lean attacks, provenance, project locks, CLI signals | 4 passed |
| Existing release Rust suites before final hardening | 57 passed, including 7 PTX CLI tests and ptxas agreement |
| Complete PTX model library and shared axiom audit | Passed, 5162 declarations, standard axioms only |
| A10G differential test | Passed: 1693 launches, 856 kernels including 311 float forms; JIT, cubin, Lean model and Rust interpreter identical |
| GPU negative controls | 10 misaligned launches faulted in the model and were refused by the GPU |
| Relocated source bundles | Flash, RAM and cold PTX proof replay passed; final refutation/legacy replay rerun pending |
| Firmware jobs | Clamp and duty passed earlier; final three-job run pending |
| Firmware import, proof, input and memory controls | Final run pending |
| All PTX benchmark verdicts and exit codes | Final run pending |
| PTX mutation and supplied-proof controls | Final run pending |
| Final release Rust/clippy after all changes | Queued |
| Firmware QEMU differential/replay | Not executed: QEMU and RISC-V binutils unavailable |
| Optional RMK jobs and rounding cross-check project | Not executed: external fixtures/dependencies not prepared; production isolation retained |

Hardware run: NVIDIA A10G, driver 595.112.07, CUDA/ptxas 13.2. The run used the
shared process runner with a 4096 MiB sampled group RSS threshold and a 1800 s
wall threshold. The host is Amazon Linux 2023, Lean 4.35.0, host Rust 1.99.1;
firmware uses pinned Rust 1.98.1. No performance benchmark result is claimed.

The acceptance guard test was deliberately mutated to ignore command failure;
the test failed, and the guard was restored. Initial low-memory checker controls
stopped at their cap, and were rerun with sufficient memory. Source edits during
earlier checks produced explicit stale-input errors, which were never accepted.
Final suites use an immutable verifier and frozen backend inputs.
