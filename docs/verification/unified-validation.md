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
E5R_REQUIRE_LEAN=1 cargo test --release -p e5r-verify -p e5r-ptx
cargo clippy --release -p e5r-verify --all-targets -- -D warnings
cp "$CARGO_TARGET_DIR/release/e5r" "$TMPDIR/validated-e5r"
export E5R_VERIFY="$TMPDIR/validated-e5r"
python3 scripts/test-unified-artifacts.py --bin "$E5R_VERIFY" --out "$TMPDIR/artifacts-new"
E5R_PTX_KEEP_BUILD=1 bash scripts/check-lean-ptx.sh
```

`--out` for artifact tests must not already exist. Repeat `--only` to select
cases, for example `--only ptx --only refuted --only supplied` for the final
supplemental run; omit it for all five artifact cases and legacy Lean-only replay.
On a fresh checkout run
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
python3 verification/ptx/mutants/run.py "$E5R_VERIFY" "$TMPDIR/mutants-new"
E5R_SUPPLIED_MEMORY_MIB=8192 bash verification/ptx/proofs/controls.sh "$E5R_VERIFY"
# Full existing suites, including optional execution oracles:
bash scripts/check-firmware-verification.sh
bash scripts/recheck-ptx.sh
```

The PTX CLI defaults to 6144 MiB per command. Generated benchmark checks used
5120 MiB, and the library/GPU scripts used 4096 MiB. Full supplied-proof replay
needs more memory: this run uses `E5R_SUPPLIED_MEMORY_MIB=8192` for the supplied
controls on a 16 GiB host. A 5120 MiB cap stopped valid supplied proofs and several
negative controls before their intended diagnostics; those runs do not establish
the controls. Run Lean-heavy suites serially and choose caps for available memory.
The runner samples aggregate RSS and can overshoot between samples.

## Coverage and executed evidence

The matrix records executed local checks. A skipped oracle does not establish
agreement. [Machine-readable evidence](evidence/unified-2026-11-05.json) retains
all mutant outcomes and reasons, benchmark verdicts, immutable verifier hashes
and raw log digests. It records success and freshness at execution time; later
source/tool edits require regeneration, as specified by the freshness contract.

| Check | Executed result |
| --- | --- |
| Shared Rust library, process-group limits, cancellation and policy controls | 38 passed |
| Shared integration: pinned Lean attacks, provenance, project locks, CLI signals | 4 passed |
| Existing PTX Rust parser, round-trip, fuzz, assembler and CLI suites | 18 passed, including all 7 CLI tests and actual ptxas agreement |
| Complete PTX model library and shared axiom audit | Passed, 5162 declarations, standard axioms only |
| A10G differential test | Passed: 1693 launches, 856 kernels including 311 float forms; JIT, cubin, Lean model and Rust interpreter identical |
| GPU negative controls | 10 misaligned launches faulted in the model and were refused by the GPU |
| Relocated source bundles | Flash, synthetic RAM image, cold PTX proof, checked-refutation and supplied-proof bundles passed; supplied repeated replay/freshness and legacy Lean-only replay passed |
| Firmware jobs | All three standard jobs proved and passed freshness checks on the immutable final suite binary |
| Firmware import, proof, input and memory controls | All 9 passed, including compiled multiline import rejection and memory exhaustion |
| All PTX benchmark verdicts and exit codes | Passed: 26 proved, 3 checked refutations, 2 unsupported |
| PTX mutation controls | 59 executed: 58 checked refutations, 0 proved, 1 unknown (non-advancing SAXPY index) |
| Supplied-proof controls and checker freshness | 2 proofs accepted, all 12 negative controls refused for their intended reasons; legacy exits and changed-checker staleness passed |
| Required-Lean CI mode | 4 shared integration tests passed; workflow YAML parsed locally, GitHub execution not claimed |
| Final default-parallel release Rust/clippy after all changes | 60 tests passed, required pinned Lean enabled; strict clippy and formatting passed |
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
Each validation stage used an immutable verifier and froze backend inputs for
the duration of its checks. The main backend suite and final supplemental suite
used the binary hashes recorded in the machine-readable evidence. The supplemental
suite uses the final `b502c84` implementation, with the completed test fixtures.
The final follow-up commit changes regression scripts, documentation and CI
cache metadata.

The non-advancing SAXPY mutant remains `unknown`. The suite establishes that
no tested mutant was proved; it does not establish complete refutation coverage
or a checked nontermination result for that mutant. Proof-stage timeouts in some
reduction/scan mutants were followed by independent checked counterexample
replay; only the replay justifies the recorded refutation.
