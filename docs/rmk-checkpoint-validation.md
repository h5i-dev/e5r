# Integrated RMK checkpoint validation

Integration base: `9bacb95` (support + ISA/encode review + exporter/UART).
The checkpoint source/job changes start at `d21b694`.

Validation on 2026-10-30, in the isolated `prepare/rmk-main` worktree:

* `cargo test --release -p e5r-verify -j 2`: **24 passed**, including tests
  against the supplied pinned RMK ELF.
* `cargo fmt --all -- --check`: **passed** (includes formatting an existing
  dashboard match).
* `cargo clippy --release --workspace --all-targets -j 2 -- -D warnings`:
  **passed**.
* `cargo-deny check`: **advisories, bans, licenses and sources passed** with
  the committed license policy. A temporary config copy set only the advisory
  database path to `/tmp/e5r-rmk-advisory-db`, because this machine's NFS home
  does not support its locking. Cargo also emitted a package-cache lock
  diagnostic; the checker exited 0.
* `cargo test --release --workspace --no-fail-fast -j 2`: **not green**:
  1,050 passed, 21 failed, 20 ignored across 116 test/doc-test targets.
  The failures are the missing-input/tool gates below, not accepted passes.
* `e5r-verify check .../rmk-checkpoint.json` **without `--resume`**:
  **`proved`**. All 110 modules compiled from source and all 110 replayed
  through `leanchecker` (220 stages; no resumed stages). The audit checked
  the 17 requested endpoints and four image-binding theorems. Only
  `propext`, `Classical.choice` and `Quot.sound` were reported.
* `e5r-verify verify-result .../checkpoint.json`: **current**, exit 0.
  The receipt binds the supplied ELF, board, job, Lean version, verifier
  binary and proof sources. Proof sources are at `0c75c31`; this validation
  commit adds only documentation and the receipt.

## Workspace test limitations

`./scripts/build-fixtures.sh` stopped because this host has no AArch64 cross
compiler. It also lacks clang and the LLVM command-line oracles. Removing the
empty directory created by that failed attempt avoided treating an empty
fixture directory as a built corpus; the full-suite figures above are from
that subsequent run.

| Failing target | Missing prerequisite |
| --- | --- |
| `e5r-analysis` / `jumptable_a64` | AArch64 system-library fixture builds |
| `e5r-api` / `classes` | C++/Microsoft ABI fixtures |
| `e5r-api` / `dataflow` | Dataflow fixtures |
| `e5r-arch` / `a64_logical_imm` | `llvm-mc` |
| `e5r-asm` / `oracle` | Disassembler oracle |
| `e5r-format` / `overlay` | Binary fixture corpus |
| `e5r-format` / `pdb` | PDB fixture corpus and `llvm-pdbutil` |

These seven test files have no changes relative to the integration's main
base, `a211e10`. The CI test job already installs the toolchains and builds
that corpus. **Its full suite must pass before merging**; local results do
not establish oracle-backed coverage. No tests were weakened or skipped to
make a green report. CI uses its existing dev/test profiles; all local Cargo
build, test and Clippy invocations used release.

## Proof integration

The aggregate replay initially caught a stale concrete UART witness: the
session extras invariant gained service/TX fields, but the witness still
constructed the old invariant. The witness RAM and constructor now include
those fields; no invariant or theorem precondition was weakened.

The encode check also exceeded the runner's memory limit when all ten
response values were reduced in one declaration. It now proves each response
separately and combines those proofs into the unchanged `enc_check` theorem.
All ten cases remain required; negative-control declaration expectations
follow the split.

The [fresh checkpoint receipt](../verification/rv32/Projects/rmk/results/checkpoint.json)
records 2258.0 seconds elapsed and a maximum observed child RSS of
7,808 MiB, within the job's 10,240 MiB cap.
Its SHA-256 is `141cf83453939a20808fd40da91fdc7a87258bbe996e20f77bd298ac5af321bc`.
The replay command is in [the checkpoint guide](rmk-checkpoint.md).
Historical receipts and incremental development runs are not substituted for
this result. The development replay was stopped after source compilation so
that the final run could start from source without `--resume`.

This validates the conditional component theorems listed in the guide;
`SessionSafe`, the false old Some contract, `TopicsNewContract` and R0 limits
remain exactly as documented. The local workspace test prerequisite failures
above still require a fixture-equipped CI run before merge.
