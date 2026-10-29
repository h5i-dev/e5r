# R0 reproducibility receipt (RMK qemu-riscv-rynk), 2026-10-29

Upstream rmk `71556128fa72881fc35f0bf6c292d5e28ad9568d`, `examples/use_rust/qemu-riscv-rynk`,
Rust 1.98.1 (`RUSTUP_TOOLCHAIN`, no toolchain install or sync), `cargo build --release --locked`,
unchanged sources and `Cargo.lock`, private `CARGO_HOME`, all in `/dev/shm`.

| Build | Checkout path | Remap | ELF sha256 |
| --- | --- | --- | --- |
| pinned evidence (review recon) | `/dev/shm/e5r-isa-review-20261029T042314Z/rmk` | no | `f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30` |
| recon.sh recipe, fresh, twice | `/dev/shm/e5r-rmk-recon/rmk` | no | `e95989308a27531733b766913d2e2d01f88bfdebd0f1c044368d667c3bccc39a` (both) |
| remapped, path A | `/dev/shm/e5r-claude-r0/pathA/rmk` | yes | `2398cbc12541624612a357adecf6e7e3dca56b1a053bd2dbc01e04e1a2869ccc` |
| remapped, path B | `/dev/shm/e5r-claude-r0/elsewhere/pathB-longer/rmk` | yes | `9d147c645266830b636d336e7da87363ad6b99a157a74f47cf08ef7a0b2ae82c` |
| **canonical (build-canonical.sh), fresh, twice** | `/dev/shm/e5r-rmk-canonical/rmk` | yes | **`5871dceee5aa302705f4d3ef423ee6765951c0c7d314e996559641630bf16a06`** (both, identical bytes, no build path embedded) |

Diagnosis:
* Absolute source and registry paths are embedded in panic locations (`.rodata`); the pinned ELF holds
  `/dev/shm/e5r-isa-review-20261029T042314Z/{rmk,cargo-home}` 38 times. `--remap-path-prefix` removes them
  (`.rodata` 35,564 -> 33,972 bytes).
* With remapping, two checkout paths still give different `.text` (same size, 484 bytes in 4 runs, e.g.
  call offsets at 0x800018fc/0x80001940 into `KeyboardContext::with_combos` instances): functions are
  placed in a different order. Cargo's `-C metadata` hashes the absolute path of path dependencies (the
  rmk crates), which changes mangled names and with them the order. Remapping cannot change it; a fixed
  checkout path does.
* At one path the build is deterministic (two fresh recon-recipe builds agree; two fresh canonical builds
  agree).

Status:
* The canonical recipe is reproducible from a clean environment: R0's byte-identical criterion holds for
  it, at the stated fixed path. Path independence is not achieved (Cargo metadata), and is not claimed.
* `f39d833f` (all current RMK evidence: image job, replay, memmove proof) is reproducible only at its
  original path inside the review worker's scratch tree; not rebuilt here (that tree is in use).
  Dependency: the review worker can rebuild it there to confirm.
* Migration to `5871dcee…` is a separate step: addresses move (.rodata shrinks, .text layout differs),
  so the image job, the replay and every direct proof must be re-run or re-derived on it. Not done.
