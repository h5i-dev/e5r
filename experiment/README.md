# Experiments

The work nocompiler grew out of, kept buildable and tested, but not the product and
not where effort goes first (see [docs/ROADMAP.md](../docs/ROADMAP.md)):

- **PTX**: proofs about NVIDIA PTX kernels (memory safety, race freedom,
  termination, functional correctness), automatic for maps, reductions,
  scans and atomics. [docs/ptx.md](docs/ptx.md).
- **RV32 firmware**: machine-code proofs of functions in RV32IMAC firmware for
  the HiFive1 Rev B and of the RMK checkpoint. [docs/firmware.md](docs/firmware.md),
  [docs/rmk-checkpoint.md](docs/rmk-checkpoint.md).

| Path | What |
| --- | --- |
| `crates/nocompiler-verify` | the `nocompiler-exp` binary (formerly `nocompiler`): `nocompiler-exp ptx check`, `nocompiler-exp check JOB`, ... |
| `crates/nocompiler-ptx` | the PTX parser and Lean exporter |
| `verification/ptx`, `verification/ptx-ieee-crosscheck`, `verification/rv32` | the Lean projects |
| `scripts/` | their check scripts; run from anywhere, they work in this directory |
| `docs/` | their documentation |

```bash
cargo build --release -p nocompiler-verify          # ../target/release/nocompiler-exp
experiment/scripts/recheck-ptx.sh            # rebuild and recheck every PTX result
```

The RV32 proofs use their own hand-written RV32I model, independent of the
core's RV64 model in `lean/NoCompiler`.
