# Experiments

The work e5r grew out of, kept buildable and tested, but not the product and
not where effort goes first (see [docs/ROADMAP.md](../docs/ROADMAP.md)):

- **PTX**: proofs about NVIDIA PTX kernels (memory safety, race freedom,
  termination, functional correctness), automatic for maps, reductions,
  scans and atomics. [docs/ptx.md](docs/ptx.md).
- **RV32 firmware**: machine-code proofs of functions in RV32IMAC firmware for
  the HiFive1 Rev B and of the RMK checkpoint. [docs/firmware.md](docs/firmware.md),
  [docs/rmk-checkpoint.md](docs/rmk-checkpoint.md).

| Path | What |
| --- | --- |
| `crates/e5r-verify` | the `e5r-exp` binary (formerly `e5r`): `e5r-exp ptx check`, `e5r-exp check JOB`, ... |
| `crates/e5r-ptx` | the PTX parser and Lean exporter |
| `verification/ptx`, `verification/ptx-ieee-crosscheck`, `verification/rv32` | the Lean projects |
| `scripts/` | their check scripts; run from anywhere, they work in this directory |
| `docs/` | their documentation |

```bash
cargo build --release -p e5r-verify          # ../target/release/e5r-exp
experiment/scripts/recheck-ptx.sh            # rebuild and recheck every PTX result
```

The RV32 proofs use their own hand-written RV32I model, independent of the
core's RV64 model in `lean/E5R`.
