# e5r: Assembly-Level Formal Verification with Lean 4

e5r proves properties of the code a compiler actually emitted: NVIDIA PTX
kernels and RISC-V firmware binaries. Every proof is checked by the Lean 4
kernel, so neither the compiler nor whoever wrote the code has to be trusted.

```bash
e5r-verify ptx check saxpy.ptx --spec saxpy.json    # proved, refuted, unsupported or unknown
e5r-verify ptx check k.ptx --spec k.json --proof Proof.lean   # check your own proof
e5r-verify check verification/rv32/jobs/hifive1-duty.json     # a firmware proof job
```

For a PTX kernel, `check` proves memory safety, race freedom, termination and
functional correctness for every launch, input and thread interleaving the
spec allows. If the proof fails, it looks for a counterexample and has Lean
replay it.

## What works

- **PTX:** elementwise maps, block reductions and scans with shared memory and
  barriers, commutative atomics, and bit-exact `.f32` maps are proved
  automatically. Anything else in the instruction subset can be proved by
  hand and checked with `--proof`. The Lean model agrees bit for bit with an
  NVIDIA A10G on every differential test.
- **RISC-V:** machine-code proofs for one board (HiFive1 Rev B), with the
  semantics checked against QEMU. A whole-firmware safety theorem is not
  proved yet.

Each doc lists what is not covered and why:
[PTX](docs/verification-ptx.md), [firmware](docs/firmware-verification.md),
[RMK](docs/rmk-checkpoint.md).

## Install

```bash
cargo build --release -p e5r-verify
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
./scripts/recheck-ptx.sh      # rebuild and recheck every PTX result
```

## The `e5r` toolkit

e5r also ships `e5r`, the binary analysis toolkit it grew out of:
disassembler, decompiler, binary differ. It is development infrastructure
here and is not an input to any proof. See [MANUAL.md](docs/MANUAL.md).

[ROADMAP](docs/ROADMAP.md) · [CONTRIBUTING](CONTRIBUTING.md) · Apache-2.0
