# e5r: Assembly-Level Formal Verification with Lean 4

e5r proves properties of the code a compiler actually emitted, such as NVIDIA
PTX kernels and RISC-V firmware binaries. Every proof is checked by the Lean 4
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

## Supported assembly

| Assembly | What is proved | Semantics checked against | Not yet | Docs |
| --- | --- | --- | --- | --- |
| NVIDIA PTX | Automatically: elementwise maps, block reductions and scans (shared memory, barriers), commutative atomics, bit-exact `.f32` maps. Other kernels in the subset: a hand-written proof checked by `--proof` | NVIDIA A10G, bit for bit | `exch`/`cas` atomics, float error bounds, float reductions, `.f64` maps, approximate instructions | [PTX](docs/verification-ptx.md) |
| RISC-V (RV32IMAC, HiFive1 Rev B) | Hand-written machine-code proofs of functions and regions | QEMU | A whole-firmware safety theorem | [firmware](docs/firmware-verification.md), [RMK](docs/rmk-checkpoint.md) |

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
