# e5r: a formal-verification-friendly RISC-V

e5r is a profile of 64-bit RISC-V (RV64IM + Zba + Zbb, structured control
flow, a fixed stack discipline) designed so that machine code can be proved
correct in Lean 4, together with the Lean library the proofs are written in
and the tools that check binaries against the profile and export them for
proof.

Code in the profile is ordinary RISC-V: it runs unchanged on any RV64 Linux
machine or under qemu. Proofs are about the bytes of the binary, checked by
the Lean kernel, so neither the compiler nor whoever wrote the code or the
proof has to be trusted.

```bash
cargo build --release -p e5r
e5r check examples/elf/sum.elf      # does every function conform to the profile?
e5r disasm examples/elf/sum.elf     # the code, nested by its block/loop structure
e5r export examples/elf/sum.elf --namespace Examples.Sum.Image -o lean/Examples/Sum/Image.lean
cd lean && lake build && lake exe e5r-audit
```

One theorem per function says it is correct, memory-safe, terminating and
follows the calling convention, for every input its precondition allows.
For `sum` in [examples/sum.c](examples/sum.c) as clang `-O2` compiled it:

```lean
theorem sum_verified : Verified code sum_dom sum_entry spec
```

[lean/Examples/Sum.lean](lean/Examples/Sum.lean) has the specification and
the proof. [lean/Examples/Sum2.lean](lean/Examples/Sum2.lean) proves a caller,
`sum(a, n) + sum(b, m)` with its stack frame, from `sum`'s specification
alone. [lean/E5R/Adequacy.lean](lean/E5R/Adequacy.lean) proves, once for all
programs, what such a theorem means for the machine.
`scripts/check-proof-controls.sh` checks that mutated binaries break the proofs.

## Layout

| Path | What |
| --- | --- |
| [docs/isa/](docs/isa/README.md) | the profile, specifications, environment model, metadata, trusted base |
| [lean/E5R/](lean/E5R) | ISA semantics, environment model, program logic, adequacy, tactics |
| [lean/Examples/](lean/Examples) | proofs about committed binaries in [examples/elf/](examples/elf) |
| [crates/e5r/](crates/e5r) | the `e5r` tool: ELF reader, decoder, profile checker, structure recovery, Lean export |
| [experiment/](experiment/README.md) | earlier work: PTX kernel and RV32 firmware verification (`e5r-exp`) |
| [devinfra/](devinfra/README.md) | development infrastructure: the binary analysis toolkit and decompiler (`e5rx`) |

## Requirements

Rust (stable), Lean 4 through elan (the version is in
[lean/lean-toolchain](lean/lean-toolchain)), and for building examples and
running the oracle tests: clang, ld.lld, llvm-mc and qemu-riscv64.

[ROADMAP](docs/ROADMAP.md) · [CONTRIBUTING](CONTRIBUTING.md) · Apache-2.0
