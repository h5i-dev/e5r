# Documentation

- [ROADMAP.md](ROADMAP.md): scope, versions of the profile, what is not built yet

## The nocompiler profile (the core)

- [isa/profile.md](isa/profile.md): the instruction subset, the semantics choices, the structural rules R1 to R5, the calling convention
- [isa/spec.md](isa/spec.md): function specifications, `VerifiedImg`, what a proof establishes about the machine, how to write one
- [isa/environment.md](isa/environment.md): the Linux syscall model behind `ecall`, and its assumptions
- [isa/metadata.md](isa/metadata.md): the `.nocompiler.struct` section
- [isa/toolchain.md](isa/toolchain.md): building conforming code, the proof workflow, the LLVM and Rust plan
- [isa/trust.md](isa/trust.md): what a result depends on, and what it does not
- [isa/related-work.md](isa/related-work.md): where the ideas come from

## Experiments ([experiment/](../experiment/README.md))

PTX kernel verification and RV32 firmware proofs, the work nocompiler grew from:
[experiment/docs/](../experiment/docs).

## Development infrastructure ([devinfra/](../devinfra/README.md))

The binary analysis toolkit `nocompiler-x` (disassembler, decompiler, differ):
[devinfra/docs/](../devinfra/docs), starting from [MANUAL.md](../devinfra/docs/MANUAL.md).
