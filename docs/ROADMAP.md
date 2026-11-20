# Roadmap

Status: 2026-11-20. This file is the scope authority for nocompiler.

**Decision (2026-11-20).** The core of nocompiler is the nocompiler profile: a
formal-verification-friendly profile of RISC-V, with the Lean 4 library
proofs about it are written in and the tools that check binaries against it
([docs/isa/](isa/README.md)). The PTX and RV32 firmware verifiers move to
[experiment/](../experiment/README.md) and the binary analysis toolkit with
its decompiler to [docs/toolkit/](toolkit/README.md). When they compete for
effort, the core comes first. The previous roadmap, including the toolkit's
milestones and its "not building" list, is kept as
[docs/toolkit/ROADMAP-toolkit.md](toolkit/ROADMAP-toolkit.md).

## Principles

- **Binaries stay binaries.** Profile code runs on any RV64 machine. Nothing
  rejects a binary at load time; a proof is an optional, separate artifact
  about exact bytes.
- **Proofs are about what the compiler emitted**, checked by the Lean kernel.
  Compilers, tools and whoever writes code or proofs are not trusted.
- **One theorem per function** carries correctness, memory safety,
  termination and the calling convention, and composes through calls by
  specification alone.
- **The trusted base is listed** ([isa/trust.md](isa/trust.md)) and each part
  of it has an external oracle wherever one exists.

## Version 0

| Part | State |
| --- | --- |
| Instruction subset RV64IM + Zba + Zbb, decoder, semantics in Lean | done; decoder checked against llvm-mc, semantics against qemu-riscv64 |
| Environment model: write, read, exit, exit_group | done |
| `Reach`/`Exec`, program logic (sequencing, loops, calls, frame) | done, proved |
| Adequacy: no fault, memory safety, postcondition, termination on the machine | done, proved |
| Function specifications with the LP64 calling convention | done |
| Step tactics and word-arithmetic lemmas | done |
| `nocompiler` tool: check R1 to R5, recover structure, `.nocompiler.struct`, export, disasm | done |
| Lean ELF reader and `nocompiler-audit`: `.text` and every data section match the binary, axioms | done |
| Worked examples from clang `-O2`: `sum` (a loop over an array) and `sum2` (a stack frame and two calls to `sum`, proved from its specification alone) | done |
| Negative controls: mutated binaries must break their proofs (`scripts/core/check-proof-controls.sh`) | done |
| Syscall examples: `write_all` (a loop over short writes, with errors) and `hello` (writes a `.rodata` message through it, then exits) | done |
| The structural checker in Lean (R1 to R3), `<name>_checked` theorems for every exported function, and `Struct.cfi`: a checked function only transfers control as the rules allow | done |
| R4 and R5 (registers, stack discipline) in Lean | next |
| `nocompiler cc`: clang and ld.lld with the flags that keep ordinary C in the profile, then annotate and check; tested on a corpus | done |
| Loop invariants placed from `.nocompiler.struct` by the tactics instead of by hand | next |
| Spec vocabulary (`lean/NoCompiler/Vocab/`: buffers, folds, words, frames) and spec QA: spec mutation tests, computable specs against independent references ([isa/vocab.md](isa/vocab.md)) | done |
| Differential test against the Sail RISC-V model's C emulator (pinned release), random programs over every instruction | done |
| Lean semantics generated from the Sail RISC-V model (its Lean backend) and proved equal to `NoCompiler.exec` | planned: needs the Sail toolchain built (OCaml 5, opam) and a generated model of tens of thousands of lines |

## Version 1

- Jump tables as a recognised pattern; typed indirect calls (function
  pointers, vtables, `dyn Trait`).
- Recursion with a variant and a stack bound.
- The `+nocompiler` target feature in LLVM's RISC-V backend with WebAssembly's
  structuring passes, emitting `.nocompiler.struct` ([isa/toolchain.md](isa/toolchain.md)).
  Not started: it needs an LLVM build tree (tens of GB), which the current
  development machine has no room for. `nocompiler cc` covers what flags can.
- A Rust target specification and a `no_std` example.
- `mmap`/`brk` in the environment model.

## Version 2

- The A extension and more than one thread, which needs reasoning under the
  RVWMO memory model.
- F and D (IEEE 754 rounding), then V.
- A constant-time discipline (no secret-dependent branches or addresses) as
  an additional relational property.

## Not building

- Enforcement at load time in the style of the eBPF verifier. The profile is
  a convention plus proofs, not a sandbox.
- A new instruction encoding. The profile is a subset of RISC-V so that
  existing hardware, emulators and compilers keep working.
- x86 or Arm profiles. Variable-length encodings and condition flags are the
  costs the profile exists to avoid.
- A verified compiler. The compiler is outside the trusted base by design.
