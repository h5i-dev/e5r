# Documentation

Where things are, and where they are documented. [ROADMAP.md](ROADMAP.md) is the scope: versions of the profile, and what is not built yet.

## Repository layout

| Path | What | Docs |
| --- | --- | --- |
| `crates/nocompiler` | the core library: ELF reader, decoder, profile checker (levels L0–L2), metadata, Lean exporter, `cmd` (the core commands) | [isa/](isa/README.md) |
| `crates/nocompiler-cli` | the one binary, `nocompiler`: core commands and toolkit commands | `nocompiler --help`, [toolkit/MANUAL.md](toolkit/MANUAL.md) |
| `crates/nocompiler-*` (the rest) | the binary analysis toolkit: loaders, decoders, SLEIGH, IR, analysis, decompiler, differ, annotation log | [toolkit/](toolkit/README.md) |
| `lean/` | the Lean library (`NoCompiler/`), example proofs (`Examples/`), demo proofs (`Demo/`), the audit | [isa/spec.md](isa/spec.md), [isa/trust.md](isa/trust.md) |
| `examples/` | C sources, build scripts and the committed ELFs the proofs are about; `examples/demo/` is the A/B comparison; `examples/link/` the relocation example | [examples/demo/README.md](../examples/demo/README.md) |
| `fixtures/` | the toolkit's test corpus (sources; `scripts/toolkit/build-fixtures.sh` builds it) | [toolkit/README.md](toolkit/README.md) |
| `scripts/core/` | proof and audit controls, spec references and mutations, the dev-build guard | [isa/vocab.md](isa/vocab.md), [CONTRIBUTING](../CONTRIBUTING.md) |
| `scripts/toolkit/` | corpus, benchmark, comparison and release scripts; run from the repository root | [toolkit/benchmarks.md](toolkit/benchmarks.md) |
| `skills/` | an agent skill for the toolkit commands | |
| `install.sh` | installs a released `nocompiler` binary | |
| `experiment/` | PTX and RV32 firmware verification: crates, Lean projects, scripts and docs, self-contained (`nocompiler-exp`) | [experiment/README.md](../experiment/README.md) |

## The nocompiler profile (the core)

- [isa/profile.md](isa/profile.md): the instruction subset, the semantics choices, the structural rules, the calling convention
- [isa/v1.md](isa/v1.md): profile spec v1 (levels L0–L2, rule R6, the structured form, relocatable proofs) and its decisions; [isa/v1-results.md](isa/v1-results.md): its acceptance criteria as measured
- [isa/spec.md](isa/spec.md): function specifications, `VerifiedImg`/`Verified`, what a proof establishes about the machine, how to write one
- [isa/vocab.md](isa/vocab.md): the spec vocabulary, and how specifications are checked (references, mutations)
- [isa/environment.md](isa/environment.md): the Linux syscall model behind `ecall`, and its assumptions
- [isa/metadata.md](isa/metadata.md): the `.nocompiler.struct` section (v2)
- [isa/toolchain.md](isa/toolchain.md): building conforming code, the proof workflow, the LLVM and Rust plan
- [isa/ledger.md](isa/ledger.md): the ledger of verified functions
- [isa/refine.md](isa/refine.md): refinement, B refines A with A as the specification (the relational layer of the optimisation benchmark)
- [isa/trust.md](isa/trust.md): what a result depends on, and what it does not
- [isa/related-work.md](isa/related-work.md): where the ideas come from

## The binary analysis toolkit

[toolkit/README.md](toolkit/README.md). Start with [MANUAL.md](toolkit/MANUAL.md) and the [tutorial](toolkit/tutorial.md). The design notes are in [toolkit/design/](toolkit/design/README.md). Measurements are in the [scorecard](toolkit/scorecard.md), [benchmarks](toolkit/benchmarks.md), [boundaries](toolkit/boundaries.md) and [DecBench](toolkit/decbench.md) pages. [ROADMAP-toolkit.md](toolkit/ROADMAP-toolkit.md) is its milestone record.

## Experiments

[experiment/README.md](../experiment/README.md): PTX ([ptx.md](../experiment/docs/ptx.md)), and RV32 firmware ([firmware.md](../experiment/docs/firmware.md), [rmk-checkpoint.md](../experiment/docs/rmk-checkpoint.md)).
