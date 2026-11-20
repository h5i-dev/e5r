# Development infrastructure

`nocompiler-x`, the binary analysis toolkit nocompiler started as: ELF, PE/COFF and Mach-O
loaders, x86-64 and AArch64 decoders, a SLEIGH runtime, an IR with lifters,
function and CFG recovery, a decompiler to C, a binary differ and an
annotation log that merges in git. It is used to look at binaries while
working on the core. Nothing it computes is an input to a proof.

| Path | What |
| --- | --- |
| `crates/` | the toolkit crates; `nocompiler-cli` is the `nocompiler-x` binary |
| `docs/` | [MANUAL.md](docs/MANUAL.md), design notes, scorecard and benchmarks; [ROADMAP-toolkit.md](docs/ROADMAP-toolkit.md) is the toolkit's milestone record |
| `fixtures/` | sources of the test corpus; `scripts/build-fixtures.sh` builds it into `fixtures/build/` |
| `scripts/` | corpus, benchmark, comparison and release scripts; they work in this directory |
| `skills/` | an agent skill for driving `nocompiler-x` |
| `install.sh` | installs a released `nocompiler-x` |

```bash
cargo build --release -p nocompiler-cli             # ../target/release/nocompiler-x
devinfra/scripts/build-fixtures.sh           # the corpus the oracle-backed tests need
```
