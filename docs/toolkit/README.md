# Development infrastructure

`nocompiler`, the binary analysis toolkit nocompiler started as: ELF, PE/COFF and Mach-O
loaders, x86-64 and AArch64 decoders, a SLEIGH runtime, an IR with lifters,
function and CFG recovery, a decompiler to C, a binary differ and an
annotation log that merges in git. It is used to look at binaries while
working on the core. Nothing it computes is an input to a proof.

| Path | What |
| --- | --- |
| `crates/nocompiler-*` | the toolkit crates (every crate but `crates/nocompiler`, the core); `nocompiler-cli` is the binary |
| `docs/toolkit/` | [MANUAL.md](MANUAL.md), [design notes](design/README.md), [scorecard](scorecard.md) and [benchmarks](benchmarks.md); [ROADMAP-toolkit.md](ROADMAP-toolkit.md) is the toolkit's milestone record |
| `fixtures/` | sources of the test corpus; `scripts/toolkit/build-fixtures.sh` builds it into `fixtures/build/` |
| `scripts/toolkit/` | corpus, benchmark, comparison and release scripts; they run from the repository root |
| `skills/` | an agent skill for driving the toolkit commands |
| `install.sh` | installs a released binary |

```bash
cargo build --release -p nocompiler-cli     # target/release/nocompiler
scripts/toolkit/build-fixtures.sh           # the corpus the oracle-backed tests need
```
