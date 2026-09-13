# r12e

A reverse engineering toolkit with a command line as its only front end. One
static Rust binary: no JVM, no project server, no proprietary database.

Status: early, and honest about it. [`ROADMAP.md`](ROADMAP.md) is the scope
authority and [`docs/scorecard.md`](docs/scorecard.md) holds the measured
numbers, including the ones that go against us.

## What works

| | |
| --- | --- |
| Containers | ELF, PE and COFF, Mach-O (thin and fat), raw images |
| Decoders | AArch64 and x86-64, both at zero disagreements with their oracle |
| Analysis | functions with provenance, control flow, jump tables, no-return propagation, cross references, strings |
| Names | Itanium C++, Rust (both schemes), MSVC |
| Storage | git-mergeable annotation log keyed to content anchors |
| Surfaces | CLI with JSON on every command, MCP server, binary diff |

Not built: the decompiler, which is what would make this a competitor rather
than a good disassembler. No IR, no SSA, no type recovery. SVE, AVX and 32-bit
x86 are deliberately out of scope for now.

```console
$ r12e info ./a.out
$ r12e funcs ./a.out
$ r12e disas ./a.out main
$ r12e xrefs ./a.out 0x4006e8
$ r12e annotate ./a.out name 0x4006e8 parse_header
$ r12e diff ./old ./new          # what did the patch touch
$ r12e stats --json ./a.out
$ r12e mcp                       # JSON-RPC on stdin and stdout, for an agent
```

Analysis of `libc.so.6` (1.7 MB, 3,517 functions, 95.3% of them analyzed
completely) takes 0.10s and 58 MB on a 10-core aarch64 machine. `objdump -d` on
the same file takes 0.26s and only disassembles.

## Why another one

Ghidra, rizin and IDA are each better than r12e at breadth of architecture and
at accumulated analysis lore. The bets are on the axes where their design, not
their effort, is the limit:

- **Speed.** Memory-mapped, parallel per function, analyzed on demand.
- **Annotations in git.** Names, types and comments are lines in an append-only
  log keyed to content anchors that survive a rebuild. Two analysts merge with
  `git merge`. Reviewing reverse engineering work becomes a pull request. Add
  `*.r12e merge=union` to `.gitattributes`: the fold ignores line order, so the
  union of two branches is the correct merge and git already knows how.
- **Determinism.** Same bytes, same output, any thread count. Checked.
- **Provenance.** A boundary from an `.eh_frame` FDE and one from a prologue
  pattern are different claims, and `r12e funcs` says which.
- **Automation first.** JSON on every command, documented exit codes, an MCP
  server. The CLI is a thin client of the library.

## How it is tested

Every correctness gate is measured against something outside this repository,
so the numbers cannot be produced by writing more assertions about our own
behaviour.

| gate | oracle | result |
| --- | --- | --- |
| AArch64 decoding | `objdump -d` | 1,429,650 instructions, 0 wrong, 99.87% decoded |
| x86-64 decoding | `llvm-objdump --x86-asm-syntax=intel` | 4,760 instructions, 0 wrong, 100% decoded |
| ELF loading | `readelf` | entry point, every section address, every defined function symbol |
| PLT naming | `objdump -d --section=.plt` | every entry objdump names |
| Mach-O symbols | `llvm-objdump -t` | every symbol it lists |
| Demangling | `c++filt` | 5,953 libstdc++ names, 94.0% exact, 2.4% wrong |
| Annotation merge | `git merge` itself | two branches, 40 assertions each, clean |
| Determinism | itself, at 1, 4 and 10 threads | 35 fixtures, identical output |

Plus mutation fuzzing of every loader and decoder in the ordinary test run,
which found the one place in the loaders that bypassed the bounds-checked
reader.

## Build

The checkout is release-only; see [`CLAUDE.md`](CLAUDE.md).

```console
$ cargo build --release
$ ./scripts/build-fixtures.sh     # the corpus the gates measure against
$ cargo test --release --workspace
$ ./scripts/bench.sh
```

## History

r12e began as a C++ teaching disassembler for x86-64. That code is in the git
history, and its x86-64 and ELF notes are kept at
[`docs/x86-64-notes.md`](docs/x86-64-notes.md).

## License

Apache-2.0.
