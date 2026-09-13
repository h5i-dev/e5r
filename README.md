# r12e

A reverse engineering toolkit with a command line as its only front end. One
static Rust binary: no JVM, no project server, no proprietary database.

It loads a binary, recovers functions, disassembles, lifts to an IR, decompiles
to C, diffs two builds, and writes an analyst's findings to a text log that git
can merge.

Status: early, and honest about it. `ROADMAP.md` is the scope authority.

What works today: ELF loading, an AArch64 decoder at objdump parity, function
discovery with provenance, control flow, cross references, strings, a CLI with
JSON on every command, and a git-mergeable annotation log. No decompiler yet,
and x86-64 decodes only far enough to load the container.

```console
$ r12e info ./a.out
$ r12e funcs ./a.out
$ r12e disas ./a.out main
$ r12e annotate ./a.out name 0x4006e8 parse_header
$ r12e xrefs ./a.out 0x4006e8
$ r12e stats --json ./a.out
$ r12e mcp                    # JSON-RPC on stdin and stdout, for an agent
```

Analysis of `libc.so.6` (1.7 MB, 3,534 functions, 436,040 instructions, 57,646
references) takes 0.08s and 33 MB on a 10-core aarch64 machine. `objdump -d` on
the same file takes 0.31s and only disassembles.

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
- **Determinism.** Same bytes, same output, any thread count.
- **Provenance.** A boundary from an `.eh_frame` FDE and one from a prologue
  pattern are different claims, and the output says which.
- **Automation first.** JSON on every command, stable exit codes, an MCP server.
  The CLI is a thin client of the library.

## Build

The checkout is release-only; see `CLAUDE.md`.

```
cargo build --release
cargo test --release --workspace
```

## History

r12e began as a C++ teaching disassembler for x86-64. That code is in the git
history, and its x86-64 and ELF notes are kept at
[`docs/x86-64-notes.md`](docs/x86-64-notes.md).

## License

Apache-2.0.
