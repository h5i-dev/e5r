# r12e

A reverse engineering toolkit with a command line as its only front end. One
static Rust binary: no JVM, no project server, no proprietary database.

It loads a binary, recovers functions, disassembles, lifts to an IR, decompiles
to C, diffs two builds, and writes an analyst's findings to a text log that git
can merge.

Status: early. `ROADMAP.md` is the scope authority and says what is built, what
is next, and what will not be built. Nothing here is ready for real work yet.

## Why another one

Ghidra, rizin and IDA are each better than r12e at breadth of architecture and
at accumulated analysis lore. The bets are on the axes where their design, not
their effort, is the limit:

- **Speed.** Memory-mapped, parallel per function, analyzed on demand.
- **Annotations in git.** Names, types and comments are lines in an append-only
  log keyed to content anchors that survive a rebuild. Two analysts merge with
  `git merge`. Reviewing reverse engineering work becomes a pull request.
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
