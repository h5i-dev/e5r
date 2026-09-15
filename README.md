<p align="center">
  <a href="https://github.com/h5i-dev/r12e/actions/workflows/ci.yaml"><img alt="ci" src="https://github.com/h5i-dev/r12e/actions/workflows/ci.yaml/badge.svg"></a>
  <a href="https://github.com/h5i-dev/r12e/blob/main/LICENSE"><img alt="Apache-2.0" src="https://img.shields.io/github/license/h5i-dev/r12e?color=blue"></a>
  <a href="https://github.com/h5i-dev/r12e/stargazers"><img alt="GitHub stars" src="https://img.shields.io/github/stars/h5i-dev/r12e?style=social"></a>
  <a href="https://github.com/h5i-dev/r12e/releases"><img alt="release" src="https://img.shields.io/github/v/release/h5i-dev/r12e?label=release"></a>
</p>

<h1 align="center">The Reverse Engineering Toolkit for AI Agents</h1>

**r12e** is a disassembler, decompiler and binary differ with a command line as
its only front end. Every command speaks JSON, every recovered fact carries the
evidence for it, and every name, type and comment an agent writes lands in a
git-mergeable log. One static Rust binary: no JVM, no project server, no
proprietary database.

<table align="center">
  <tr>
    <td align="center">
      <strong>Agent-native</strong><br>
      <sub>JSON everywhere, an MCP server, and analysis an agent can correct</sub>
    </td>
    <td align="center">
      <strong>Evidence, not assertions</strong><br>
      <sub>Every gate measured against an outside oracle, including a processor</sub>
    </td>
    <td align="center">
      <strong>21×–3,291× faster than rizin</strong><br>
      <sub><a href="./docs/benchmarks.md">2.4×–8.6× less memory, in our benchmarks</a></sub>
    </td>
  </tr>
</table>

**Let agents read binaries the way a human does with IDA — and write what they
learn back into the repository.**

```bash
# Look at a binary.
r12e info ./a.out                              # container, architecture, entry, what the loader noticed
r12e funcs ./a.out                             # every function, with the evidence for each boundary
r12e disas ./a.out main                        # one function, or a range, or everything
r12e decompile ./a.out main                    # pseudo-C, with a goto where the shape is not there

# Ask questions instead of reading output.
r12e xrefs ./a.out 0x4006e8                    # who reaches this, and how
r12e strings ./a.out                           # ASCII, UTF-8 and UTF-16LE, by section
r12e classes ./a.out                           # C++ hierarchy from the vtables and the RTTI
r12e query ./a.out 'functions where insns > 100 and name ~ "crypt"'

# Write what you worked out, and merge it like code.
r12e annotate ./a.out name 0x4006e8 parse_header
r12e annotate ./a.out type 0x4006e8 "int parse_header(struct hdr *h, size_t n)"
r12e decompile ./a.out parse_header            # the assertion reaches the output

# Drive it from an agent.
r12e mcp                                       # Model Context Protocol on stdin and stdout
r12e batch ./a.out --command funcs --command strings   # several commands, one document
```

---

## 1. Install

```bash
curl -fsSL https://raw.githubusercontent.com/h5i-dev/r12e/main/install.sh | sh
# cargo install --path crates/r12e-cli   # build from source
```

One binary, no runtime dependency. The script works out the platform, verifies
the download against the release's `SHA256SUMS`, and refuses to install if it
does not match. [`MANUAL.md`](MANUAL.md) has the environment variables.

```bash
r12e completions bash > /etc/bash_completion.d/r12e   # or zsh, fish, elvish
r12e manpage > ~/.local/share/man/man1/r12e.1
```

---

## 2. Use it

### 2.1. Read a binary

Everything r12e recovers carries the evidence for it, and the strength of that
evidence is printed next to it, so a boundary from an `.eh_frame` record and one
from a prologue pattern are never the same claim:

```bash
r12e info ./a.out                    # container, architecture, entry, warnings
r12e sections ./a.out                # and how each maps into memory
r12e funcs ./a.out                   # address, size, blocks, strength, evidence, name
r12e disas ./a.out main              # a function, an address, a range, or `all`
r12e stats ./a.out --json            # counts, for a script rather than a reader
```

| Strength | Meaning |
| --- | --- |
| `asserted` | A person or an agent wrote it in the annotation log. |
| `proven` | The file says so: a symbol table, debug information, an unwind record. |
| `inferred` | The code implies it: a call target, a jump table, an import thunk. |
| `heuristic` | A pattern suggests it: a prologue, a sweep, a pointer in data. |

Where a thing cannot be worked out it is reported as unknown, never guessed.

### 2.2. Decompile

```bash
r12e decompile ./a.out main          # pseudo-C
r12e decompile ./a.out all --json    # every complete function, with a position map
r12e shapes ./a.out parse_header     # what the pointers it takes appear to point at
r12e emulate ./a.out checksum 1 2 3  # run it in the interpreter and see what comes back
```

The output says what the machine does in C's notation; it does not claim to be
the source. Where the control flow does not fit a loop or a branch, a labelled
`goto` appears rather than a shape that is not there, and the count is printed.

**Every function that can be compiled and run is compiled and run, on every
argument vector, and agrees with the interpreter.** That gate started at 130
disagreeing functions and is at zero.

### 2.3. Write analysis back, and merge it

Names, types and comments are lines in an append-only log keyed to **content
anchors** — a shape hash and a body hash — rather than to addresses, so they
survive a rebuild that moves everything:

```bash
r12e annotate ./a.out name 0x4006e8 parse_header
r12e annotate ./a.out comment 0x400710 "length is attacker-controlled"
r12e annotate ./a.out list
```

Two analysts merge with `git merge`. Reviewing reverse engineering work becomes
a pull request. Add `*.r12e merge=union` to `.gitattributes`: the fold ignores
line order, so the union of two branches is the correct merge and git already
knows how to compute it.

### 2.4. Compare two builds

```bash
r12e diff ./old ./new                # which functions changed, moved, appeared, vanished
r12e diff ./old ./new --json         # and what changed inside each one
```

Matching is by content, not by address, so a rebuild that shifts every function
is not reported as a rewrite of the program.

### 2.5. Patch, and say why

```bash
r12e patch ./a.out record 0x4006f0 --asm "nop" --out fix.r12epatch
r12e patch ./a.out preview fix.r12epatch         # what it would change
r12e patch ./a.out apply fix.r12epatch --out ./patched   # a new file, never in place
```

### 2.6. Drive it from an agent

```bash
r12e mcp                                       # JSON-RPC over stdin and stdout
r12e batch ./a.out --command funcs --command strings
r12e project new ./a.out --out a.r12eproj      # reopen it later without reanalysing
```

Every command takes `--json`, and the exit codes are documented: `0` ok, `1`
nothing found, `2` bad usage, `3` bad input. The CLI is a thin client of the
library, so anything it can do is a function call away.

---

## 3. What works

| | |
| --- | --- |
| Containers | ELF, PE and COFF, Mach-O (thin and fat), PDB, `ar` archives, raw images |
| Decoders | AArch64, x86-64, i386, ARM32 and Thumb-2 — each at zero disagreements with its oracle |
| Also | any architecture a Ghidra SLEIGH specification covers, through our own runtime |
| Lifting | p-code-style IR and SSA for AArch64, x86-64, i386 and ARM32/Thumb |
| Analysis | functions with provenance, control flow, jump tables, no-return propagation, cross references, strings, data regions |
| Decompiler | expressions, types, structuring, variable naming, C++ classes from vtables and RTTI |
| Names | Itanium C++, Rust (both schemes), MSVC |
| Storage | git-mergeable annotation log keyed to content anchors |
| Surfaces | CLI with JSON on every command, MCP server, REPL, binary diff, patching |

Scope, and what is deliberately **not** built, is in
[`ROADMAP.md`](ROADMAP.md), which is the authority on both.

---

## 4. How it is tested

Every correctness gate is measured against something outside this repository,
so no number here can be produced by writing more assertions about our own
behaviour. The ones that go against us stay in
[`docs/scorecard.md`](docs/scorecard.md).

| gate | oracle | result |
| --- | --- | --- |
| AArch64 decoding | `objdump -d` | 1,640,904 instructions, 0 wrong |
| x86-64 decoding | `llvm-objdump --x86-asm-syntax=intel` | 0 wrong |
| ARM32 and Thumb-2 | `llvm-objdump-18 -d` | 0 wrong |
| i386 decoding | `llvm-mc`, over a swept encoding space | 235,357 encodings, 0 wrong |
| SLEIGH decoding | `objdump` and `llvm-objdump` | 0 wrong on AArch64, x86-64 and RISC-V |
| Lifting | **a processor**, natively and under `qemu` | every case agrees |
| Decompiled C | **a processor**, again: compile it and run it | 0 functions disagree |
| Function boundaries | DWARF, via `readelf` | 95,697 functions; 0.766 recall blind, 0.937 precision |
| ELF, Mach-O, PDB loading | `readelf`, `llvm-objdump -t`, `llvm-pdbutil` | every section, symbol and record |
| Demangling | `c++filt` | 5,953 libstdc++ names |
| Annotation merge | `git merge` itself | two branches, clean |
| Determinism | itself, at 1, 4 and 10 threads | 153 fixtures, identical output |

A processor is the oracle wherever one can be: the lifters are checked by
assembling a case, running it, and comparing against our own interpreter, so
"the manual says this instruction sets the carry flag" is never the last word.

Plus mutation fuzzing of every loader and decoder in the ordinary test run,
which found the one place in the loaders that bypassed the bounds-checked
reader, and a no-panic gate over 1.26 million inputs across every entry point
that takes foreign bytes.

---

## 5. Where it stands against the others

Ghidra, rizin and IDA are each better than r12e at breadth of architecture and
at accumulated analysis lore. Two measurements, both with every command written
down in [`docs/benchmarks.md`](docs/benchmarks.md) and
[`docs/decbench.md`](docs/decbench.md):

- **Against rizin**, on the same 16 binaries on the same machine: 21× to 3,291×
  faster and 2.4× to 8.6× less memory. Three qualifications belong with that
  ratio and are in the table rather than under it — including the one row r12e
  loses.
- **Against angr, on DecBench**, a third-party decompiler benchmark: 23.4 union
  against angr's 37.0. That is a third behind, and the milestone this project
  set itself is Ghidra's published 32.2, which is **not met**.

The bets are on the axes where the others' design, not their effort, is the
limit: speed, annotations in git, determinism, provenance, and an interface
built for a program rather than for a person.

---

## 6. Build

The checkout is release-only; see [`CLAUDE.md`](CLAUDE.md).

```bash
cargo build --release
./scripts/build-fixtures.sh       # the corpus the gates measure against
cargo test --release --workspace
./scripts/bench.sh
```

---

## 7. Documentation

- [MANUAL.md](MANUAL.md) / `man r12e`: the full command reference
- [docs/tutorial.md](docs/tutorial.md): a stripped binary to a committed annotation log
- [docs/design/](docs/design/): one document per subsystem, and why it is shaped that way
- [docs/scorecard.md](docs/scorecard.md): every measured number, including the bad ones
- [CONTRIBUTING.md](CONTRIBUTING.md): what a change has to measure, and the clean-room rule

---

## 8. FAQ

<details>
<summary>What is r12e?</summary>

A reverse engineering toolkit: it loads a binary, recovers its functions,
disassembles and decompiles them, and lets you write names, types and comments
back into a log you can commit. It runs locally, is written in Rust, and ships
as one static binary.

</details>

<details>
<summary>Why another one, when Ghidra and rizin exist?</summary>

Not because they are bad. Because a few things are hard to retrofit: an
annotation store that merges with `git merge` rather than with a project-file
lock, output that is deterministic across thread counts, a provenance record on
every recovered fact, and an interface designed for a program to call rather
than for a person to click. Those are design choices rather than effort, and
they are what r12e is betting on.

</details>

<details>
<summary>Is the decompiler as good as Hex-Rays?</summary>

No, and the gap is measured rather than estimated: 23.4 union on DecBench
against IDA's published 47.9 — on a different corpus, which
[`docs/decbench.md`](docs/decbench.md) is careful about. What r12e does claim is
narrower and checked: every function it decompiles, that can be compiled and
run, computes what the machine computes.

</details>

<details>
<summary>What does "agent-native" actually mean here?</summary>

Three things that are properties of the tool rather than a wrapper around it.
Every command emits JSON with a schema and a documented exit code. An MCP server
exposes the analysis to a model directly. And an agent's conclusions are
first-class input: an asserted name or type reaches the decompiled output and
the recovered prototype, so read, conclude, correct, re-read is the normal way
to use it rather than a feature bolted on.

</details>

<details>
<summary>Can I trust what it tells me?</summary>

Look at the evidence column, and at [`docs/scorecard.md`](docs/scorecard.md).
"Wrong" is treated as a bug with no allowance; "not recovered" is a gap with a
number and a floor that only rises. Where the two could be confused, the
scorecard says so — it has a section for what is *not* measured.

</details>

<details>
<summary>What is not built?</summary>

WASM, .NET, DEX and Java class files; scripting beyond the batch language; and
the decompiler quality needed to clear the DecBench milestone. All of it is in
[`ROADMAP.md`](ROADMAP.md) with the reason, and none of it is claimed here.

</details>

---

## 9. History

r12e began as a C++ teaching disassembler for x86-64. That code is in the git
history, and its x86-64 and ELF notes are kept at
[`docs/x86-64-notes.md`](docs/x86-64-notes.md).

---

## 10. License

Apache-2.0. See [LICENSE](LICENSE).
