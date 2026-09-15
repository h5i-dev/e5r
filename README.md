# e5r: The Reverse Engineering Toolkit for AI Agents

**e5r** is a disassembler, decompiler and binary differ with a command line as
its only front end. Every command speaks JSON, every recovered fact carries the
evidence for it, and every name, type and comment an agent writes lands in a
git-mergeable log. One static Rust binary: no JVM, no project server, no
proprietary database.

```bash
# Look at a binary.
e5r info ./a.out                              # container, architecture, entry, what the loader noticed
e5r funcs ./a.out                             # every function, with the evidence for each boundary
e5r disas ./a.out main                        # one function, or a range, or everything
e5r decompile ./a.out main                    # pseudo-C, with a goto where the shape is not there

# Ask questions instead of reading output.
e5r xrefs ./a.out 0x4006e8                    # who reaches this, and how
e5r strings ./a.out                           # ASCII, UTF-8 and UTF-16LE, by section
e5r classes ./a.out                           # C++ hierarchy from the vtables and the RTTI
e5r query ./a.out 'functions where insns > 100 and name ~ "crypt"'

# Write what you worked out, and merge it like code.
e5r annotate ./a.out name 0x4006e8 parse_header
e5r annotate ./a.out type 0x4006e8 "int parse_header(struct hdr *h, size_t n)"
e5r decompile ./a.out parse_header            # the assertion reaches the output

# Drive it from an agent.
e5r batch ./a.out --command funcs --command strings   # several commands, one document
e5r funcs ./a.out --json                      # every command takes it
```

---

## 1. Install

```bash
curl -fsSL https://raw.githubusercontent.com/h5i-dev/e5r/main/install.sh | sh
# cargo install --path crates/e5r-cli   # build from source
```

One binary, no runtime dependency. The script works out the platform, verifies
the download against the release's `SHA256SUMS`, and refuses to install if it
does not match. [`MANUAL.md`](MANUAL.md) has the environment variables.

```bash
e5r completions bash > /etc/bash_completion.d/e5r   # or zsh, fish, elvish
e5r manpage > ~/.local/share/man/man1/e5r.1
```

---

## 2. Use it

### 2.1. Read a binary

Everything e5r recovers carries the evidence for it, and the strength of that
evidence is printed next to it, so a boundary from an `.eh_frame` record and one
from a prologue pattern are never the same claim:

```bash
e5r info ./a.out                    # container, architecture, entry, warnings
e5r sections ./a.out                # and how each maps into memory
e5r funcs ./a.out                   # address, size, blocks, strength, evidence, name
e5r disas ./a.out main              # a function, an address, a range, or `all`
e5r stats ./a.out --json            # counts, for a script rather than a reader
```

### 2.2. Decompile

```bash
e5r decompile ./a.out main          # pseudo-C
e5r decompile ./a.out all --json    # every complete function, with a position map
e5r shapes ./a.out parse_header     # what the pointers it takes appear to point at
e5r emulate ./a.out checksum 1 2 3  # run it in the interpreter and see what comes back
```

### 2.3. Write analysis back, and merge it

Names, types and comments are lines in an append-only log keyed to **content
anchors** — a shape hash and a body hash — rather than to addresses, so they
survive a rebuild that moves everything:

```bash
e5r annotate ./a.out name 0x4006e8 parse_header
e5r annotate ./a.out comment 0x400710 "length is attacker-controlled"
e5r annotate ./a.out list
```

### 2.4. Compare two builds

```bash
e5r diff ./old ./new                # which functions changed, moved, appeared, vanished
e5r diff ./old ./new --json         # and what changed inside each one
```

### 2.5. Patch, and say why

```bash
e5r patch ./a.out record 0x4006f0 --asm "nop" --out fix.e5rpatch
e5r patch ./a.out preview fix.e5rpatch         # what it would change
e5r patch ./a.out apply fix.e5rpatch --out ./patched   # a new file, never in place
```

### 2.6. Drive it from an agent

```bash
e5r funcs ./a.out --json                      # every command takes it
e5r batch ./a.out --command funcs --command strings
e5r project new ./a.out --out a.e5rproj      # reopen it later without reanalysing
```

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
| Surfaces | CLI with JSON on every command, REPL, binary diff, patching |

Scope, and what is deliberately **not** built, is in
[`ROADMAP.md`](ROADMAP.md), which is the authority on both.

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

- [MANUAL.md](MANUAL.md) / `man e5r`: the full command reference
- [docs/tutorial.md](docs/tutorial.md): a stripped binary to a committed annotation log
- [docs/design/](docs/design/): one document per subsystem, and why it is shaped that way
- [docs/scorecard.md](docs/scorecard.md): every measured number, including the bad ones
- [CONTRIBUTING.md](CONTRIBUTING.md): what a change has to measure, and the clean-room rule

---

## 8. FAQ

<details>
<summary>What is e5r?</summary>

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
they are what e5r is betting on.

</details>

<details>
<summary>Is the decompiler as good as Hex-Rays?</summary>

No, and the gap is measured rather than estimated: 23.4 union on DecBench
against IDA's published 47.9 — on a different corpus, which
[`docs/decbench.md`](docs/decbench.md) is careful about. What e5r does claim is
narrower and checked: every function it decompiles, that can be compiled and
run, computes what the machine computes.

</details>

<details>
<summary>What does "agent-native" actually mean here?</summary>

Two things that are properties of the tool rather than a wrapper around it.
Every command emits JSON with a schema and a documented exit code, so an agent
drives it the same way it drives `git`. And an agent's conclusions are
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

e5r began as a C++ teaching disassembler for x86-64. That code is in the git
history, and its x86-64 and ELF notes are kept at
[`docs/x86-64-notes.md`](docs/x86-64-notes.md).

---

## 10. License

Apache-2.0. See [LICENSE](LICENSE).
