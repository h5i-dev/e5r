# Contributing

## The rule that matters: clean room

This project reimplements ideas that other reverse engineering tools also
implement. Ideas are not the problem; copied code is.

**Work from public specifications and from observed behaviour, never from
another tool's source.** In practice:

- Read the published specification: the ELF gABI and the processor supplements,
  the DWARF standard, the PE/COFF specification, the Itanium C++ ABI, the ARM
  and Intel architecture reference manuals, the public documentation of the PDB
  format.
- Observe what an existing tool *does* as much as you like. Running `objdump`
  and comparing its output against ours is how the decoders are tested, and
  that is fine: the output is a fact about the input, not a piece of someone's
  program.
- Do not read another tool's implementation and then write the same thing here.
  If you have read it, say so in the pull request, and expect the reviewer to
  ask someone who has not to write that part.
- One exception, deliberately narrow: the SLEIGH *language definitions* under
  Ghidra's processor tree are data, and loading them is the point of M2. Their
  format is specified. The decompiler's source is not to be consulted.

If a fixture or a test case comes from another project, say where it came from
and under what licence, in the file that uses it.

## What a change has to come with

Every claim this tool makes is measured, and a change that makes a claim has to
bring its measurement. `ROADMAP.md` says what each milestone is gated on; the
short version:

- **An external oracle wherever one exists.** A decoder is compared against
  `objdump` and `llvm-objdump`; a lifter against what a processor produced when
  the same program was run; a demangler against `c++filt`; debug information
  against `readelf`; a merge against `git merge`. Numbers that only compare the
  tool against itself are not evidence.
- **Wrong and missing are different.** A wrong answer is a bug with no
  allowance and the test asserts zero of them. A missing answer is a gap with a
  floor or a ceiling that only moves one way, and the number stays in
  `docs/scorecard.md` even when it is unflattering.
- **A test that cannot fail is not a test.** After writing one, break the code
  it covers on purpose and check that it goes red.

## Style

- Comments are concise and explain *why*. The code says what it does. A comment
  that restates the line above it is noise, and a banner is worse.
- Say what is not known. An analysis that cannot work something out reports
  that rather than guessing, and the type system should make the difference
  visible: `Option`, an explicit `Unresolved`, a strength on the evidence.
- No emoji, no em dashes.
- `cargo clippy --release --all-targets` leaves no warnings.

## Building

This checkout is release-only; `CLAUDE.md` explains why and how the guards
work. Every command takes `--release`:

```
CARGO_BUILD_JOBS=4 cargo build --release
CARGO_BUILD_JOBS=4 cargo test --release
bash scripts/build-fixtures.sh      # the corpus the gates measure against
bash scripts/check-determinism.sh   # the same input must give the same output
```

Fixtures are built, not committed. A test whose fixture or tool is missing
returns early rather than failing, so a fresh checkout on a different machine
still runs the suite it can.

## Reporting something wrong

A decoding that disagrees with `objdump`, a lifting that disagrees with the
processor, or a recovered fact that is untrue are the most valuable reports
this project can get. Include the bytes, the architecture, and what the other
tool said.
