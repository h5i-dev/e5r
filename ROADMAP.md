# Roadmap

Status: drafted 2026-09-12, nothing built yet. This file is the scope authority
for r12e: what it is, what gets built in what order, and what will be refused in
review rather than argued about again.

r12e is a reverse engineering toolkit with a command line as its only front end.
It loads a binary, recovers functions, disassembles, lifts to an IR, decompiles
to C, diffs two builds, and writes an analyst's findings to a text log that git
can merge. One static Rust binary, no JVM, no project server, no proprietary
database.

The previous contents of this repository were a C++ teaching disassembler for
x86-64. It is gone from the tree as of M0 and stays readable in git history. The
x86-64 and ELF notes in `MEMO.md` survive the rewrite and move under `docs/`.

## The bets

Ghidra, rizin and IDA are each better than r12e will be for years at breadth of
architecture and at accumulated analysis lore. Beating them means picking the
axes where their design, not their effort, is the limit.

1. **Startup and throughput:** Ghidra pays JVM startup and a project import
   before it shows a function. rizin is single-threaded through most of its
   analysis. r12e memory-maps the image, analyzes functions in parallel, and
   analyzes a function only when something asks for it. The target is first
   useful output in under 200 ms on a 100 MB binary, and full analysis of
   `/bin/bash` faster than `rizin -A` by a factor we publish and regression-test.

2. **Annotations in git, not in a database:** Every name, type and comment an
   analyst writes is one line in an append-only log, keyed to a content anchor
   that survives a rebuild and a rebase. Two analysts working on branches merge
   with `git merge` and no conflict markers, because the log folds to the same
   state regardless of line order. Review of reverse engineering work becomes a
   pull request. Ghidra needs a server for this and IDA needs a plugin.

3. **Determinism:** Same bytes, same output, any thread count, any machine. This
   is what makes the other features possible: diffing two builds, gating a CI
   job on an analysis result, and reproducing a bug report all need the tool to
   stop guessing differently on Tuesday.

4. **Proven, inferred, asserted:** Every fact the engine reports carries which of
   the three it is and what evidence produced it. A function boundary from an
   `.eh_frame` FDE is not the same claim as one from a prologue pattern, and the
   output says so. The incumbents flatten both into the same listing.

5. **Built for automation first:** Structured JSON on every command, stable exit
   codes, an MCP server, and a library API that the CLI is a thin client of. Not
   a headless mode retrofitted onto a GUI.

6. **Breadth through SLEIGH, depth by hand:** Writing 40 instruction decoders is
   not a good use of the next two years. r12e ships a Rust SLEIGH runtime and
   compiler so Ghidra's processor specifications load directly, plus
   hand-written decoders for x86-64 and AArch64 where speed matters. Kuna proved
   the SLEIGH port is tractable.

## Architecture

The library owns every fact. The CLI, the MCP server and any future UI compute
nothing of their own.

```
r12e-core      addresses, spaces, memory map, ids, error model, provenance
r12e-format    ELF, PE/COFF, Mach-O, raw, archives, overlays
r12e-arch      decoder trait, hand-written x86/x86-64 and AArch64/ARM
r12e-sleigh    .sla runtime plus the SLEIGH compiler (breadth)
r12e-ir        p-code-style IR, SSA, dataflow framework
r12e-analysis  partition, function discovery, CFG, jump tables, xrefs, strings
r12e-types     type model, DWARF, PDB, demanglers, type archives
r12e-decomp    regions, structuring, expression rebuild, C emission
r12e-db        content anchors, the annotation log, git merge semantics
r12e-diff      function matching, build-to-build diff
r12e-patch     assembler-backed patch sets
r12e-api       stable library surface and the versioned JSON schema
r12e-mcp       agent server over r12e-api
r12e-cli       the r12e binary
```

Dependency edges run downward only. `r12e-cli` may depend on everything;
`r12e-core` depends on nothing in the workspace.

## Milestones

### M0. Clear the ground

- [x] Copy the release-only build guards from h5i (`scripts/no-debug-guard.sh`,
      `scripts/deny-debug-build.py`) and wire the hook in
      `.claude/settings.local.json`. This machine has 7.5 GB of RAM; a dev-profile
      build of a workspace this size is not affordable.
- [ ] Delete `src/`, `test/`, `script/`, `CMakeLists.txt` and the C++ build. Move
      `MEMO.md` to `docs/x86-64-notes.md`.
- [ ] Cargo workspace, edition 2024, MSRV pinned, `resolver = "3"`.
- [ ] `[profile.release]` with debug symbols on and `panic = "abort"` off, because
      the fuzz targets need unwinding.
- [ ] Rewrite `.gitignore` for Rust; drop the Python and C++ sections.
- [ ] Rewrite `README.md` for the new tool. The old one documents a C++ teaching
      disassembler that no longer exists.
- [ ] CI on GitHub Actions: fmt, clippy with `-D warnings`, `cargo deny`, tests.
      CI runners are disposable, so CI builds dev profile on purpose.
- [ ] `CONTRIBUTING.md` with the clean-room rule: public specifications and
      published papers only, no decompiled IDA or disassembled Hex-Rays.
- [ ] Test corpus. A `fixtures/` tree of small committed binaries plus a script
      that fetches larger ones (coreutils, `libcrypto`, a Go binary, a stripped
      C++ binary, a Rust binary, a PE from a public malware corpus, an iOS dylib).
      Ground truth comes from DWARF where the fixture has it.
- [ ] Bench harness that records wall time, peak RSS and output hash per fixture,
      so a regression shows up as a number and not a feeling.
- [ ] Coverage and mutation tooling: `cargo llvm-cov` and `cargo mutants` in CI,
      with the per-crate floors from "Test coverage targets" in a checked-in
      config so raising or lowering one is a reviewed diff.

### M1. Containers

Depth-first: ELF and PE carry the workload, Mach-O follows, everything else waits.

- [ ] ELF32 and ELF64, both endians. Program headers, sections, `symtab`,
      `dynsym`, GNU hash, symbol versioning, `.dynamic`, `.init_array`,
      `.eh_frame` and `.eh_frame_hdr`, `.note.gnu.build-id`.
- [ ] ELF relocations for x86-64, AArch64 and i386, enough to load `.o` files
      and to resolve PLT entries to names.
- [ ] PE and COFF. Import and delay-import descriptors, exports, TLS callbacks,
      base relocations, resources, debug directory with the PDB path, load config,
      and the exception directory (`RUNTIME_FUNCTION` unwind data, which is the
      best function-boundary oracle Windows offers).
- [ ] Mach-O, including fat binaries, chained fixups, the exports trie, and
      `LC_FUNCTION_STARTS`, which is another boundary oracle.
- [ ] Raw blob loading with an explicit base, architecture and entry point, plus
      Intel HEX and S-record, for firmware work.
- [ ] `ar` archives and loose object files.
- [ ] Overlay detection, section entropy map, and a packer heuristic that reports
      a suspicion with its evidence rather than a verdict.
- [ ] Every loader treats its input as hostile. A malformed header returns a typed
      error; it never panics and never allocates from an attacker-controlled count.
- [ ] Later, behind a feature flag: WASM, .NET metadata, DEX, Java class files.

### M2. Instruction decoding

- [ ] x86 and x86-64 decoder, table-driven from a specification file that is
      checked into the repo and compiled at build time. Legacy prefixes, REX,
      VEX, EVEX, AVX-512, and the encodings that matter for obfuscated code.
- [ ] AArch64 A64 decoder. SVE and SME can wait; NEON cannot.
- [ ] ARM32 and Thumb-2, including interworking and the IT block.
- [ ] Differential fuzzing of each decoder against `objdump` and `iced-x86` over
      random and corpus-derived bytes. Parity on length and on operand semantics
      is a gate, not a goal. Divergences that are deliberate get a written reason
      in a checked-in list; there is no third category.
- [ ] SLEIGH runtime: load a compiled `.sla`, decode, and produce p-code.
- [ ] SLEIGH compiler: `.slaspec` to `.sla`, so Ghidra's processor tree builds
      from source instead of shipping as binary blobs. This is the single largest
      task in M2 and it unlocks RISC-V, MIPS, PowerPC, SPARC, SuperH, 6502, Z80,
      AVR, MSP430 and the rest in one step.
- [ ] Assembler for x86-64 and AArch64, needed by M10 patching. Encoding only
      from public manuals.
- [ ] Text formatting for each architecture, with Intel and AT&T syntax for x86
      and a formatter trait so a caller can render its own.

### M3. Program model and partition

- [ ] Address spaces and a memory map that survives overlays, `bss`, and a raw
      blob loaded at an arbitrary base.
- [ ] Function discovery, layered by evidence quality: symbol table, `.eh_frame`
      FDEs, PE unwind records, `LC_FUNCTION_STARTS`, Go `pclntab`, ObjC method
      lists, Swift metadata, call targets found by recursive descent, then
      prologue scanning as the last resort. Each layer tags its provenance.
- [ ] Recursive descent with a linear sweep fallback over the gaps, with the two
      reconciled rather than concatenated.
- [ ] Basic blocks, CFG, tail-call detection, no-return propagation through the
      call graph (a call to `abort` ends a block, and the fixpoint matters).
- [ ] Jump table recovery. Bounded index plus base is the easy case; the ones
      that matter are the PIC pattern, the negative-offset pattern, and MSVC's
      two-level tables.
- [ ] Cross references: code to code, code to data, data to data, with the
      reference type recorded.
- [ ] String extraction: ASCII, UTF-8, UTF-16LE, Pascal-style, Go string headers,
      and Rust `&str` slices found through their length field.
- [ ] Data flow into the data sections: pointers, vtables, jump tables and
      literal pools marked as data so the code partition stops at them.
- [ ] PLT, GOT and IAT thunk resolution, so an indirect call prints a name.
- [ ] Parallel analysis with deterministic output. Functions are independent
      units; the work queue order must not reach the result.

### M4. IR and dataflow

- [ ] A p-code-style IR with explicit varnodes and address spaces, sized to be
      generated by both the hand-written decoders and the SLEIGH runtime.
- [ ] SSA construction over the IR, with a heritage pass that handles partial
      register writes (`al` inside `rax`) without lying about them.
- [ ] Stack frame recovery: frame pointer or not, prologue and epilogue matching,
      stack depth tracking through calls, `alloca` and dynamic frames.
- [ ] Memory promotion, turning stack slots into variables where aliasing allows.
- [ ] Constant propagation, copy propagation, dead code elimination, and a rule
      pool driven to a local fixpoint.
- [ ] Value-set or range analysis, enough to bound a jump table index and to
      prove a comparison constant.
- [ ] Calling convention detection per function, including non-standard ones that
      a compiler invents for a static function.
- [ ] Prototype recovery: parameter count, storage, return value, varargs.
- [ ] Feedback edges. A prototype learned late re-runs the callers' dataflow. The
      schedule is explicit and budgeted, not a `while (changed)` around everything.
- [ ] An IR interpreter. This lands here and not in M10, because it is the only
      way to test a lifter: compile a C body for the target, run it natively for
      the answer, run the lifted IR under the interpreter, compare. Ghidra's
      PCodeTest works exactly this way and it is why their 40 processor
      specifications are trustworthy. Without it, every lifter is asserted
      correct by eye.

### M5. Types

- [ ] A C type model with structures, unions, arrays, enums, function pointers,
      bitfields and typedefs, sized per architecture.
- [ ] DWARF 4 and 5 consumption: types, variables, line numbers, inlined frames.
- [ ] PDB consumption for Windows binaries, from the public format documentation.
- [ ] Demanglers: Itanium C++, MSVC, Rust legacy and v0, Swift, ObjC selectors.
- [ ] Type archives. Parse C headers into the type model so an analyst can apply
      a known API signature. Importing Ghidra `.gdt` is worth doing if the format
      holds still.
- [ ] Structure recovery from access patterns: offsets touched through a pointer
      become fields, with the confidence recorded.
- [ ] C++ recovery: vtables, RTTI where present, constructor and destructor
      identification, `this` pointer typing.
- [ ] Go: `pclntab` function names, `moduledata`, interface tables, the runtime
      type descriptors.
- [ ] Rust: the metadata that exists, which is less than people expect. Panic
      location strings carry file and line and are worth mining.
- [ ] ObjC and Swift metadata, including Swift field descriptors and protocol
      conformances.

### M6. Decompiler

- [ ] Region identification over the CFG, producing a region tree distinct from
      the block graph.
- [ ] Structuring into if, while, for, switch and the rest, with the goto set as
      the measured quality signal. Follow the SAILR approach: make an edit,
      restructure, count gotos, keep the change or roll it back.
- [ ] Expression rebuilding from SSA, with operator precedence and cast insertion
      that is correct rather than pretty.
- [ ] Variable naming and merging, so the output reads as code and not as a
      register dump.
- [ ] C emission with a position map, so every token maps back to an address and
      the CLI can highlight, slice and cross-reference the output.
- [ ] Port Ghidra's 89 decompiler datatests to our format before the M6 gate
      opens. They encode two decades of decompiler bugs and they are the cheapest
      correctness signal available. Every bug fixed after that adds one case.
- [ ] Quality gates: goto density per function against a baseline, and a
      recompilability check on a corpus where the output is expected to build.
- [ ] M6 does not close until DecBench scores r12e above Ghidra on the
      unoptimized set: 32.2 union, 29.3 structure. See the DecBench section.
- [ ] Options are toggles, not rewrites. A user who wants low-level output and a
      user who wants idiomatic C get the same engine with different switches.

### M7. The annotation store

This is the feature that distinguishes r12e from every incumbent, so it gets
designed before it gets coded, and the design lives in `docs/design/db.md`.

- [ ] Content anchors. A function is identified by a fingerprint of its
      instruction-shape stream with branch targets excluded, so the identity
      survives a rebase and a relink; by an exact body hash for the same-binary
      fast path; and by its address as a tiebreak. Resolution reports which of
      the three matched.
- [ ] Anchors for things that are not functions: a data object, an address inside
      a function, a structure field, a call site.
- [ ] The log. One assertion per line, append-only, sorted by a sequence number
      with a content hash as the deterministic tiebreak. A fold over the log is
      the current state, and the fold is order-independent.
- [ ] Merge semantics. Two branches that annotate the same binary merge with git
      alone. A conflict on the same field of the same anchor resolves by the fold
      rule, and the tool can list which assertions lost.
- [ ] What is never stored: anything the engine can recompute. Function
      boundaries, blocks, xrefs and types inferred from bytes stay out of the
      file, so regenerating them cannot conflict.
- [ ] Undo and redo as operations on the log.
- [ ] Provenance on every assertion: who, when, and optionally why.
- [ ] A project file that records the binary hash, the load configuration and the
      analysis options, and nothing else.
- [ ] Tests that run actual `git merge` on diverging annotation branches and
      assert the folded result.

### M8. The command line

- [ ] Non-interactive subcommands that do one thing and exit: `info`, `sections`,
      `imports`, `exports`, `funcs`, `disas`, `decompile`, `xrefs`, `strings`,
      `search`, `graph`, `diff`, `patch`, `annotate`, `sig`.
- [ ] `--json` on every one of them, against a schema that is versioned and
      checked in. Breaking the schema is a major version bump.
- [ ] Stable exit codes, documented, so a script can branch on them.
- [ ] A REPL for the interactive session, with commands that read as words rather
      than as rizin's two-character grammar, plus short aliases for the commands
      people type a hundred times an hour.
- [ ] Address expressions: symbol names, `main+0x20`, `[rip+0x10]`, section
      relative, file offset.
- [ ] Paging, color, and a terminal-width-aware listing that stays diffable when
      piped.
- [ ] Shell completion for bash, zsh and fish, and a generated man page.
- [ ] Progress reporting on stderr with an estimate, because analysis of a 500 MB
      binary is not instant even when it is fast.

### M9. Automation and agents

- [ ] `r12e-api`: the stable library surface the CLI and the MCP server both use.
      Semver from 1.0, with a compatibility test suite.
- [ ] MCP server exposing open, list functions, disassemble, decompile, xrefs,
      rename, retype, comment, diff and patch preview.
- [ ] Cancellable jobs with a budget, so an agent that asks for the decompilation
      of a 40,000-function binary gets partial results and a reason.
- [ ] A batch mode that runs a script of commands and emits one JSON document.
- [ ] Scripting. Start with the batch language above; add an embedded interpreter
      only when a real workflow needs control flow. Python via an extension
      module is the likely answer and it is explicitly not in the first year.

### M10. The differentiators

- [ ] Binary diff. Function matching across two builds by anchor, by call graph
      neighborhood, and by structural hash, reporting matched, changed, added and
      removed with a similarity score. Patch diffing is the use case that has to
      work: given a vulnerable and a patched build, point at the change.
- [ ] Patch sets. An auditable object describing byte edits, previewed before
      write, applied to a sibling file by default, assembled from public
      encodings. Never a silent overwrite of the input.
- [ ] Signature matching. An open format for library function identification with
      a corpus built from real distribution packages, so a statically linked
      binary stops being 8,000 anonymous functions.
- [ ] Emulation of selected paths, built on the M4 IR interpreter with a memory
      model and syscall stubs added: string decryption, resolving an obfuscated
      control flow, confirming a jump table.
- [ ] A query language over the program model. "Find every call to `memcpy` whose
      third argument is not bounded by a constant" is a question the incumbents
      answer with a throwaway script. Making it a first-class query, over a model
      that already records provenance, is the most useful thing r12e can offer a
      vulnerability researcher.

### M11. Performance

- [ ] Published benchmark numbers against `rizin -A` and Ghidra headless on the
      fixture corpus, rerun in CI, with a regression budget.
- [ ] Lazy analysis. Opening a binary costs a header parse and a symbol table
      read; everything else happens when asked.
- [ ] An on-disk analysis cache keyed by binary hash and options, so the second
      open is instant. The cache is derived data and is gitignored.
- [ ] Memory ceiling. A 500 MB binary must analyze inside 8 GB of RAM, which
      means arenas, interning, and not storing a `String` per instruction.
- [ ] Profiling as a habit, with a flamegraph script checked in.

### M12. Hardening and release

- [ ] Fuzz targets for every parser and decoder, run in CI with a persistent
      corpus.
- [ ] Resource caps on every attacker-controlled count, with a documented policy.
- [ ] `#![forbid(unsafe_code)]` where possible, and a written justification for
      every exception.
- [ ] A no-panic gate on the loader and decoder paths, checked by fuzzing rather
      than asserted in a README.
- [ ] Static musl builds for Linux, plus macOS and Windows binaries.
- [ ] Packaging: `cargo install`, a Homebrew formula, and a release workflow that
      signs and attaches checksums.
- [ ] `MANUAL.md`, a design document per subsystem under `docs/design/`, and a
      tutorial that takes a reader from a stripped binary to a named, typed,
      committed annotation log.

## Quality gates

Green before every merge to main. Each one is a command, not a judgment call.

| Gate | What it checks |
| --- | --- |
| G1 | `cargo fmt --check`, `cargo clippy --release -- -D warnings`, `cargo deny` |
| G2 | `cargo test --release --workspace` |
| G3 | Decoder parity against `objdump` and `iced-x86` on the fuzz corpus |
| G4 | Function boundary precision and recall against DWARF ground truth, per fixture |
| G5 | Determinism: same output hash at 1, 4 and 10 threads, on two runs |
| G6 | No panic and no timeout on the malformed-input corpus |
| G7 | Decompiler goto density and recompilability against the recorded baseline |
| G8 | Benchmark wall time and peak RSS inside the regression budget |
| G9 | Annotation log merge scenarios fold to the expected state |
| G10 | Line and branch coverage at or above the floor for the crate |
| G11 | Mutation score at or above the floor for the crate |
| G12 | DecBench union and recompile rates at or above the last release, per dataset |

## Test coverage targets

Ghidra has 1,946 test files and 18,999 `@Test` methods. Copying that number is
the wrong target and it would take a decade. Look at where those tests actually
are: 615 files cover `Features/Base`, 399 cover the framework, and most of the
rest are GUI and integration tests for a UI r12e does not have. The decompiler,
which is the hardest thing in the product, has 15 Java test files, because the
real decompiler tests are 89 XML datatests driving the C++ engine. Processors
have 17.

So the count is not the measure. Four things are, and the first of them is backed by an
oracle outside this repository, which means its numbers cannot be padded by
writing more assertions about our own behavior.

### Oracle-backed suites

| Suite | What the oracle is | Reference point | r12e target |
| --- | --- | --- | --- |
| Decoder parity | `objdump` and `iced-x86` on the same bytes | rizin ships 6,333 named cases and 24,625 lines of assembly vectors | every instruction in the fixture corpus, plus 10^8 randomly generated encodings per architecture, with zero unexplained disagreements |
| Semantic lift | native execution of the same code | Ghidra's PCodeTest compiles 21 C bodies per target and emulates them | the same C bodies plus our own, executed natively and under the r12e emulator, compared on every observable |
| Function boundaries | DWARF and PE unwind records | none published | precision and recall per fixture, tracked per release |
| Decompiler behavior | recorded baseline, reviewed on change | Ghidra 89 datatests, kuna 83 files and 675 assertions | 89 ported cases before the M6 gate opens, then one case per fixed bug, permanently |
| Type recovery | DWARF types in the fixture that has them | none published | agreement rate per type category, tracked per release |
| Annotation merge | `git merge` itself | none | every scenario in the design doc, run against real git |

The decoder parity suite is the one that has to be enormous and it costs almost
nothing to grow, because the oracle generates the expected answers. A disagreement
is either a bug in our decoder or a known divergence with a written reason, and
the list of written reasons is checked in.

The semantic lift suite is the part most projects skip, and skipping it is why
lifters quietly produce wrong p-code for years. Ghidra's approach works: compile
a C body for the target, run it natively to get the answer, run it under the
emulator, compare. It is also the only way to test 40 SLEIGH specifications
without 40 experts.

### Coverage floors

Line coverage measured with `cargo llvm-cov`, enforced per crate, because a
single workspace number lets a well-tested decoder hide an untested loader.

| Crate | Line | Branch |
| --- | --- | --- |
| `r12e-format`, `r12e-arch`, `r12e-sleigh` | 90% | 85% |
| `r12e-core`, `r12e-ir`, `r12e-db`, `r12e-types` | 85% | 80% |
| `r12e-analysis`, `r12e-decomp`, `r12e-diff`, `r12e-patch` | 75% | 65% |
| `r12e-cli`, `r12e-mcp` | 60% | 50% |

Parsers and decoders get the high floor because their inputs are hostile and
their failure mode is silent. The decompiler gets a lower one because a
structuring pass has combinatorially many paths and the datatests cover what
matters better than a coverage percentage does.

### Mutation score

Coverage says a line ran. It does not say a test would have noticed if the line
were wrong, and on a decoder that distinction is the whole game: a table entry
with the wrong operand size is executed by every test and caught by none.

`cargo mutants` changes one operator, constant or return value at a time and
reports whether the suite failed. The score is the fraction of mutants killed.

| Crate | Floor |
| --- | --- |
| `r12e-format`, `r12e-arch`, `r12e-core` | 85% |
| `r12e-ir`, `r12e-db`, `r12e-types` | 75% |
| everything else | 60%, or an exemption with a written reason |

Full mutation runs are slow, so CI mutates only the diff on a pull request and
the whole workspace on a nightly. Neither Ghidra nor rizin publishes a mutation
score. Publishing ours, and holding a floor, is a claim about test quality that
a test count cannot make.

### Fuzzing

Counted by what it finds, not by whether it runs.

- Every loader, decoder and demangler has a target, run in CI against a corpus
  that is checked in and grows with every crash.
- The metric is edge coverage plateau per target, recorded per release. A target
  whose coverage stops growing has either been fully explored, which is worth
  knowing, or has a harness bug, which is worth fixing.
- A crash found by fuzzing becomes a unit test with the minimized input before
  the fix lands.

### Where the tests live

- Unit tests next to the code, for anything with a contract.
- `tests/` in each crate for behavior that crosses module boundaries.
- `fixtures/` for the binaries, with a manifest recording the source, the build
  flags and the ground truth available for each one.
- `tests/golden/` for the recorded baselines, one file per case, reviewed as part
  of the change that moves them. A baseline that moves without a reviewer saying
  why is not a baseline.


## Scorecard

The claim is that r12e is better than the incumbents, so it needs numbers that
can prove it wrong. These get recorded in `docs/scorecard.md` from the first
release and rerun every release.

| Measure | Against |
| --- | --- |
| Time from invocation to first function listing | Ghidra headless, `rizin -A` |
| Full analysis wall time and peak RSS per fixture | same |
| Function boundary F1 on stripped binaries | DWARF ground truth |
| Variable type agreement in decompiled output | DWARF ground truth |
| Goto density per decompiled function | Ghidra decompiler on the same fixture |
| Fraction of decompiled functions that recompile | absolute |
| Byte-identical output across runs and thread counts | absolute |
| Patch-diff: does the changed function rank first | a set of known CVE build pairs |

Where a number is worse than the incumbent, it stays in the table. A scorecard
that only reports wins is marketing.

### DecBench

The scorecard above is ours, which means we choose the fixtures and we grade our
own work. [DecBench](https://decbench.com) is the external check: a public
benchmark that compiles 39 projects at several optimization levels, decompiles
every function with every entrant, and scores the output against the original
source on three axes. 94,575 functions across 803 binaries, with a published
dataset and a leaderboard.

Its three metrics, none of which we chose:

| Metric | What it compares |
| --- | --- |
| Structure (GED) | graph edit distance between the source CFG and the decompiled CFG, 0 being isomorphic |
| Types | recovered variable types against DWARF |
| Recompile | recompile the decompiled function with the original toolchain, then compare assembly by Jaccard similarity with linker-dependent operands normalized away |

Union is the fraction of functions where the entrant is perfect on at least one
of the three.

Where the field stands, from the 2026-08-29 snapshot. Numbers are percent of
functions, higher is better, on the unoptimized (O0, stripped) set of 34,406
functions:

| | Union | Structure | Types | Recompile |
| --- | --- | --- | --- | --- |
| Hex-Rays | 47.9 | 45.7 | 8.7 | 0.8 |
| kuna | 46.8 | 44.8 | 8.1 | 3.0 |
| angr | 45.7 | 41.2 | 12.1 | 0.6 |
| Ghidra | 32.2 | 29.3 | 7.7 | 0.2 |
| Binary Ninja | 28.9 | 24.0 | 10.4 | 0.2 |
| r2dec | 22.1 | 21.5 | 2.3 | 0.1 |

On plain `-O2` with inlining, everything drops: kuna 31.4, Hex-Rays 30.7, angr
30.3, Ghidra 21.7. On the large-function tail the whole field collapses: kuna
1.6, Binary Ninja 0.8, angr 0.7, Hex-Rays 0.6, Ghidra 0.4.

Four things follow for this roadmap.

1. **Ghidra is not the bar,** and beating it is not the achievement it sounds
   like. It sits fourth on the default set, 15 points behind Hex-Rays. "Better
   than Ghidra" as a decompiler claim means passing 32.2 union and 29.3 structure
   on the unoptimized set, and that is the M6 exit criterion. The bar that
   matters is Hex-Rays at 47.9.

2. **Recompilation is wide open.** The best score in the field is kuna at 3.0 and
   Ghidra manages 0.2, so fewer than one function in thirty rebuilds to
   equivalent assembly anywhere. Output that actually recompiles is worth more to
   a patch-diff or a vulnerability workflow than output that reads nicely, and it
   is the one axis where a new entrant can lead instead of catching up. M6
   optimizes for it on purpose, which is why the recompilability gate is in G7
   from the start.

3. **Large functions are the other open axis.** Under 2% for everyone, on a set
   of 1,987 functions. A large optimized function is what a researcher actually
   hits in real work, and it is what a structuring pass with no budget discipline
   gives up on. Scale is already an M11 commitment.

4. **The LLM results are a scale artifact.** Codex scores 57.2 union and Claude
   Code 56.4 on the 250-function sample set, ahead of every traditional
   decompiler there. Both score 0.2 on the full 34,406-function set. Per-function
   attention from a frontier model wins when someone pays for 250 functions, and
   nobody is paying for 94,575. That argues for a fast deterministic engine an
   agent drives, which is bet 5. It does not argue that the engine is obsolete.

Tasks:

- [ ] Use the DecBench dataset as part of the M0 fixture corpus. 39 projects
      built at several optimization levels with DWARF retained is ground truth
      that already exists, and it feeds the G4 function-boundary gate as much as
      it feeds the decompiler work.
- [ ] Write a `r12e_raw.py` harness for `decbench/decompilers/raw/` so r12e is
      scored on every run rather than by us. The existing harnesses for Ghidra,
      angr and kuna are the template.
- [ ] Submit to the 250-function sample set as soon as M6 produces output at all.
      It needs no harness and no open-sourcing: decompile the kit, mail back the
      zip. An early bad score is a baseline, not an embarrassment.
- [ ] Record the DecBench numbers in `docs/scorecard.md` per release, including
      the runs where we lose.

## Not building

Each of these is a decision. Reopening one needs a reason that did not exist when
it was closed.

- **A GUI:** Not in the first year, possibly not ever from this repository. The
  library API and the JSON schema are designed so someone else can build one.
- **A debugger:** rizin and gdb do this well and it is a different product. The
  emulator in M10 runs code paths for analysis; it does not attach to a process.
- **Ghidra script compatibility:** Running Java is the thing this project exists
  to avoid.
- **Exotic architectures ahead of depth:** x86-64 and AArch64 on ELF, PE and
  Mach-O get finished before anything else gets attention, SLEIGH breadth aside.
- **Reverse engineering the incumbents' internals:** Clean-room: public
  specifications, published papers, and the source of permissively licensed
  projects used within their licenses.
- **Obfuscation-specific unpackers for named commercial protectors:** The
  emulation and query surfaces are general; shipping a bypass for a specific
  product is not the goal.

## Order of work

M0 and M1 are prerequisites for everything. M2's hand-written x86-64 decoder
comes before the SLEIGH compiler, because the fixture corpus is mostly x86-64 and
because it sets the shape of the decoder trait the SLEIGH runtime has to fit.
M3 and M4 are the long middle. M7 can be built in parallel with M3, since anchors
need only function boundaries and an instruction stream, and getting the storage
format wrong late is expensive. M6 is the hardest and last of the core work.

The first release worth announcing is M0 through M4 plus M7 and M8: a fast,
deterministic disassembler with git-native annotations and a JSON surface. That
is already a tool a researcher would use. The decompiler is what makes it a
competitor.
