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
      is a gate, not a goal.
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
- [ ] Quality gates: goto density per function against a baseline, and a
      recompilability check on a corpus where the output is expected to build.
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
- [ ] Emulation of selected paths over the IR, for string decryption, for
      resolving an obfuscated control flow, and for confirming a jump table.
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
