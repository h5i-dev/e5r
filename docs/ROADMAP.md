# Roadmap

Status: in progress, 2026-09-13. This file is the scope authority for e5r:
what it is, what gets built in what order, and what will be refused in review
rather than argued about again.

## Where it stands

| Part | State |
| --- | --- |
| workspace, guards, fixtures, CI | built (M0) |
| ELF, PE and COFF, Mach-O, raw | built (M1) |
| AArch64 decoder | built, objdump parity over 395K fixture instructions, 99.67% decoded |
| x86-64 decoder | built, llvm-objdump parity over 4,760 instructions, 100% decoded |
| SLEIGH runtime and compiler | not started (M2) |
| i386, ARM32 and Thumb-2 decoders | not started (M2) |
| functions, CFG, xrefs, strings, jump tables, no-return | built and parallel (M3) |
| IR, lifters, interpreter, SSA, dataflow | built for AArch64 and x86-64, gated against real execution (M4) |
| stack promotion, ABI model, algebraic rules | built (M4) |
| decompiler to pseudo-C | built, output gated on compiling (M6) |
| type model, DWARF, PDB | not started (M5) |
| demanglers | Itanium, Rust both schemes, MSVC names (M5) |
| annotation log, content anchors, git merge | built (M7) |
| CLI with JSON on every command | built (M8) |
| binary diff | built (M10) |
| patch, signatures, emulation, queries | not started (M10) |
| benchmarks and scorecard | built (M11) |
| fuzzing, coverage and mutation tooling | built (M12); packaging not started |

The measured numbers live in [`docs/scorecard.md`](scorecard.md),
including the ones that go against us. In short: `libc.so.6` analyzes in 0.10s
and 58 MB, finding 3,517 functions with 95.3% analyzed completely, where
`objdump -d` takes 0.26s and only disassembles; both decoders are at zero
disagreements with their oracle; memory use is about ten times objdump's, which
is the axis e5r is worse on. 164 tests, clippy clean.

e5r is a reverse engineering toolkit with a command line and an optional local
project workspace.
It loads a binary, recovers functions, disassembles, lifts to an IR, decompiles
to C, diffs two builds, and writes an analyst's findings to a text log that git
can merge. One static Rust binary, no JVM, no required project server, no
proprietary database.

The previous contents of this repository were a C++ teaching disassembler for
x86-64. It is gone from the tree as of M0 and stays readable in git history. The
x86-64 and ELF notes in `MEMO.md` survive the rewrite and move under `docs/`.

## The bets

Ghidra, rizin and IDA are each better than e5r will be for years at breadth of
architecture and at accumulated analysis lore. Beating them means picking the
axes where their design, not their effort, is the limit.

1. **Startup and throughput:** Ghidra pays JVM startup and a project import
   before it shows a function. rizin is single-threaded through most of its
   analysis. e5r memory-maps the image, analyzes functions in parallel, and
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
   codes, and a library API that the CLI is a thin client of. Not
   a headless mode retrofitted onto a GUI.

6. **Breadth through SLEIGH, depth by hand:** Writing 40 instruction decoders is
   not a good use of the next two years. e5r ships a Rust SLEIGH runtime and
   compiler so Ghidra's processor specifications load directly, plus
   hand-written decoders for x86-64 and AArch64 where speed matters. Kuna proved
   the SLEIGH port is tractable.

## Architecture

The library owns every fact. The CLI and any future UI compute
nothing of their own.

```
e5r-core      addresses, spaces, memory map, ids, error model, provenance
e5r-format    ELF, PE/COFF, Mach-O, raw, archives, overlays
e5r-arch      decoder trait, hand-written x86/x86-64 and AArch64/ARM
e5r-sleigh    .sla runtime plus the SLEIGH compiler (breadth)
e5r-ir        p-code-style IR, SSA, dataflow framework
e5r-analysis  partition, function discovery, CFG, jump tables, xrefs, strings
e5r-types     type model, DWARF, PDB, demanglers, type archives
e5r-decomp    regions, structuring, expression rebuild, C emission
e5r-db        content anchors, the annotation log, git merge semantics
e5r-diff      function matching, build-to-build diff
e5r-patch     assembler-backed patch sets
e5r-api       stable library surface and the versioned JSON schema
e5r-cli       the e5r binary
```

Dependency edges run downward only. `e5r-cli` may depend on everything;
`e5r-core` depends on nothing in the workspace.

## Milestones

### M0. Clear the ground

- [x] Copy the release-only build guards from h5i (`scripts/no-debug-guard.sh`,
      `scripts/deny-debug-build.py`) and wire the hook in
      `.claude/settings.local.json`. This machine has 7.5 GB of RAM; a dev-profile
      build of a workspace this size is not affordable.
- [x] Delete `src/`, `test/`, `script/`, `CMakeLists.txt` and the C++ build. Move
      `MEMO.md` to `docs/x86-64-notes.md`.
- [x] Cargo workspace, edition 2024, MSRV pinned, `resolver = "3"`.
- [x] `[profile.release]` with `panic = "unwind"`, because the fuzz targets need
      it. Debug symbols are off: on 7.5 GB of RAM, linking with them is the
      peak-memory step.
- [x] Rewrite `.gitignore` for Rust; drop the Python and C++ sections.
- [x] Rewrite `README.md` for the new tool. The old one documents a C++ teaching
      disassembler that no longer exists.
- [x] CI on GitHub Actions: fmt, clippy with `-D warnings`, `cargo deny`, tests.
      CI runners are disposable, so CI builds dev profile on purpose.
- [x] `CONTRIBUTING.md` with the clean-room rule: public specifications and
      published papers only, no decompiled IDA or disassembled Hex-Rays.
- [x] Test corpus. A `fixtures/` tree of small committed binaries plus a script
      that fetches larger ones (coreutils, `libcrypto`, a Go binary, a stripped
      C++ binary, a Rust binary, a PE from a public malware corpus, an iOS dylib).
      Ground truth comes from DWARF where the fixture has it.
- [x] Bench harness that records wall time, peak RSS and output hash per fixture,
      so a regression shows up as a number and not a feeling.
- [x] Coverage and mutation tooling, run on demand rather than in CI:
      `cargo llvm-cov --workspace` for per-crate line coverage and
      `cargo mutants` for the mutation score, with `mutants.toml` saying what
      not to mutate. Neither gates yet — the floors below are not met, and a
      floor nobody can pass is a floor everyone learns to skip — and a CI job
      that reports a number without gating on it buys nothing: the coverage
      run re-ran the whole suite under instrumentation for a summary line, and
      the mutation run ended in `|| true`, so it could not fail. They belong in
      CI on the day the floors become gates.

### M1. Containers

Depth-first: ELF and PE carry the workload, Mach-O follows, everything else waits.

- [x] ELF32 and ELF64, both endians. Program headers, sections, `symtab`,
      `dynsym`, GNU hash, symbol versioning, `.dynamic`, `.init_array`,
      `.eh_frame` and `.eh_frame_hdr`, `.note.gnu.build-id`.
- [x] ELF relocations for x86-64 and AArch64, enough to load `.o` files
      correctly: the absolute, relative and branch kinds a compiler emits,
      including the split immediate an `adrp` carries and the scaled
      twelve-bit offsets. Gated by running functions out of the objects and
      comparing against what the processor produced. i386 is still to do.
- [x] ELF relocations for i386, enough to load `.o` files and to resolve PLT
      entries to names. REL rather than RELA, so the addend comes out of the
      bytes being patched; seventeen types applied and every TLS type recorded
      as unhandled rather than skipped. 37 relocations compared against
      `readelf` entry for entry with zero disagreements, plus 1,828 in
      `.rel.debug_*` that were never read before.
- [x] PE and COFF. Both image and object layouts, import and delay-import
      descriptors with their IAT slots, exports, the COFF symbol table, the
      debug directory's PDB path, and the exception directory
      (`RUNTIME_FUNCTION` unwind data, the best function-boundary oracle
      Windows offers). Base relocations, resources and load config are still
      to do.
- [x] Mach-O, thin and fat, with `LC_FUNCTION_STARTS` for boundaries, the
      symbol table, dylib dependencies and the UUID. Chained fixups and the
      exports trie are still to do, as is the dyld shared cache.
- [x] Raw blob loading with an explicit base, architecture and entry point, plus
      Intel HEX and S-record, for firmware work.
- [x] `ar` archives and loose object files. GNU and BSD flavours, long names,
      both symbol index forms and thin archives, measured against `ar t` and
      `nm -s`. An archive is opened rather than loaded: it has no architecture,
      entry point or memory map, so making one an `Object` would mean picking a
      member and making every later answer about bytes the caller never chose.
- [x] Bun standalone module graphs. `bun build --compile` appends source and
      bytecode the native image does not describe. Listed rather than loaded,
      from the layout Bun's own source writes: the last trailer, the offsets
      before it, and both record sizes that layout has shipped. `module_info`
      and bytecode are reported by size and not interpreted.
- [x] Overlay detection, section entropy map, and a packer heuristic that reports
      a suspicion with its evidence rather than a verdict. Nine finding kinds,
      each with a strength; a packer is named only where a section carries that
      packer's own signature. The false-positive gate matters as much as the
      true positives: fourteen ordinary binaries, seven linked and seven
      relocatable, produce no overlay and no finding at `Inferred` or above.
- [x] Every loader treats its input as hostile. A malformed header returns a typed
      error; it never panics and never allocates from an attacker-controlled count.
- [ ] Later, behind a feature flag: WASM, .NET metadata, DEX, Java class files.

### M2. Instruction decoding

- [x] x86-64 decoder, table-driven in the Intel manual's own operand notation
      so an entry can be diffed against appendix A. Legacy prefixes, REX, the
      one-byte, two-byte and three-byte maps, mandatory prefixes, groups, and
      SSE through SSE4.2. VEX, EVEX and AVX are not written; 32-bit mode is
      not supported, because the opcodes it spends on inc/dec and the BCD
      instructions are REX prefixes in long mode.
- [x] AArch64 A64 decoder including Advanced SIMD. SVE is deliberately not
      decoded: it is a separate architecture's worth of encodings and the
      coverage number records its absence.
- [x] ARM32 and Thumb-2, including interworking and the IT block. 3,568
      instructions over twelve fixture objects against `llvm-objdump-18`, 0
      wrong and 0 undecoded, after a development sweep of roughly 260,000
      random and strided encodings that found about 15,000 disagreements.
      NEON, the parallel arithmetic, the saturating and packing instructions
      and the exception-return transfers are declined rather than guessed.
- [x] i386, the 32-bit mode of the x86 decoder. The mode rather than the
      opcodes, since the table is shared: no REX, so 0x40-0x4f are `inc` and
      `dec`; default operand and address size 32; ModRM mod=00 rm=101 is an
      absolute displacement rather than rip-relative; eight registers; the
      instructions valid only in 32-bit mode and the ones invalid in it.
      Measured against `llvm-mc` and `llvm-objdump` over a sweep of 235,357
      candidates, every one- and two-byte opcode crossed with prefix strings
      and ModRM shapes, both three-byte maps, all 256 ModRM values of all eight
      x87 escapes, and 200,000 random byte piles: 0 wrong, 99.711% decoded.
      100.000% over the compiled fixtures. What it declines is what llvm
      declines because it faults on hardware, and what it decodes where llvm
      declines is listed with the reason.
- [x] SLEIGH runtime. The `.sla` format is worked out in
      [`docs/sla-format.md`](sla-format.md) and its reader consumes all
      137 files Ghidra ships. The decode engine measures 0 wrong against
      objdump on AArch64 (19,710), x86-64 (5,688) and RISC-V 64 (2,567), the
      last being an architecture this tool could not decode at all and for
      which no code was written: the language definition is data. Sixteen more
      decode noise without panic. P-code lifts at 100% for RISC-V, 99.8% for
      AArch64 and 98.5% for x86-64, and every gap is SLEIGH's user-defined
      operation, which this IR has no opcode for.
- [x] The `.slaspec` front end: all 152 language definitions Ghidra ships
      parse, none fail, 133,097 constructors in two seconds, with the bit
      patterns reduced to masks that are honest about what they cannot pin
      down. 24 real encodings across ten architectures select their own
      constructor and no other.
- [x] SLEIGH compiler: `.slaspec` to `.sla`. Partial, and the number says how
      partial: all 152 definitions compile and read back with a model that
      agrees with the source, and a file we wrote decodes 20,000 encodings
      identically to the parsed source on RISC-V and x86-64 and all but 8 on
      AArch64. Against Ghidra's own compiler, 2 of 152 match byte for byte,
      because the payload is 43% of the reference's: the missing 57% is p-code
      templates, whose allocation rule is not established and so is not
      guessed. Where the structure is established, 150 of 152 agree on the
      space table and 148 on the constructor count.
- [x] Assembler for x86-64 and AArch64, needed by M10 patching. Encoding only,
      from public manuals, built around the decoder so it accepts our own
      disassembly verbatim: a user can copy a line out of `e5r disas`, change
      it, and assemble it back. Round trip over the whole fixture corpus, 0
      wrong on both architectures; byte-identical to `as` and
      `aarch64-linux-gnu-as` on every one of 2,535 and 1,272 comparable forms.
      A branch whose target does not fit is a typed error naming the range,
      never a truncated displacement. SIMD and floating point are refused by
      name rather than guessed.
- [x] Text formatting for each architecture, with Intel and AT&T syntax for x86
      and a formatter trait so a caller can render its own.

### M3. Program model and partition

- [x] Address spaces and a memory map that survives overlays, `bss`, and a raw
      blob loaded at an arbitrary base.
- [x] Function discovery, layered by evidence quality: symbol table, `.eh_frame`
      FDEs, PE unwind records, `LC_FUNCTION_STARTS`, Go `pclntab`, ObjC method
      lists, Swift metadata, call targets found by recursive descent, then
      prologue scanning as the last resort. Each layer tags its provenance.
- [x] Recursive descent with a linear sweep fallback over the gaps, with the two
      reconciled rather than concatenated.
- [x] Basic blocks, CFG, tail-call detection, and no-return propagation
      through the call graph. Each block records why it ended, which is what
      distinguishes a function that returns from one that only ever traps.
- [x] Jump table recovery for the absolute, base-relative and entry-relative
      forms, on both architectures. The bound comes from the compare that
      guards the switch, matched to the register the table is indexed by; a
      compact table of byte or halfword offsets is refused outright when that
      compare cannot be found, because every value in such a table yields a
      plausible target and scanning cannot honestly bound it. MSVC's two-level
      tables are still to do.
- [x] Cross references: code to code, code to data, with the reference type
      recorded, including the AArch64 `adrp`/`add` pair. Data to data is still
      to do.
- [x] String extraction: ASCII, UTF-8 and UTF-16LE, scanned by section rather
      than by segment. Go string headers and Rust slices are still to do.
- [x] Data flow into the data sections: pointers, vtables, jump tables and
      literal pools marked as data so the code partition stops at them. Five
      proofs, each something observed rather than inferred; a candidate
      overlapping a block some function walked is dropped. 55,577 regions over
      154 images, 8.72% of the bytes the gap scan sweeps. It changed no
      function anywhere -- no word inside a marked region matches a prologue
      pattern -- so it is a guard measured at zero firings, gated by a
      hand-built image whose literal-pool word *is* `stp x29, x30, [sp, #-16]!`.
- [x] A jump table whose entries are bytes scaled from a separate `adr`
      anchor, which is what gcc emits for a small dense switch at `-O1` and
      `-Os` on AArch64:

      ```
      ldrb w1, [x1, w3, uxtw]     ; a one-byte entry
      adr  x3, <anchor>           ; not the table's own address
      add  x1, x3, w1, sxtb #2    ; sign extended and scaled by four
      br   x1
      ```

      Recovery models a four-byte offset from the table's own base and not
      this, so `pick` in `em-paths.a64.O1` stays incomplete while the same
      source at `-O2` recovers. Found by the emulation gate, which confirms a
      recovered table by running the branch for every index: a table that is
      not recovered at all is the one thing that gate cannot confirm. The
      `ldrh` form, for a switch too large for a byte, is the same shape.
- [x] PLT thunk resolution from the relocation table, so a call through one
      prints the imported name. GOT and IAT still to do for the indirect
      forms.
- [x] Windows-specific entry points, which are how a PE runs code the entry
      point never reaches. TLS callbacks, the `.pdata` exception directory with
      the `.xdata` unwind info behind it (frame layout, handler, chained
      parent, and the ARM64 packed form), SEH scope tables, base relocations,
      and the load config's Control Flow Guard and SafeSEH tables, which are
      linker-built lists of real entry points the loader enforces and so carry
      their own evidence kind. Measured against `llvm-readobj` entry for entry
      over four real linked PE images, x64 and arm64 at O0 and O2, with zero
      disagreements. Still to do: the resource directory, the 32-bit `fs:[0]`
      handler chain, which is code recognition rather than a directory, and the
      `.CRT$XC*` initializer tables, which are a section-name convention.
- [x] Parallel analysis with deterministic output. Functions are independent
      units; the work queue order must not reach the result.

### M4. IR and dataflow

- [x] A p-code-style IR with explicit varnodes and address spaces. Operations
      have no implicit effects, so an instruction that sets four flags becomes
      four operations; the register file is byte-addressed, so `w0` overlapping
      `x0` is a property of the addresses rather than a rule. AArch64 lifts
      99.52% of the instructions inside recovered functions and x86-64 99.83%,
      including the integer SIMD of both and floating point.
- [x] x86-64 lifting with every flag each instruction writes, the wide multiply
      and divide its one-operand forms need, and SSE. Gated by running the same
      program on both architectures — natively here, under qemu for the other —
      and comparing the recorded answers against the interpreted lifting: 59
      calls across five optimization levels on each architecture, floating
      point compared as the bits the machine produced.
- [x] SSA construction over the IR, with partial register writes made explicit
      rather than papered over: locations are canonical whole registers, a
      narrow read becomes a `SubPiece` and a narrow write a masked merge, so
      `w0` sitting inside `x0` is a dependency dataflow can see.
- [x] Stack depth tracked through a function, so an access at a known offset
      from the entry stack pointer is recognized whichever block it is in.
      `alloca` and dynamic frames make the depth unknown, which the analysis
      reports rather than guesses.
- [x] Memory promotion, turning stack slots into variables where aliasing
      allows. It refuses when any stack address is used as a value or when two
      slots overlap without being identical.
- [x] Constant folding, copy propagation and dead code elimination, each run to
      a fixed point. On the fixture corpus they take 7,726 lifted operations to
      915, which is what turns IR into something a person can read.
- [x] An algebraic rule pool: known-bits simplification, which collapses the
      sub-register merges partial writes produce; local common-subexpression
      elimination; and pattern rules that turn flag algebra back into the
      comparison it stands for.
- [x] The default calling convention per architecture, which dead code
      elimination needs to know what the caller reads after a return and the
      decompiler needs to name arguments. Per-function detection of the ones a
      compiler invents is still to do.
- [x] Value-set or range analysis, enough to bound a jump table index and to
      prove a comparison constant. Interval domain with widening over eight
      rounds; 117 results checked, 62 of them bounded.
- [x] Calling convention detection per function. Four answers rather than two:
      standard, standard with fewer arguments where the gap in the register
      order is the evidence, non-standard with the departures named by
      register, and unknown where the lifter did not model everything, because
      an unmodelled instruction's reads are not arguments. Gated against
      `DW_TAG_call_site_parameter`, which is what the compiler knew: 33 of 37
      recorded argument registers found.
- [x] Prototype recovery: parameter count, storage, return value, varargs.
      186 prototypes recovered with no argument lost.
- [x] Feedback edges. A prototype learned late re-runs the callers' dataflow. The
      schedule is explicit and budgeted, not a `while (changed)` around everything.
      Callers also settle whether a function returns at all.
- [x] An IR interpreter, landed with the lifter as planned. Ten semantic tests
      run real compiled functions through it and compare against the answer
      computed independently in Rust: arithmetic at every width, signed and
      unsigned division including division by zero, widening, all seven
      comparisons, conditional selection, shifts and rotates, nested loops,
      and a memory-summing loop. It found two lifter bugs that reading could
      not have: signed overflow was always false at 64-bit width, and the
      two-operand conditional-select aliases had their condition inverted,
      which turned an absolute value into a negation.

### M5. Types

- [x] A C type model with structures, unions, arrays, enums, function pointers
      and typedefs, which prints a declaration the way C spells it: the
      declarator wraps around the name, so a pointer to an array is not a
      prefix and a suffix glued together.
- [x] DWARF 4 and 5 consumption: the type graph, function signatures with
      named parameters, local variables with frame offsets, and the line
      table. Relocations are applied to the debug sections first, because a
      relocatable object writes zero where an address goes. Measured against
      readelf for names and against the object's own symbol table for
      addresses.
- [x] Structure recovery from access patterns: the offsets touched through a
      pointer become fields, loop-carried pointers are followed through their
      phi so a walk reports its element size, and the result is what was seen
      rather than a conclusion. Gated against the debug information: the
      recovery runs without looking at it and has to agree.
- [x] A C type model with structures, unions, arrays, enums, function pointers,
      bitfields and typedefs, sized per architecture, and a parser that reads
      a declaration into it.
- [x] DWARF inlined frames, call sites and location lists, compared against
      `readelf` entry for entry: 39 inlined frames with their ranges and call
      lines, 16 call sites by argument count, 198 variables with location
      lists compared range for range. 230 variables in the fixtures change
      storage inside their own body, which a single-location reader gets
      wrong for most of the function.
- [x] PDB consumption for Windows binaries, from the public format
      documentation. Measured against `llvm-pdbutil` record by record on real
      databases built here by clang and lld: 14 procedures, 27 public symbols,
      24 frame-relative locals, 33 register locations by range and register
      name, 9 inlined frames, 25 section contributions. It fills the same
      structures the DWARF reader does, so nothing above that layer knows
      which format the information came from, and a database whose identity
      does not match the image is refused with a note rather than believed.
- [x] Demanglers: Itanium C++ at 94% exact parity with `c++filt` over 5,953
      real libstdc++ symbols, Rust in both schemes, and MSVC qualified names.
      Swift and ObjC selectors are still to do, and MSVC's type grammar is a
      separate job from its names.
- [x] Type archives. A whole translation unit parses into the type model: all 61
      declarations of `elf.h`, with `Elf64_Ehdr` laid out at 64 bytes checked
      against the specification rather than against a compiler, and all 91 of
      a preprocessed `stdint.h`. Importing Ghidra `.gdt` is still to do.
- [x] Structure recovery fed back into the decompiler. A declared structure
      turns an offset into the declared field name, and an inferred one turns
      it into `field_<offset>`, which is this crate saying what is at that
      offset and cannot be mistaken for something a person wrote.
- [x] C++ vtable recovery, by symbol and by scanning, reported with what each
      rests on, and gated against a fixture whose virtual dispatch is run in
      the interpreter and compared against hardware.
- [x] C++ recovery beyond the tables: RTTI where present, constructor and
      destructor identification, `this` pointer typing. Both the Itanium and
      Microsoft layouts. Over libstdc++, RTTI names 56 tables no symbol named,
      and with symbols cleared it names 156 of 211 that otherwise had only an
      address. `-fno-rtti` degrades to the tables alone and says so. It found
      a defect no fixture could: the constructor rule accepted a vtable-pointer
      store at any offset, so a class that sets a member's pointer was read as
      that member's constructor, 114 wrong classes in 335 claims; restricted to
      offset zero it is 221 claims and none wrong.
- [x] Go: `pclntab` function names and `moduledata`. 1,299 of 1,299 function
      names recovered from a stripped Go binary. Interface tables and the
      runtime type descriptors are still to do.
- [x] Rust: the metadata that exists, which is less than people expect. Panic
      location strings carry file and line and are worth mining.
- [x] ObjC class and method lists with selectors, and Swift nominal type
      descriptors, field descriptors and protocol conformances. The Swift side
      is measured against fixtures written from the published ABI, not against
      compiler output, because there is no Swift toolchain here; that is a
      weaker claim than the DWARF and Go gates and the scorecard says so.

### M6. Decompiler

- [x] Region identification over the CFG, producing a region tree distinct from
      the block graph: sequences, two-way branches joined at their immediate
      post-dominator, natural loops from back edges, and a labelled goto where
      the graph has no such shape.
- [x] Structuring into if, while and the loop forms, with break and continue
      taken from the loop nesting and the goto count reported as the quality
      signal. Switch recovery and the SAILR edit-and-measure loop are still to
      do.
- [x] Expression rebuilding from SSA, with operator precedence and cast
      insertion that is correct rather than pretty, and the reinterpretations
      between a value's bits and the number they stand for written down
      wherever the two disagree.
- [x] Variable naming: a value read more than once or produced by a phi becomes
      a named local, a promoted stack slot becomes a named variable, and
      arguments are named from the calling convention. Merging variables that
      share storage across their live ranges is still to do.
- [x] C emission carries every variable with its name, type, size, role and
      where the machine kept it, which is what a consumer needs to match
      against what the source declared. A token-level position map, so the CLI
      can highlight and slice, is still to do.
- [ ] Port Ghidra's 89 decompiler datatests to our format before the M6 gate
      opens. 61 cases are ported, representing roughly 48 of the 89; the rest
      need processors we do not decode, user-applied data types we have no way
      to attach, or assert on Ghidra's own SSA dump. 56 pass and 5 stay
      `#[ignore]`d, each naming a real defect, so the list of known defects
      lives in the test suite rather than in someone's head.
- [x] Quality gates: goto density per function against a ceiling that only
      comes down, and a recompilability check — every function recovered from
      the fixture corpus is decompiled into one translation unit that `clang`
      has to accept. Density is zero at O0, O1 and Os on both architectures and
      0.24 per function at O2 and O3.
- [ ] M6 does not close until DecBench scores e5r above Ghidra on the
      unoptimized set: 32.2 union, 29.3 structure. **Measured 2026-09-13: 23.4
      union, 22.9 structure.** Not met. The gap is structuring: 1.98 gotos per
      function against angr's 0.57, and the 124 functions with three or more
      score zero on structure, every one of them.
- [ ] Options are toggles, not rewrites. A user who wants low-level output and a
      user who wants idiomatic C get the same engine with different switches.

### M7. The annotation store

This is the feature that distinguishes e5r from every incumbent, so it gets
designed before it gets coded, and the design lives in
[`docs/design/db.md`](design/db.md).

- [x] Content anchors. A function is identified by a fingerprint of its
      instruction-shape stream with branch targets excluded, so the identity
      survives a rebase and a relink; by an exact body hash for the same-binary
      fast path; and by its address as a tiebreak. Resolution reports which of
      the three matched.
- [x] Anchors for things that are not functions: a data object, an address inside
      a function, a structure field, a call site.
- [x] The log. One assertion per line, append-only, sorted by a sequence number
      with a content hash as the deterministic tiebreak. A fold over the log is
      the current state, and the fold is order-independent.
- [x] Merge semantics. Two branches that annotate the same binary merge with git
      alone. A conflict on the same field of the same anchor resolves by the fold
      rule, and the tool can list which assertions lost.
- [x] What is never stored: anything the engine can recompute. Function
      boundaries, blocks, xrefs and types inferred from bytes stay out of the
      file, so regenerating them cannot conflict.
- [x] Undo and redo as operations on the log.
- [x] Provenance on every assertion: who, when, and optionally why.
- [x] A project file that records the binary hash, the load configuration and the
      analysis options, and nothing else. It names the binary by content as well
      as by path, so a rebuilt binary is refused and a moved one is a distinct,
      usable verdict.
- [x] Tests that run actual `git merge` on diverging annotation branches and
      assert the folded result.

### M8. The command line

- [x] Non-interactive subcommands that do one thing and exit: `info`, `sections`,
      `imports`, `exports`, `funcs`, `disas`, `decompile`, `xrefs`, `strings`,
      `search`, `graph`, `diff`, `patch`, `annotate`, `sig`.
- [x] `--json` on every one of them, against a schema that is versioned and
      checked in. Breaking the schema is a major version bump.
- [x] Stable exit codes, documented, so a script can branch on them.
- [x] A REPL for the interactive session, with commands that read as words
      rather than as a two-character grammar, plus short forms for the ones
      typed a hundred times an hour. It runs the command line's own dispatch
      against one analysis, so a session and a one-shot invocation cannot
      disagree about what a command means, and five commands on libcrypto cost
      0.63s in a session against 1.26s as five invocations.
- [x] Address expressions: symbol names, `main+0x20`, `[rip+0x10]`, section
      relative, file offset.
- [x] Paging, color, and a terminal-width-aware listing that stays diffable when
      piped. All three are decided once from whether standard output is a
      terminal, so piped output is byte-identical to what it was before they
      existed. `NO_COLOR`, `PAGER` and `E5R_PAGER` are honoured; `--color` and
      `--no-pager` override. JSON is never coloured or paged.
- [x] Shell completion for bash, zsh and fish, and a generated man page, both
      generated from the command tree so neither can describe a command that
      does not exist.
- [x] Progress reporting on stderr with an estimate. `--progress` covers the
      loops the CLI drives, with a rate-based estimate, silent unless stderr is
      a terminal. The inside of `analyze()` now reports too:
      `Session::with_progress` takes a callback, five stages report through it,
      the `Update` allocates nothing, and every report is made from the
      sequential merge between parallel batches so nothing contends. Cost is
      indistinguishable from noise.

### M9. Automation and agents

- [x] `e5r-api`: the library surface the CLI and the tests share, so a
      difference between what a test checks and what a user gets is a
      difference a user will find. Decompilation, shapes, signatures,
      emulation and queries go through it.
      Semver from 1.0, with a compatibility test suite.
- [x] ~~MCP server~~. Built in M9 and **removed**: it exposed eight of the
      twenty-nine commands, so it was never the complete agent interface it
      was advertised as, and everything it did was already reachable through
      `--json` and a documented exit code. A second protocol over the same
      library is a second surface to keep in step with the first, and the
      first one is the one that is complete.
- [x] Cancellable jobs with a budget, so an agent that asks for the decompilation
      of a 40,000-function binary gets partial results and a reason. `--budget`
      in seconds and `--limit` in items, on `decompile` and `disas`. The clock
      starts when the command does, so loading and analysis count against it,
      and the reason goes to stderr so a partial document is still a valid
      document.
- [x] A batch mode that runs a script of commands and emits one JSON document,
      each result carried with the command that produced it.
- [ ] Scripting. Start with the batch language above; add an embedded interpreter
      only when a real workflow needs control flow. Python via an extension
      module is the likely answer and it is explicitly not in the first year.

### M10. The differentiators

- [x] Binary diff. Function matching across two builds by anchor, by name and
      by call graph neighborhood, reporting matched, changed, added and removed
      with a similarity score, gated on a patched build where the change is
      known.
- [x] Diff at instruction granularity inside a changed function, so the answer
      is the line that changed rather than the function that contains it.
      Patience alignment over a per-instruction shape token that leaves out
      exactly what an insertion moves, which is the address a branch or a
      pc-relative computation resolves to. An aligned pair whose addresses then
      differ is either displaced, which the alignment inside the function and
      the function matching outside it can prove, or retargeted, which is a
      claim about the program and is never folded into the other. Gated on
      three build pairs whose source difference is one line, with the edit list
      asserted instruction for instruction: an operator substituted is one
      replacement and nothing else, a statement added is four insertions and
      one displaced branch, a statement removed is three deletions and one.
      `_start`, which the function-level diff calls changed because every byte
      of its calls moved, reports no change in it at all.
- [x] Patch sets. An auditable object describing byte edits, previewed before
      write, applied to a sibling file by default. A set applies as a whole or
      not at all, overlapping edits are a conflict rather than an order-dependent
      result, and an edit is always the same length as what it replaces.
      Assembling an edit from mnemonics still waits on the assembler.
- [x] Signature matching, in a sorted text format that reviews in a diff.
      A library built from a binary with symbols recovers 10 of 11 names in
      its stripped copy with none wrong. It refuses every coin flip: two
      signatures that disagree about a hash name nothing, a function shorter
      than twenty-four instructions is not identified by shape, and import
      thunks are excluded because four instructions that differ only in an
      offset match across binaries by coincidence.
- [x] Signature matching against published libraries: a corpus built from real
      distribution packages, so a statically linked binary stops being 8,000
      anonymous functions. `scripts/build-siglib.sh` takes `.deb`, `.rpm` or
      tarball packages, installed packages by name, or bare `.a` files,
      extracts the static libraries, and turns every named function in every
      archive member into one signature with the member it came from recorded
      beside it. Measured on a stripped `-static` build of `hello.c` against
      this distribution's own `libc.a`, `libm.a` and `libc_nonshared.a`: 3,228
      signatures from 2,016 archive members recover 497 of the binary's 908
      names, 54.7%, with 0 wrong. The oracle is the unstripped copy's symbol
      table, read as the set of names at each address, because a linker puts
      `strlen` and `__strlen` on the same byte and either is right.

      The sentence this replaces read "an importer for the a corpus built from
      real distribution packages": the format's name was lost in an edit, and
      the format was IDA's FLIRT `.sig`. That importer is declined rather than
      postponed. Hex-Rays publishes the FLAIR tools and documents the text
      `.pat` files they emit; it does not publish the byte layout of the `.sig`
      container, and every description of that layout in circulation is
      somebody's reverse engineering of the tool, which CONTRIBUTING.md's
      clean-room rule forbids reading. Even the documented `.pat` half could
      not *match* anything without reimplementing FLIRT's own CRC16 over the
      bytes past the leading pattern, and that polynomial is written down in
      the same reverse engineering and nowhere else. The archives in a
      distribution's development packages carry the same code under the same
      names, are what a statically linked binary was built from, and need no
      reading of anyone's format.
- [x] Emulation, built on the M4 IR interpreter: `e5r emulate` runs a
      function with given arguments and reports what came back and what it
      touched. Nothing escapes the process. Gated against the processor by
      running the oracle's case table through it.
- [x] Emulation of selected paths, with a memory model and syscall stubs. All
      three uses gated against a processor: a decrypted string equal to the
      bytes the hardware produced, a masked pointer table yielding exactly its
      three real targets after static analysis settled nothing, and five
      recovered jump tables confirmed by running the branch for every index.
      Nothing escapes the interpreter: the stubs are answers, not actions.
- [x] A query language over the program model, over seven entities with
      boolean operators, brackets and JSON on the same command. A field that
      does not exist is a typo and says so rather than matching nothing.
- [x] Query over dataflow facts. `calls to "memcpy" where arg3 is not bounded`
      answers, and the value is in the negation: `unconstrained` is a claim
      about the program, `unknown` is a claim about the analysis, and they are
      separate verdicts never printed as each other. Every row carries a
      strength. Still to do: interprocedural bounds, so a wrapper one level
      deep stops hiding the answer, and relational bounds, so "bounded by the
      size of the destination" becomes askable.

### M11. Performance

- [x] Published benchmark numbers against `rizin -A` on the fixture corpus,
      rerun in CI, with a regression budget. 16 binaries, 21x to 3,291x faster
      and 2.4x to 8.6x less memory, with the three qualifications that ratio
      needs in the table rather than under it, and the one row e5r loses left
      in. `docs/benchmarks.md`, `scripts/bench-budget.json`. Ghidra's headless
      analyzer is wired and opt-in behind `GHIDRA_INSTALL_DIR`, but its
      decompiler ships x86-64 only, so on this aarch64 host the comparison that
      would matter most cannot be made.
- [x] Lazy analysis. A session computes functions, cross references and strings
      on first use, memoized, so a command no longer has to be told what to
      switch off. `funcs` on libcrypto goes from 0.086s and 55.3 MB to 0.069s
      and 50.7 MB.
- [x] An on-disk analysis cache keyed by content hash, format version and the
      option bytes each part reads. A hit is 2.7 to 3.1x; a miss costs 25 to
      35% more than no cache at all. A key mismatch is a miss and never a
      partial reuse, and a damaged file is a miss with a warning, checked by
      corrupting real entries at 1,328 positions with no wrong answer.
- [x] Memory ceiling. Peak resident falls 47.7% on the largest binary here and a
      500 MB one extrapolates to 4.6 to 6.4 GB where every model before put it
      at 8.0 to 8.7. Interning the block table by range is most of it: 8.47M
      stored blocks were 2.69M distinct ranges, held once per function that
      could reach them. Wall time is unchanged and is not claimed as a win.
- [x] Profiling as a habit, with `scripts/flamegraph.sh` checked in and run
      rather than merely written. It found that `e5r funcs` spends 12.3% of
      its time computing content anchors for every function before printing
      anything.

### M12. Hardening and release

- [x] Mutation fuzzing of every loader and decoder, running in the ordinary
      test suite rather than behind a nightly toolchain, seeded from the real
      corpus and bounded by time. It found a panic on its first run: a
      five-byte file beginning with the ELF magic, where the class byte was
      read by indexing the slice instead of through the reader. A `cargo-fuzz`
      setup for longer runs is still to do.
- [x] Resource caps on every attacker-controlled count, with a documented
      policy in [`docs/design/limits.md`](design/limits.md): bound by
      the file first, then by the cap, check the cursor advanced, and read
      through the reader. Checked by the mutation fuzzer in the ordinary test
      suite rather than by review.
- [x] `#![forbid(unsafe_code)]` on every crate except `e5r-cli`, which is
      `#![deny(unsafe_code)]` so one audited call can opt in. There is exactly
      one exception, the memory map, and its justification is in
      [`docs/design/limits.md`](design/limits.md).
- [x] A no-panic gate on every path that reads foreign bytes, 1.26 million cases
      inside a 12-second budget so it runs every time rather than nightly. It
      asserts three things and not one: no panic, a per-case ceiling, and that
      the object which comes back is self-consistent. It found three defects,
      all the same mistake of adding a number the file chose to an address
      without checking, and all three are fixed.
- [x] Static musl builds for Linux, both architectures, built and run: 4.4 MB
      aarch64 and 5.5 MB x86-64, no interpreter and no shared library, with
      the x86-64 one executed under qemu and the aarch64 one producing output
      byte-identical to the glibc build. The recipe needs no musl-gcc, no
      `cross` and no container, because rust-lld and the self-contained crt
      objects ship with rustup. macOS and Windows compile here and cannot be
      linked or run here, and the workflow marks both unverified rather than
      implying otherwise.
- [x] Packaging. `cargo install` works and is checked by the workflow rather
      than asserted: installed into an empty root and run from outside the
      checkout, where the absent fixtures break nothing. `cargo package
      --workspace` succeeds for all 14 crates. Signing is Sigstore keyless
      through the workflow's own identity, so no secret is stored, and it
      degrades to unsigned checksums rather than failing the release.
      `install.sh` is the install path, and it has been run: against a real
      archive served locally, and against a tampered checksum, a missing
      `SHA256SUMS` and a missing archive, each of which it refuses. The draft
      Homebrew formula it replaced had never been run at all.
- [x] `MANUAL.md`, a design document per subsystem under `docs/design/`, and a
      tutorial that takes a reader from a stripped binary to a named, typed,
      committed annotation log (`docs/tutorial.md`).

## V0. Binary-level Lean firmware research (2026-10-28 authorization)

The owner explicitly reopened the architecture-priority exclusion for this
narrow research milestone. The new reason is a concrete binary-to-ISA-to-Lean
verification experiment, using the existing ELF loader rather than trusting
heuristic CFGs, IR or decompiled C. This does not reorder the general decoder
or decompiler roadmap or authorize a firmware framework.

- [x] Small real bare-metal RV32I ELF, loaded through e5r and exported with
      original file bytes, initial mapped memory, permissions and file offsets.
- [x] Lean decodes the original fetched instruction words; an independent Lean
      ELF reader checks the exported memory against the original-byte literal.
      The runner checks that literal against every input-file byte as well as
      recording SHA-256 identities. A digest alone is not exporter fidelity.
- [x] Strict instruction subset, wraparound, x0, signed immediates/branches,
      permission/alignment/bounds faults and explicit unsupported/fuel failure.
- [x] All byte inputs: successful bounded reachability, exact clamped output,
      output bound and whole-memory frame; real Lean kernel checking and axiom
      audit. No compiler, Rust, hardware or Embassy verification claim.
- [x] Original `no_std` Rust fixture at O1 and O2 against the same binary spec,
      with an explicit memory ABI and pinned compiler. QEMU differential edge
      tests supplement, rather than prove, ISA model fidelity.
- [x] Superseded by F below: the owner's second authorization (2026-10-28)
      turns this research result into a staged, scoped product.

The supported subset, exact statements, build commands, assumptions, provenance
and trusted computing base are together in
[`verification-rv32.md`](verification-rv32.md). Implementation is isolated in
`e5r-verify` and `verification/rv32`; no empty firmware crate or CI profile change.

## F. Scoped firmware verification (2026-10-28 owner authorization)

The owner expanded V0 into a production tool for one scope: a binary-level,
Lean-kernel-checked safety guarantee for firmware on one RISC-V board. This is
the only architecture exception; it does not reorder M1-M12 or the decoder
priorities, and nothing in it trusts e5r's decompiler, CFG recovery or IR.
Product documentation is [`firmware-verification.md`](firmware-verification.md).
Each item is checked only when its acceptance criterion has been run.

- [x] **F1. Stable baseline.** V0 committed as inherited, its fixture-corpus
      regression fixed, re-checked from a clean clone. *Accepted:* V0 checker
      exits 0 from a fresh clone with identical image hashes; the workspace
      failures that remain are the corpus-gated tests that need
      `scripts/build-fixtures.sh` prerequisites absent on the dev host.
- [x] **F2. One supported scope.** SiFive HiFive1 Rev B (FE310-G002, E31
      RV32IMAC), M-mode only, boot at `0x20010000`, 16 KiB DTIM, CLINT timer.
      *Accepted:* `boards/hifive1-revb.json` is the single source of the memory
      map, device registers, boot assumptions and exclusions; the Lean board is
      generated from it and the checker refuses a stale copy; the product doc
      states guarantees and exclusions in the same terms. (Accepted
      2026-10-29.)
- [x] **F3. Semantics for real compiler output.** RV32IMAC + Zicsr + Zifencei
      + MRET/WFI, machine-mode CSRs, interrupt entry, aligned RAM, flash image,
      device registers; unsupported behavior fails closed. *Accepted:* QEMU
      `sifive_e` whole-firmware trace replay agrees on every register after
      every transition; instruction-level differential cases cover every
      supported opcode class; negative controls show each fault class.
      (Accepted 2026-10-29: 62,773-transition firmware replay with 170
      interrupts; ~30k random instructions over all 84 kinds; 30 controls.)
- [x] **F4. Symbolic and compositional proofs.** *Accepted:* the clamp
      binaries are proved for all 2^32 inputs including the wrapping case; a
      loop over a buffer is proved by an invariant, not unrolling; function
      contracts state pre/postconditions and frames; at least one successful
      execution is exhibited (nonvacuity); the axiom audit shows only
      `propext`, `Quot.sound` and `Classical.choice`. (Accepted 2026-10-29:
      `clamp_all`, `duty_contract`, both `nonvacuous`.)
- [ ] **F5. General workflow.** *Accepted:* `e5r-verify check` takes a job
      file (ELF, board, property, entry/boot model) and returns structured JSON
      with one of `proved`, `counterexample`, `unknown`, `unsupported`,
      `resource_exhausted`, `error`; resource limits and resumable runs; a new
      target needs a job file, not a new runner; a counterexample is reported
      only after it replays in the model. *Done:* job files, the statuses
      (a failed proof is never a counterexample), limits, `--resume`,
      stale-result detection, a new target needs a job file plus its proof
      module. *Open:* automatic proofs (the F7 checker) and a counterexample
      producer with replay, so `counterexample` is still never emitted.
- [x] **F6. Environment model for the board.** *Accepted:* boot state, CSRs,
      interrupt entry/return, CLINT/UART/PWM registers and environmental
      nondeterminism are explicit and documented; replay against QEMU covers
      interrupts and device traffic. (Accepted 2026-10-29.)
- [ ] **F7. Embassy firmware proof.** One executor, timer interrupt, channel,
      built with plain cargo. *Accepted:* a kernel-checked theorem that, from
      every boot state the board allows and under every environment behavior
      the model allows, the emitted binary never leaves the modeled envelope
      and every PWM duty write is at most 100; plus a concrete execution that
      reaches such a write. *Status:* not proved. The checker
      (`Theories/Absint.lean`) is proved sound (`check_sound`, and
      `check_sound_hybrid` with directly proved regions and summaries),
      kernel-replayed, standard axioms only. With per-partition interrupt
      invariants (e41afad) and the proved ring-head summary, the analyzer
      found a certificate with no possible-fault report (65,845 nodes,
      2026-10-29). It is **resource-limited, not accepted**: its 29 MB source
      does not elaborate within 24 GB (aborted after 593 s at 13.8 GB
      resident), and the checker's list-indexed node lookup would make kernel
      evaluation quadratic. Open: an O(log n) node index and a compact
      certificate encoding, fewer nodes (the review worker's channel-tail
      summary), and the checking job. See `firmware-verification.md`.
- [ ] **F8. Packaging.** *Accepted:* pinned toolchains, one command that
      rebuilds and rechecks from source, proof bound to ELF bytes, board,
      property, model and toolchain hashes with stale results refused, CI job,
      malformed-input tests, schema/version policy, tutorial, residual TCB,
      and an independent review recorded (or recorded as not obtained).
      *Done:* pinned toolchains, `scripts/check-firmware-verification.sh`,
      result binding and staleness, CI job (not yet run on a runner),
      malformed-input and runner controls, schema names, docs, an
      installation guide (`firmware-verification-install.md`), Lean-only
      offline recheck bundles (`e5r-verify bundle`), kernel replay of every
      module (`leanchecker`), and an independent review by a separate
      reviewer agent session (findings fixed and recorded in
      `firmware-verification.md`). *Open:* a review by a human RISC-V or
      Lean expert, and a first green CI run on a GitHub runner.

## R. RMK on RISC-V (2026-10-29 owner authorization)

The next product target is upstream [RMK](https://github.com/rmk-rs/rmk),
RISC-V only, pinned at `71556128fa72881fc35f0bf6c292d5e28ad9568d`. The first
acceptance target is its existing example `examples/use_rust/qemu-riscv-rynk`
(`riscv32imac-unknown-none-elf`, Embassy executor, mock time, a UART16550 at
`0x10000000`, semihosting, the Rynk host protocol through
`HostService::run_session`, `LockConfig { insecure: true }`). It is not a
replacement toy, and nothing here claims RMK as a whole is verified. The
HiFive1 board model is not reused for it: QEMU `virt` is a different machine.
ESP32-C3/C6 BLE examples are a later phase. Abstract interpretation stays
optional; direct and hybrid proofs are equally valid routes.

- [ ] **R0. Pinned, reproducible target.** *Accepted:* source pin, toolchain,
      features and `Cargo.lock` recorded; one command rebuilds the ELF with
      plain cargo, byte-identical across two clean builds and checkout paths;
      its sha256 recorded with the symbols of the Rynk session and frame
      handling; the example runs on the pinned QEMU.
      *Status:* not accepted. Evidence pin: `f39d833f…` (built inside the
      review worker's scratch tree, no remapping); it is not cleanly
      reproduced: the third worker found an in-place rebuild there with the
      same bytes, not a fresh-checkout, fresh-cache build, and no other path
      can give it. Canonical recipe (`verification/rv32/rmk/build-canonical.sh`):
      reproducible byte for byte (`5871dcee…`, three times, two independent
      scripts, `verification/rv32/rmk-r0-audit/AUDIT.md`) ONLY at its fixed
      checkout path on this machine. The checkout path changes code, not only
      layout (66,551 `.text` bytes between two remapped paths), through
      Cargo's metadata of the path crates. Another machine, rustup home or
      user is untested. All evidence stays on `f39d833f`; migration to
      `5871dcee` (rwBase 0x80029590; memmove and deframer bytes keep their
      addresses) is not done and not implied.
- [x] **R1. Board model for QEMU `virt` (RV32).** *Accepted:* a board JSON
      (memory map, UART16550 registers, timer, boot state, how semihosting
      calls are treated: modeled, or a fail-closed exclusion) and the
      generated Lean board; whole-program replay of the R0 ELF against QEMU
      agrees on registers and device traffic, with negative controls; every
      environment assumption listed. (Accepted 2026-10-29:
      `boards/qemu-virt-rv32.json` with the read-only image carve-out and
      byte-wide UART registers; image = `RamElf.imageOf` of the packed ELF,
      reader acceptance kernel-checked; `tools/run_rmk_replay.py` replays
      299,999 transitions from the entry with 13 UART input bytes consumed,
      441 UART reads and 24 writes equal to QEMU's MMIO log, 3 semihosting
      calls taken from QEMU under stated restrictions; 8 negative controls in
      `tools/test_rmk_replay_controls.py` rejected for the expected reason.)
- [ ] **R2. Property chosen after code inspection.** Candidates: malformed
      host input (any byte sequence on the UART) never makes the emitted code
      fault or access memory outside its buffers; state mutations happen only
      through accepted, authorized commands (with `insecure: true` stated as
      an assumption, not hidden). *Accepted:* the property written as a job
      (ELF, board, entry/boot model, property) with the inspected code paths
      and why each is in or out of scope.
- [ ] **R3. First proof on emitted RMK code.** The smallest useful region,
      e.g. the Rynk frame decoder or command dispatch, proved on the emitted
      instructions for every input, every intermediate step, fault and event
      covered. *Accepted:* job `proved`, nonvacuity, mutation controls
      (changed instruction, false postcondition, weakened precondition),
      axioms audited.
      *Status (partial, not accepted):* `jobs/rmk/rmk-memmove-small.json`
      is proved on `f39d833f` (memmove n < 16, both directions; 7 negative
      controls). `jobs/rmk/rmk-memmove-contractB.json` is proved on
      `f39d833f` (`E5R.Rmk.Memmove.contractB`: n < 16 either direction, or
      n ≥ 16 forward with src ≡ dst mod 4; 7 mutation controls; re-run on
      the integrated tree: 430 s, 6.3 GB). Not covered: n ≥ 16 backward and
      the misaligned forward path, both reachable from the 488-byte deframer
      buffer. The COBS decoder is proved (COBS worker,
      `Projects/rmk/Cobs/`: `decode_in_place_report` and the wrapper
      `decode_in_place`, job `jobs/rmk/rmk-cobs-decode.json`, 9/9 controls).
      memmove is proved for every size, direction and alignment (peer:
      `Memmove.contractAll`, Projects/rmk/MemmoveBwdAll.lean, 89ab0a6).
      `Deframer/CopyDischarge.lean` proves `copy_contract : CopyContract` from
      it, with an exact bridge and no weakening. So all four deframer methods
      are proved UNCONDITIONALLY on the pinned bytes: `tail_contract`,
      `park_contract`, `unpark_contract`, `next_contract`. With them come
      `recv_step'` and `unpark_step'`. The COBS decoder is proved too (COBS
      worker; `cobs_report`).

      All 74 modules rebuild from source in 786 s and pass leanchecker, with
      standard axioms only. Not done: the panic controls as runner jobs (COBS
      worker owns the official jobs) and the session (R4).
- [ ] **R4. Toward the session.** Compose R3 with the surrounding session
      loop and interrupts (checker, direct regions or summaries). *Accepted:*
      a kernel-checked theorem about the whole `run_session` path for the
      chosen property, or a documented, measured blocker.
      *Status (partial, not accepted):* the receive step is proved
      (`recv_step'`, unconditional since `copy_contract`). `Deframer/Session.lean` `recv_step`: from
      the session loop head 0x80003e1a with the deframer invariant, a quiet
      run, for any buffer contents, reaches one of two points:
      - `Some(k)`, 2 < k ≤ 488: 0x80003e70, after `park_pending` and
        `RynkMessage::from_decoded`. Neither the bounds check 0x80003e5a nor
        from_decoded's length panic is taken, because `next` now also
        guarantees k < consumed. The message at 0x8002a580 is filled;
      - `None`: just after `tail`, with the invariant again.

      Along the way RAM writes stay in the deframer, the buffer, 0x70 stack
      bytes, s6+0x2db and the 16-byte message. `Deframer/SessionLoop.lean`
      `unpark_step`: from the unpark call site 0x80003fd8 (parked ≤ 488,
      discarding ≤ 1) back to the loop head with `SessPre`. The map is
      `verification/rv32/rmk/session-map.md`. Composition tools, proved:
      `Projects/rmk/Reach.lean` (`reach_on_runs`: quiet deterministic runs
      between checkpoints cover every Reach-able machine) and
      `Projects/rmk/PanicRegion.lean` (`panic_absorbing`, `reach_no_panic`).
      Event-aware trees (`Trees.lean`: `Lands`, `reach_lands`,
      `reach_no_escape`, `reach_no_panic_io`) cover device reads (every
      value) and writes (events). With them, `Deframer/Rx.lean` `rx_loop` (the
      UART receive poll, unconditional) is proved for every LSR/RBR value
      sequence, given the stated `RxEnv`. `Deframer/NonePath.lean`
      `none_step`: from the None point, every behaviour returns to the loop
      head with `SessPre`, or stops at an explicit read-future boundary
      (0x80003ff2 or 0x80004428). Its assumptions about the Uart16550
      struct and the task flag pointer are explicit. `Deframer/SessionInv.lean`
      composes these steps for one loop round. `SessInv` is `SessPre` plus those
      Uart16550/flag/stack facts, placed outside every proved write.
      `none_of_recv` derives `NoneAt` from it. `session_round` says that from the
      loop head with `SessInv`, every behaviour takes at least one step, with no
      fault or interrupt, and reaches one of these:
      - the loop head with `SessInv` again;
      - the read-future boundary 0x80003ff2 or 0x80004428;
      - the Some point 0x80003e70.

      `unpark_round`: from the unpark call site 0x80003fd8 with the same
      extras, back to the loop head with `SessInv`. The Some boundary
      carries `SomeAt`: the message, parked ≤ 484, discarding ≤ 1 and the
      extras. `Deframer/SomePath.lean` `some_neg` proves one branch: a
      negative message header jumps straight to the unpark site and
      returns to the loop head with `SessInv`. `Deframer/SomeRound.lean`
      `some_round` covers every header, but only against two NAMED
      callee contracts. AUDIT: the peer refuted both 07a17e5 contracts
      (3ecd81b, kernel-checked), so that `some_round` was VACUOUS. The
      dispatch side is repaired: `DispEnv` now fixes the service pointer
      0x8002a4c0, s9 = msgA and the message, and the contract takes an
      explicit world predicate `W`. SomeWitness.lean shows the repaired
      `SomeAt`/`DispEnv` are satisfiable at the observed layout. `EncEnv`
      is not yet repaired (the peer owns encode_frame, see
      verification/rv32/rmk/some-interfaces.md), so `some_round` is still
      vacuous. Both are hypotheses of the theorem and are proved
      nowhere:
      - `DispatchContract`: polling `RynkService::dispatch`'s future
        returns;
      - `EncodeContract`: `encode_frame` returns error, or a length ≤ 7.

      Each is a `Lands` statement: the ABI frame, Quiet on return, and
      the session cells it must leave alone (`Kept`). s10 = 0x8002a7f0
      (the empty response's flag byte address) is part of `SessInv`'s
      extras: recv_step, none_step and unpark_step export that x26 is
      kept, so it is no longer a hypothesis of `some_round`. Under the two
      contracts, every behaviour reaches one of:
      - the loop head with `SessInv`: an empty response, through the
        unpark site; the slice-check panic is shown not taken;
      - 0x80004204: dispatch is Pending, and the poll exits to the
        executor;
      - 0x80003fa6: dispatch returned 0xff; not proved;
      - 0x8000429e: the UART send loop; not proved.

      Not proved:
      - that `SessInv` holds when the task first reaches the loop head
        (initialization). Partly done: `Init/InitPath.lean` `init_round`
        proves that from an explicit `InitAt` at 0x80003b38 (observed
        argument, flag and UART-struct values; non-empty by
        `InitWitness.initAt_real`) every behaviour reaches the loop head
        with `SessInv`. `memset` is proved (`Init/Memset.memset_words`).
        It assumes the NAMED, undischarged `TopicsNewContract`
        (`TopicSubscribers::new`). That the first poll reaches `InitAt` is
        open;
      - `DispatchContract` (`RynkService::dispatch` at 0x800001f2 is a
        12.6 KB async state machine) and `EncodeContract`;
      - the 0xff path and the send loop;
      - the UART read future and the executor between polls (other tasks,
        interrupts, Quiet across polls).

      `SessionSafe` ranges over all of these, so it is not proved.

Not in this scope, and not to be described as done: Cortex-M, multiple harts,
DMA, U-mode/PMP, microkernels, timing or deadline guarantees, other boards,
verified Rust, verified compilers, or all of Embassy.

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
rest are GUI and integration tests for a UI e5r does not have. The decompiler,
which is the hardest thing in the product, has 15 Java test files, because the
real decompiler tests are 89 XML datatests driving the C++ engine. Processors
have 17.

So the count is not the measure. Four things are, and the first of them is backed by an
oracle outside this repository, which means its numbers cannot be padded by
writing more assertions about our own behavior.

### Oracle-backed suites

| Suite | What the oracle is | Reference point | e5r target |
| --- | --- | --- | --- |
| Decoder parity | `objdump` and `iced-x86` on the same bytes | rizin ships 6,333 named cases and 24,625 lines of assembly vectors | every instruction in the fixture corpus, plus 10^8 randomly generated encodings per architecture, with zero unexplained disagreements |
| Semantic lift | native execution of the same code | Ghidra's PCodeTest compiles 21 C bodies per target and emulates them | the same C bodies plus our own, executed natively and under the e5r emulator, compared on every observable |
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
| `e5r-format`, `e5r-arch`, `e5r-sleigh` | 90% | 85% |
| `e5r-core`, `e5r-ir`, `e5r-db`, `e5r-types` | 85% | 80% |
| `e5r-analysis`, `e5r-decomp`, `e5r-diff`, `e5r-patch` | 75% | 65% |
| `e5r-cli` | 60% | 50% |

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
| `e5r-format`, `e5r-arch`, `e5r-core` | 85% |
| `e5r-ir`, `e5r-db`, `e5r-types` | 75% |
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

The claim is that e5r is better than the incumbents, so it needs numbers that
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

- [x] Use the DecBench dataset as part of the fixture corpus, and G4 with it.
      16 of its 39 projects build here, 592 binaries at three optimization
      levels, outside the checkout. Boundary recall and precision are measured
      against `readelf`'s DWARF rather than our own reader, over 95,697
      ground-truth functions: 1.000 and 1.000 stripped, and 0.766 and 0.937
      with `.eh_frame` removed as well, which is the number that says what the
      analysis can do with nothing but code. See
      [`docs/boundaries.md`](boundaries.md).
- [x] A DecBench backend for e5r, as `scripts/decbench_e5r.py`. Out of tree,
      which DecBench's own documentation permits, so the benchmark checkout
      stays untouched. Driven by `scripts/decbench.sh`.
- [ ] Submit to the 250-function sample set as soon as M6 produces output at all.
      It needs no harness and no open-sourcing: decompile the kit, mail back the
      zip. An early bad score is a baseline, not an embarrassment.
- [x] Record the DecBench numbers in `docs/scorecard.md` per release, including
      the runs where we lose. The first run is one we lose: 23.4 union against
      angr's 37.0 on the same slice, with the method and the defect analysis in
      [`docs/decbench.md`](decbench.md).

## Not building

Each of these is a decision. Reopening one needs a reason that did not exist when
it was closed.

- **A full desktop GUI:** The 2026-10-08 request reopens the earlier UI exclusion
  for a local dashboard, durable project tasks and a decompiler pane. This
  workspace uses existing library analysis and keeps the CLI complete; it does
  not add a mandatory project service or desktop framework. See
  [`docs/dashboard.md`](dashboard.md).
- **A debugger:** rizin and gdb do this well and it is a different product. The
  emulator in M10 runs code paths for analysis; it does not attach to a process.
- **Ghidra script compatibility:** Running Java is the thing this project exists
  to avoid.
- **Exotic architectures ahead of depth:** x86-64 and AArch64 on ELF, PE and
  Mach-O get finished before anything else gets attention, SLEIGH breadth aside.
  The owner-authorized V0 research experiment and the F firmware-verification
  scope above are the only exception: one RISC-V board for binary-level
  proofs, not a general architecture expansion.
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
