# Scorecard

Measured, not claimed. Every number here comes from a command in this
repository, and the ones that go against us stay in the table.

Machine: 10-core aarch64 (WSL2), 7.5 GB RAM, Rust 1.98, release profile.
Date: 2026-09-13. Reproduce with `scripts/bench.sh` and `cargo test --release`.

## Speed and memory

`scripts/bench.sh`, best of three runs.

| binary | size | r12e (full analysis) | objdump (disassembly only) | functions / complete |
| --- | --- | --- | --- | --- |
| hello.a64.O2 | 71K | 0.00s, 3.3 MB | 0.00s, 4.9 MB | 15 / 8 |
| wide.a64.O2.o | 22K | 0.00s, 3.6 MB | 0.00s, 5.0 MB | 32 / 30 |
| ls | 194K | 0.01s, 12 MB | 0.02s, 5.1 MB | 304 / 183 |
| bash | 1.5M | 0.05s, 42 MB | 0.22s, 6.3 MB | 2,528 / 2,282 |
| objdump | 393K | 0.03s, 19 MB | 0.05s, 5.2 MB | 472 / 304 |
| libc.so.6 | 1.7M | 0.10s, 58 MB | 0.26s, 6.4 MB | 3,517 / 3,350 |
| libstdc++.so.6 | 2.5M | 0.14s, 56 MB | 0.34s, 7.5 MB | 5,610 / 2,920 |
| libcrypto.so.3 | 4.5M | 0.12s, 61 MB | aborted (SIGABRT) | 10,835 / 10,355 |

r12e is doing considerably more than objdump: recovering functions, building
control flow, resolving jump tables, tracking cross references and extracting
strings, where objdump disassembles linearly and does none of it. That it is
also two to three times faster on the larger inputs is the point, but the
comparison is not like for like and saying so matters more than the number.

Memory is the axis where r12e is worse, by roughly ten times. It keeps the
whole analysis in memory; objdump streams. On a 7.5 GB machine that is a
tradeoff rather than a problem, and it is what M11's incremental analysis is
for.

rizin and Ghidra are not installed here, so the comparison the roadmap names is
not yet made. That is a gap in the scorecard, not a result.

## Decoder correctness

The gate is a differential comparison against an external disassembler over
every instruction in the corpus. A wrong answer is a bug with no allowance; an
encoding not decoded at all is a separate number with a floor that only rises.

| architecture | oracle | instructions | wrong | decoded |
| --- | --- | --- | --- | --- |
| AArch64 | `objdump -d` | 1,640,904 | 0 | 99.85% |
| x86-64 | `llvm-objdump --x86-asm-syntax=intel` | 4,760 | 0 | 100% |
| ARM32 and Thumb-2 | `llvm-objdump-18 -d` | 3,568 | 0 | 100% |
| i386 | `llvm-mc` and `llvm-objdump`, swept | 235,357 | 0 | 99.71% |

The i386 number is a sweep rather than a corpus: every one- and two-byte
opcode crossed with prefix strings and ModRM shapes, both three-byte maps, all
256 ModRM values of all eight x87 escapes, and 200,000 random byte piles. A
compiler emits a narrow slice of an instruction set and a sweep covers the
rest; this one found 467 disagreements no fixture would have. Over the
compiled fixtures it is 100%.

Adding a static Go binary to the AArch64 corpus raised it from 1.43M to 1.64M
instructions and found five decoding bugs that the C corpus never reached: a
system register table with eight wrong entries written by hand, a 64-bit
`uxtb` and `uxth` that do not exist, the `MoveWidePreferred` test that decides
whether `orr Rd, ZR, #imm` keeps its own name or takes the `mov` alias, `sbfm`
with `imms + 1 == immr` spelled as a shift instead of `sbfiz`, and `uaddlv`
and `saddlv` accumulating into the lane width rather than twice it. The system
register table is now generated from what the assembler accepts over all
32,768 encodings an `MRS` can name, and checked against it.

The ARM32 figure is small and it is the number after a development sweep of
roughly 260,000 random and strided encodings through `llvm-objdump`, which
found and fixed about 15,000 disagreements before the fixture corpus was
measured. The sweep is the real evidence; the fixture figure is the gate.

The AArch64 corpus is the fixture set plus libc, libstdc++, libcrypto, bash,
ls and objdump. What it does not decode is the single-structure SIMD loads and
stores, the by-element multiplies, the memory-tagging instructions, and the
Scalable Vector Extension, which is deliberately out of scope.

The x86-64 corpus is much smaller, because this machine is aarch64 and the
x86-64 material is cross-compiled. 4,760 instructions is enough to find
systematic errors and not enough to claim the breadth the AArch64 number does.
That is the honest reading of it.

### Decoded from a SLEIGH language definition

The same gate, against a decoder that reads its instruction set from a file at
run time rather than having it compiled in.

| architecture | oracle | instructions | wrong | decoded |
| --- | --- | --- | --- | --- |
| AArch64 | `objdump -d` | 19,710 | 0 | 100% |
| x86-64 | `llvm-objdump --x86-asm-syntax=intel` | 5,688 | 0 | 100% |
| RISC-V 64 | `llvm-objdump -M no-aliases` | 2,567 | 0 | 100% |

RISC-V is an architecture this tool could not decode at all before, and no
RISC-V code was written to make it work: the language definition is data.
Sixteen further architectures decode noise without panic or hang.

The strongest check available is three ways at once, because two of these
already have hand-written decoders measured at zero disagreements. Running
SLEIGH over the same bytes and comparing against both names which of the two
is wrong when they differ. 19,554 agree three ways on AArch64 with none
disagreeing, and 5,688 agree on where an x86-64 instruction ends.

Spelling differences are enumerated rather than allowed in bulk: each names
the `.sinc` lines whose display differs from the oracle and why, and a
disagreement from any constructor not on that list fails the gate.

## Lifting

The IR is measured two ways. Coverage is the share of instructions inside
recovered functions that the lifter models completely; anything it does not
model emits an explicit `Unimplemented` rather than an approximation.

| architecture | instructions | lifted |
| --- | --- | --- |
| AArch64 | 617,824 | 99.64% |
| x86-64 | 13,842 | 99.95% |

The AArch64 corpus includes libc, bash and ls; the x86-64 one is the fixtures
only, because this host runs no x86 system binaries, so the two numbers are
not comparable.

What remains on AArch64 is `mrs` at 1,732 of the 2,236 gaps, which reads a
system register whose value comes from the processor and not from the program,
then the byte and bit reversals, the load-acquire and store-release forms, and
the SVE instructions in libc's string routines.

A system call is modelled rather than declared unmodelled. What the
instruction does to the register file is specified, so it is written down; what
the kernel does is not knowable from the instruction, so the result and
everything the convention lets it change is undefined rather than guessed, and
the flow still stops the interpreter. A trap changes no register on the way, so
it is complete with no operations at all.

Lifted from a SLEIGH language definition, over the same corpora: RISC-V 100%,
AArch64 99.8%, x86-64 98.5%. Every gap there is one construct, SLEIGH's
user-defined operation, which this IR has no opcode for; it is reported rather
than approximated.

Correctness is measured against a processor. One program is compiled for both
architectures and executed — natively here, under qemu for the other — and the
recorded answers are what the interpreted lifting is compared against: 59
calls across five optimization levels on each architecture, 590 executions,
with floating point compared as the exact bits the machine produced. No
expected value in that suite was written by hand.

It found bugs that reading could not: `ldpsw` and `ldnp` lifted as stores, the
signed double-width divide composing its halves without sign, signed overflow
always false at 64-bit width, the two-operand conditional-select aliases with
their condition inverted, and an eight-byte clear at offset four that straddles
two SSA locations and silently discarded the value it was meant to preserve.

SSA construction and the dataflow passes run over the same corpus: 7,726
lifted operations reduce to 915, a little over a tenth, which is the
bookkeeping lifting necessarily produces. Every SSA property is checked on
every complete function in the corpus: one definition per value, one phi input
per predecessor, phis first in their block, every use reaching a definition,
and a second optimization pass finding nothing.

## Decompiler

Two gates, and the second one is the one that matters.

Every function recovered from the fixture corpus is decompiled into one
translation unit and handed to `clang -c`, which has to accept it. That proves
the output is well formed and nothing more.

The second gate compiles the output and runs it. Every pure function in the
corpus, meaning one whose whole behaviour is its return value, is decompiled,
compiled, and called on 36 argument vectors, and the answers are compared
against the interpreter, which is itself measured against what real hardware
did with the same instructions. Nothing here is the decompiler checking itself.

It found that most of the corpus was wrong:

| after | functions measured | functions whose C disagrees with the machine |
| --- | --- | --- |
| the gate was first written | 225 | 130 |
| extension widths fixed | 225 | 69 |
| signed arithmetic widths fixed | 225 | 66 |
| byte registers fixed | 224 | 40 |
| blocks stopped being dropped | 229 | 39 |

An inverted signed comparison, found separately by the ported Ghidra
datatests, had made every `<` and `<=` in a source program reach the output
meaning its complement, on both architectures at every optimization level. It
compiled cleanly, which is why the first gate never saw it.

The gate is now a ratchet: 39 is a ceiling that fails both when the number
rises and when it falls without being recorded, because a gate that is
permanently red is a gate everyone learns to skip. Zero is the only acceptable
end state and each of the 39 is named by the failure message.

### Nothing is dropped

The most serious thing this subsystem can do is lose code, because the reader
cannot tell. Over every complete function in the corpus, **2,389 basic blocks
were vanishing from the output**, and whole inner loops with them. That is now
zero and asserted on every run.

### Gotos

A goto is honest, and it is also the thing to improve, so the count is a
ceiling that only comes down.

| | gotos over the corpus | functions needing a label |
| --- | --- | --- |
| before blocks stopped being dropped | 7,081 | |
| after, which is the honest baseline | 7,286 | 1,153 |
| after single-place block classification and tail copying | **4,489** | **1,001** |

The rise in the middle row is the price of emitting 2,389 blocks that used to
disappear: a dropped block costs no gotos. The fall is 38.4%, and it cost 6.2%
more output text.

The fixture ceiling in `quality.rs`, the share of functions needing at least
one label, came down from 0.13 to **0.07**.

What remains splits by target shape rather than by cause: 45% target a region
above 24 blocks, where duplication is the wrong tool; 31% target a region
containing a loop, where two copies would read as two different loops; 24% are
acyclic and above the copy cap, and buying those costs about 6 KB of output
per goto.

### Types

An assertion reaches the output. On a binary with no debug information,
declaring a pointer-to-struct parameter turns three anonymous 64-bit arguments
into named typed ones, emits the structure, and narrows the return. The JSON
carries every variable with its name, type, size, role and storage rather than
a count, which is why every consumer that tried to score type recovery scored
zero on nearly every function.

A function decompiles byte-identically whether asked for alone or as part of
the whole program, gated over 90 functions in three fixtures. It did not
before: asking for one left every call it makes anonymous and argument-less.

## Function recovery

Measured against the symbol table, which names every function the compiler
emitted.

| fixture | recall | notes |
| --- | --- | --- |
| hello.a64.O0 | 100% | every named function found |
| hello.a64.O2 stripped | 100% | `.eh_frame` survives stripping and carries the boundaries |

Completeness, meaning the walk finished with nothing unresolved, on real
binaries: libc 95.3%, libcrypto 95.6%, bash 90.3%, libstdc++ 52.1%. The
libstdc++ figure is the one to look at: it is full of C++ exception paths and
virtual dispatch, and the remainder is mostly genuine indirect calls that no
static analysis resolves.

Against Ghidra 12.1.3 headless, on the same binaries, counting only functions
inside the file (Ghidra puts imports in a synthetic block past the end):

| binary | Ghidra | r12e | agreed | Ghidra only | r12e only | r12e time |
| --- | --- | --- | --- | --- | --- | --- |
| driver.a64.O2 | 38 | 38 | 38 | 0 | 0 | 0.020s |
| driver.x64.O2 | 38 | 38 | 38 | 0 | 0 | 0.019s |
| hello.a64.O2 | 17 | 16 | 15 | 2 | 1 | 0.019s |

Ghidra's two extras on `hello` are the PLT resolver stub and a padding `nop`;
r12e's one extra is `__wrap_main`, a real function whose symbol has no type.
Ghidra's analysis of the same binary takes about ten seconds. Reproduce with
`scripts/compare-ghidra.sh`.

Ghidra's own decompiler could not be compared on this machine: the public
distribution ships the decompiler as a native x86-64 binary, and this host is
aarch64.

## Demangling

`c++filt` over every mangled symbol in libstdc++, 5,953 names.

| outcome | share |
| --- | --- |
| demangled exactly as c++filt does | 94.0% |
| declined, mangled name shown instead | 3.6% |
| demangled differently | 2.4% |

The 2.4% is a real defect rate and it is disclosed rather than rounded away.
The remaining disagreements are substitution-table corners in heavily nested
templates. They are display-only: a demangled name is shown, never acted on.

## Diff

A fifteen-function program with one line of code changed: one function
reported changed, fourteen identical, nothing added or removed, no false
positives. Adding two functions reports exactly those two.

There is no CVE build-pair corpus here yet, which is the measurement that would
actually settle whether the patch-diff use case works at scale.

## Fuzzing

Mutation fuzzing runs in the ordinary test suite, seeded from the corpus, with
a time budget per target. A recent run: 341,075 mutated loader inputs and
1,521,697 random ones, 2,338,351 AArch64 words and 2,185,050 x86 byte
sequences, no panics.

It found one on its first run, which is the point: a five-byte file beginning
with the ELF magic, where the class byte was read by indexing the slice rather
than through the bounds-checked reader. That was the one place in the loaders
that bypassed it.

## Determinism

`scripts/check-determinism.sh`: 35 fixtures, each analyzed at 1, 4 and 10
threads, twice each. All 105 runs produce identical output. Green.

## What is not measured

- rizin, because it is not installed here, and Ghidra's decompiler, because
  the 12.1.3 install here ships it as an x86-64 binary and this host is arm64.
- DecBench beyond one project, one optimization level and one architecture:
  see the DecBench section below for what was and was not run.
- Coverage and mutation scores as numbers: the CI jobs report them, but no
  floor is enforced yet.
- Anything on a real Mach-O image, because there is no macOS linker here;
  the Mach-O tests use cross-compiled objects and a synthesized fat header.
- Anything on a real PE image, because there is no Windows linker here; the PE
  tests use a synthesized image and real COFF objects.

## DecBench

The sections above are ours: we chose the fixtures and we grade our own work.
[DecBench](https://decbench.com) is a third-party benchmark that does not.
Full method, caveats and the defect analysis are in
[`docs/decbench.md`](decbench.md); this is the headline.

Measured 2026-09-13 against DecBench `5818d67`. zlib 1.2.13 from its
`projects/sailr` corpus, built by its own pipeline at O0 with DWARF, stripped
before the decompiler sees it: 779 functions across 7 binaries, aarch64.
Percent of functions perfect on each metric, higher better.

| | Union | Structure (GED) | Types | Recompile |
| --- | --- | --- | --- | --- |
| angr 9.3.4 | 37.0 | 34.6 | 10.2 | 0.66 |
| r12e 0.1.0 | 23.4 | 22.9 | 5.6 | 0.64 |

Behind on structure, behind on types, level on recompilation, which is the axis
the roadmap bet was open. **M6's exit criterion is not met:** it asks for
Ghidra's published 32.2 union and 29.3 structure, and this is 23.4 and 22.9.
G12 has no previous release to compare against, so this run is its baseline.

The recompile column is not a correctness score. byte_match compares
recompiled assembly by Jaccard similarity, so output that drops every call
argument still scores; the `roundtrip` gate, which actually runs the
decompiled function against the interpreter, disagrees with the machine on
over a thousand calls at this commit. Both are true of the same output.

Not scored by DecBench but measured in the same run: r12e returned C for 780
of 780 requested functions in 21s against angr's 760 and 278s, and 96.1% of
its functions recompiled after DecBench's fixup pass against angr's 88.5%.
DecBench scores each decompiler over the functions it returned, so angr's
denominator is 759 against our 779; crediting it a zero on the twenty it
missed gives it 36.1 union rather than 37.0, which does not change the
ordering.

The comparison stops at angr. Ghidra 12.1.3 is installed here but ships its
decompiler as an x86-64 binary only, so it cannot decompile on this arm64
machine at all; IDA and Binary Ninja are not installed. DecBench's published
leaderboard is x86-64 and is not comparable to this run: angr scores 45.7 union
there against 37.0 here, so the slice, not r12e, accounts for the difference.
r12e reaches 63% of angr's union on the binaries where both ran, and that ratio
is the only honest cross-reference until the corpus is built for x86-64 or the
250-function sample set is submitted.

What costs the score, in order: goto density (1.98 per function against angr's
0.57; functions r12e structures without a goto score 36.2% GED-perfect, above
angr's whole-set 34.6%, and functions with three or more score 0.0%); locals
reaching the metric with no name, offset or type, because `decompile --json`
emits only a count of them, which makes 58% of the type ground truth
unmatchable by construction; and PLT call sites emitted with no arguments and
their result read from `__clobbered()`, in 295 of the 780 functions.

Reproduce with `scripts/decbench.sh`. Not measured: any optimization level
above O0, any other project, and any architecture but aarch64.
