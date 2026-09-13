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
| AArch64 | `objdump -d` | 1,429,650 | 0 | 99.87% |
| x86-64 | `llvm-objdump --x86-asm-syntax=intel` | 4,760 | 0 | 100% |

The AArch64 corpus is the fixture set plus libc, libstdc++, libcrypto, bash,
ls and objdump. What it does not decode is the single-structure SIMD loads and
stores, the by-element multiplies, the memory-tagging instructions, and the
Scalable Vector Extension, which is deliberately out of scope.

The x86-64 corpus is much smaller, because this machine is aarch64 and the
x86-64 material is cross-compiled. 4,760 instructions is enough to find
systematic errors and not enough to claim the breadth the AArch64 number does.
That is the honest reading of it.

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

## Determinism

`scripts/check-determinism.sh`: 35 fixtures, each analyzed at 1, 4 and 10
threads, twice each. All 105 runs produce identical output. Green.

## What is not measured

- rizin and Ghidra, because neither is installed here.
- DecBench, because there is no decompiler yet.
- Coverage and mutation scores, because the tooling is not wired up.
- Anything on a real Mach-O image, because there is no macOS linker here;
  the Mach-O tests use cross-compiled objects and a synthesized fat header.
- Anything on a real PE image, because there is no Windows linker here; the PE
  tests use a synthesized image and real COFF objects.
