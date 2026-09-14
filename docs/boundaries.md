# G4: function boundaries against DWARF

`ROADMAP.md` has listed G4, "function boundary precision and recall against
DWARF ground truth, per fixture", in the quality gate table since the start.
Nothing measured it. `scripts/boundary-gate.sh` does, over 95,697 ground-truth
functions in 592 binaries from 16 real projects at three optimization levels.

```bash
cargo build --release
scripts/decbench-fixtures.sh --all     # optional but this is where the corpus is
scripts/boundary-gate.sh
```

It skips and says so when there is no corpus, like every other gate here, and
exits non-zero only when a recorded floor is missed. A full run is 48 seconds.

## Why this needs an oracle outside the repository

A boundary score computed against our own symbol reader measures agreement
between two parts of the same program. The oracle here is `readelf
--debug-dump=info`: every DWARF `DW_TAG_subprogram` with a `low_pc` and a
`high_pc` is a function whose true start and end the compiler wrote down.
`readelf` is binutils' DWARF reader, the same relationship `objdump` has to the
decoder parity gates.

Ground truth is read from the **unstripped** binary. r12e is run on a copy with
the debug information removed, so nothing it reports came from a symbol table.

## The two configurations, and why the first one is not enough

| mode | what is removed | what it measures |
| --- | --- | --- |
| `stripped` | `strip --strip-all`: symbols and every `.debug_*` | reading `.eh_frame` |
| `blind` | also `.eh_frame` and `.eh_frame_hdr` | boundary *recovery* |

`strip --strip-all` does not remove `.eh_frame`, and `.eh_frame` carries an FDE
per function with its exact start and length. A tool that reads it scores
1.000 recall on a stripped ELF and has demonstrated nothing about boundary
recovery. That is what the `stripped` table below shows, and quoting it alone
would be as self-serving as grading ourselves.

The `blind` table is the one worth reading. It is not an artificial handicap: a
Windows binary without unwind data, firmware, a static blob, and anything
deliberately hardened all arrive in exactly that state.

## How precision is scoped, which is the part worth arguing about

A stripped binary contains code the project did not compile: PLT thunks,
`_init` and `_fini`, and whatever the C runtime linked in. None of it has
DWARF, because none of it was built with `-g`. Counting all of it as false
positives would report that r12e invented 47,000 functions where it found
47,000 real ones the ground truth does not describe.

So the precision denominator is the functions r12e reported **inside a byte
range DWARF actually covers**. A reported function that starts in the middle of
a ground-truth function body is a real false positive, a split, and it counts.
A reported function in the PLT is out of scope. The wider denominator is
printed too, as `reported`, because hiding it would be the same dishonesty
pointing the other way.

`exact` is the fraction of ground-truth functions where the start *and* the
size both matched. It is the stricter number and the one that says whether the
end of a function was found rather than guessed.

## The corpus

Two corpora, and the gate uses whichever are present.

**`fixtures/build`**, built by `scripts/build-fixtures.sh`: a handful of C
files at two optimization levels plus the C++ and Go fixtures. 1,447
ground-truth functions, 1,299 of them in the one Go binary. Useful, and far too
small and too lopsided to conclude anything from.

**DecBench**, built by `scripts/decbench-fixtures.sh`: 16 upstream projects at
O0, O2 and O2-noinline with DWARF retained, 94,250 ground-truth functions in
585 binaries. This is why `ROADMAP.md` wanted the DecBench dataset in the
fixture corpus, and it is why the totals below are in the tens of thousands of
functions rather than the hundreds.

`scripts/decbench-fixtures.sh` does not copy the corpus into the checkout. It
reads each project's recipe out of the DecBench TOML, fetches and builds it in
`~/.cache/r12e/decbench` (552 MB for these 16), and writes one text file into
`fixtures/build/decbench/manifest.tsv`, which is gitignored along with the rest
of `fixtures/build`. The DecBench checkout is read-only: nothing is written
inside it, not even a `__pycache__`. It also does not use DecBench's Python
package, a virtualenv, angr or Joern; `scripts/decbench.sh` needs all of those
because it runs the benchmark's own metrics, and this one needs only the
recipe.

```bash
scripts/decbench-fixtures.sh --list          # the 39 recipes
scripts/decbench-fixtures.sh zlib bzip2      # named projects
scripts/decbench-fixtures.sh --all           # everything that builds here
DECBENCH_OPTS=O0,O2 scripts/decbench-fixtures.sh zlib
```

Sixteen of the 39 build on this machine. The rest want an autotools bootstrap,
a sysroot, or a dependency that is not here; each failure names its log under
`~/.cache/r12e/decbench/log/` and is skipped. The manifest is rebuilt from the
cache on every run rather than from that run, so adding a project adds to the
corpus instead of replacing it.

## The numbers

Measured 2026-09-14, aarch64, gcc 13.3, r12e at `03d0db8` plus the working
tree. 592 binaries, 95,697 ground-truth functions.

### stripped: `.eh_frame` present

| | bins | truth | recall | prec | exact |
| --- | --- | --- | --- | --- | --- |
| all projects O0 | 198 | 34,614 | 1.000 | 1.000 | 0.997 |
| all projects O2 | 198 | 24,758 | 1.000 | 1.000 | 0.922 |
| all projects O2-noinline | 195 | 35,026 | 1.000 | 1.000 | 0.959 |
| **TOTAL** | **592** | **95,697** | **1.000** | **1.000** | **0.953** |

Not one miss and not one false positive in 95,697 functions. Read it as "the
`.eh_frame` reader is correct", which is worth knowing and is not a boundary
result. `exact` is the informative column here: 0.953 overall, and the 0.922 at
O2 is where a function's *end* is still being guessed wrong even when its start
is handed over.

### blind: `.eh_frame` removed

Per optimization level, over everything:

| | bins | truth | scope | reported | recall | prec | F1 | exact |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| all O0 | 198 | 34,614 | 34,449 | 49,803 | 0.985 | 0.990 | 0.987 | 0.982 |
| all O2 | 198 | 24,758 | 19,068 | 34,442 | 0.683 | 0.887 | 0.772 | 0.600 |
| all O2-noinline | 195 | 35,026 | 23,366 | 38,940 | 0.599 | 0.899 | 0.719 | 0.528 |
| **TOTAL** | **592** | **95,697** | **78,194** | **124,496** | **0.766** | **0.937** | **0.843** | **0.706** |

Per project, all three levels together, largest first:

| project | bins | truth | recall | prec | exact |
| --- | --- | --- | --- | --- | --- |
| coreutils | 327 | 46,650 | 0.716 | 0.934 | 0.652 |
| shadow | 120 | 13,402 | 0.683 | 0.881 | 0.669 |
| bash | 21 | 8,257 | 0.963 | 0.994 | 0.916 |
| iproute2 | 6 | 5,053 | 0.865 | 0.985 | 0.813 |
| e2fsprogs | 3 | 5,040 | 0.950 | 0.990 | 0.930 |
| tar | 3 | 3,591 | 0.794 | 0.920 | 0.742 |
| diffutils | 12 | 2,294 | 0.759 | 0.901 | 0.667 |
| zlib | 21 | 2,195 | 0.777 | 0.929 | 0.749 |
| findutils | 3 | 1,912 | 0.745 | 0.901 | 0.701 |
| libedit | 3 | 1,528 | 0.897 | 0.974 | 0.873 |
| fixtures | 7 | 1,447 | 0.964 | 0.991 | 0.240 |
| grep | 3 | 1,291 | 0.739 | 0.931 | 0.686 |
| kmod | 3 | 1,132 | 0.793 | 0.929 | 0.777 |
| cronie | 9 | 578 | 0.905 | 0.885 | 0.894 |
| sysvinit | 42 | 542 | 0.367 | 0.713 | 0.358 |
| gzip | 3 | 469 | 0.768 | 0.876 | 0.642 |
| bzip2 | 6 | 316 | 0.737 | 0.866 | 0.642 |

Five things this says.

1. **Optimization costs a third of the recall, and inlining is not the
   reason.** 0.985 at O0 against 0.683 at O2. O2-noinline, which DecBench added
   precisely to separate inlining from the rest of optimization, scores 0.599,
   *worse* than plain O2 rather than better. Whatever is being lost is ordinary
   optimized code generation, not inlined bodies disappearing. That is worth
   saying plainly, because "inlining destroys boundaries" is the usual
   explanation and this corpus does not support it.

2. **Precision holds up far better than recall.** 0.937 blind against 1.000
   stripped. Without an unwind table r12e is not inventing functions, it is
   failing to find them, which is the better of the two failure modes and the
   one a user can work around.

3. **Size is not the predictor; the project is.** `bash` at 8,257 functions
   scores 0.963, `e2fsprogs` at 5,040 scores 0.950, and `coreutils` at 46,650
   scores 0.716. The high scorers are single large binaries with dense internal
   call graphs; the low scorers are many small binaries where most functions
   are reached only from a table or not at all.

4. **The tail is where the zeroes are.** `sysvinit` at 0.367 is the worst
   project, and inside it `readbootlog` and `fstab-decode` return nothing at
   all against three or four ground-truth functions each. Small static binaries
   with a handful of functions and no unwind information are the worst case,
   and they are worth looking at before anything in the average is.

5. **The local fixture corpus is not representative,** which is the argument
   for having DecBench at all. `fixtures` scores 0.964 recall and 0.240 exact,
   both dominated by the one Go binary whose own metadata answers the question;
   `fixtures O2` scores 0.075 blind on 53 functions, which is a
   small-denominator artifact rather than a result. 98.5% of the ground truth
   here comes from DecBench.

## Floors

The gate exits non-zero when a floor is missed. They are set a little under the
measured run, the way the lifting floors are: a floor is a regression detector
and not a target, and it is raised in the commit that moves the number.

| floor | value | measured |
| --- | --- | --- |
| stripped recall | 0.99 | 1.000 |
| stripped exact | 0.70 | 0.953 |
| blind recall | 0.75 | 0.766 |
| blind precision | 0.90 | 0.937 |

`BOUNDARY_FLOOR=0` turns the check off, for a run over a partial corpus where
the totals are not comparable to these.

## What this does not say

- **aarch64 only**, because this machine is. Nothing here has been measured on
  x86-64 code, and the discovery heuristics are not the same on a variable
  length instruction set.
- **Sixteen DecBench projects, not 39.** The recipes needing an autotools
  bootstrap or an absent dependency were skipped rather than worked around.
- **coreutils is 49% of the ground truth**, so the TOTAL row is weighted
  towards one project's style of code. The per-project table is the one to read
  before quoting a single number.
- **No comparison against another tool.** These are absolute numbers; what
  Ghidra or rizin score on the same binaries is the obvious next measurement
  and is not in this document.
- **Start matching is exact-address.** A tool reporting a function one
  instruction late scores zero for it, which is the right strictness for a
  boundary gate and is harsher than some published F1 numbers.
