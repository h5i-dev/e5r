# Benchmarks

e5r against another mature reverse engineering tool on the same binaries, with
the command that produced every number written down so it can be rerun.

The headline figures are in [`scorecard.md`](scorecard.md). This file is the
method: what was run, against what, with which flags, what the numbers do and
do not support, and what the regression budget holds them to.

## The rule this file is written under

rizin is a decade and a half of accumulated work and e5r is new. A benchmark
that flatters the new tool by measuring the wrong thing is worth less than no
benchmark, so:

- every tool gets the invocation its own documentation recommends for the job;
- the job is the same job, and where it is not, the table says so in the table
  rather than in a footnote;
- rows e5r loses stay in the table. There is one, and it is in
  [What e5r loses](#what-e5r-loses).

## The run

Measured 2026-09-14T10:22:38, load average 5.4, 5.7, 5.7 at the end of the run.
Machine: Linux 6.6.87.2-microsoft-standard-WSL2 #1 SMP PREEMPT_DYNAMIC Thu Jun  5 18:31:42 UTC 2025 aarch64, 10 cores.
Fastest of 3 runs per binary.
Measured once rather than 3: `libstdc++.so.6`, `libcrypto.so.3`.

- `e5r`: e5r 0.1.0 (target/release/e5r, sha256 6525025002f44172)
- `rizin`: rizin 0.8.2 @ linux-arm-64, package: 0.8.2 (RizinOrg)
- Ghidra: not measured, no GHIDRA_INSTALL_DIR. Its headless analyzer works on this architecture; its decompiler ships x86-64 only, so a decompiler comparison is not available on an aarch64 host either way.

rizin is the distribution package, not a build of mine: `rizin 0.8.2-1 arm64`,
installed from the project's own Ubuntu repository at
`download.opensuse.org/repositories/home:/RizinOrg/xUbuntu_24.04`. `rz-bin` is
the same package.

The e5r line carries the hash of the exact binary measured, because this
workspace is rebuilt by other agents while a run is in progress. The harness
measures a copy taken at the start of the run for the same reason: without
that, half a table can describe one build and half another with nothing saying
so. The binary measured here was built from a working tree with uncommitted
changes in `crates/`, so these numbers describe that tree and not a commit.

The machine had other work on it throughout: load average around six on ten
cores, from four other build and analysis agents. That inflates every wall time
here and adds variance to it. Two things control for it, neither perfectly:

- every number is the **fastest** of its runs, not the mean. Competing work can
  only make a run slower, so the minimum is the closest estimate of the tool's
  own cost.
- both tools were measured in the same pass, interleaved per binary, so a busy
  minute falls on both rather than on one.

What this cannot control for is a ratio between two tools measured minutes
apart on a machine whose load moved in between. Treat one significant figure of
a ratio as real and the second as noise. The absolute times are upper bounds:
an idle machine would produce smaller numbers for both tools.

## What each tool was asked to do

Three jobs are timed, because they are different questions and running them
together answers none of them.

| job | e5r | rizin |
| --- | --- | --- |
| **load**: parse the container, report what is in it, analyze no code | `e5r info <file> --json` | `rz-bin -I <file>` |
| **recover**: find the functions and nothing else | `e5r funcs <file> --json` | `rizin -N -q -c 'aa; aflj' <file>` |
| **analyze**: the tool's own full analysis, then list the functions | `e5r stats <file> --json`, timed; the list from a separate untimed `e5r funcs` | `rizin -N -q -A -c aflj <file>` |

Why each of those:

- `rz-bin` rather than `rizin` for the load row. rz-bin is rizin's own tool for
  asking what is in a container without analyzing it, and building a whole
  rizin session around the file would answer a different question.
- `rizin -A` is what the roadmap names, and what rizin's own help calls "run
  'aaa' command to analyze all referenced code". `-N` keeps a user's `rizinrc`
  out of the measurement, `-q` quits after the command, and `aflj` is the
  function list as JSON.
- **`aa` as well as `-A`, and neither row alone is the honest one.** `aaa` is
  not the same workload as `e5r stats`: on top of function recovery it
  autonames functions, recovers variables and signatures per function, and
  searches the image for values, none of which e5r produces at all. Some of
  its time buys things this table does not score. So rizin's own `aa`,
  "analyze all (fcns + bbs)", is measured beside it, to show how much of the
  cost is function recovery and how much is everything else.

  What `aa` is **not** is a fair comparison of capability. The pass that finds
  functions without symbols lives in what `aaa` adds, so `aa` on a stripped
  binary here finds two functions and nothing else. Read the `aa` row as the
  floor on rizin's cost, never as a configuration anyone would analyze a
  stripped binary with. The headline comparison stays `rizin -A` against
  `e5r stats`, which is what the roadmap names and what a user would run.
- `e5r stats` rather than `e5r funcs` for the analyze row, even though `funcs`
  is the command that produces the list. e5r's analysis is lazy, so listing
  functions does not force cross references or strings, and `aaa` computes
  those. Timing the cheaper command against a tool doing more would be the same
  error in our favour. The function list comes from a separate `funcs` run that
  is not timed.

## How the counts are made honest

A count of functions on its own is close to meaningless. A tool reporting 4,000
where another reports 3,500 may be finding five hundred more functions or
inventing five hundred addresses, and the count cannot tell you which. So every
count is split against a symbol table read by `readelf`, never by e5r:

- **recall** is the share of `FUNC` symbols the tool found, at the exact entry
  address.
- **missed (n within 16 bytes)** separates a function a tool never found from
  one whose entry it placed a few bytes late. The second is a boundary
  disagreement rather than a miss. It is still wrong, because the entry point is
  what a caller jumps to, but it is a different kind of wrong and it is not
  hidden inside the recall number.
- **unnamed (n inside a named function)** is entries the tool reports that no
  `FUNC` symbol names, with the ones falling inside a function the symbol table
  already names counted separately. Those are one function split in two, not a
  function invented out of data, and a boundary disagreement would otherwise
  cost a tool twice: once in recall and once here.
- **not in code** is entries in a section that never becomes executable. This
  one needs no symbol table at all, which is what makes it the only false
  positive count that means anything on a stripped shared library: an entry no
  symbol names may well be a real static function, but an entry in `.dynstr` is
  not a function under any reading.

Two exclusions, applied identically to every tool:

- Entries outside the file's own allocated address range are dropped. Ghidra,
  when it is measured, puts imports in a synthetic block past the end of the
  image; those are not functions in the binary.
- Entries inside `.plt`, `.plt.sec`, `.plt.got`, `.iplt` and `.mplt` are dropped
  from both the tool's list and the oracle. Import thunks are real code that no
  `FUNC` symbol names, so counting them would charge a false positive to
  whichever tool is more thorough.

### How much each oracle is worth

The `oracle` column says where the ground truth came from, and the three cases
are not equally strong.

- **`symtab of unstripped twin`** is the strongest. The fixture was stripped
  from a binary this repository still has: same bytes, same addresses, every
  name the compiler emitted. Recall and false positives are both real numbers.
- **`symtab`** is the same table read from the binary itself.
- **`dynsym only`** is the weakest, and every system binary here is in it.
  Only exported functions are named, so recall is recall over the exports and
  says nothing about the rest, and the unnamed column is not a defect count at
  all: most of those entries are real static functions. On `ls` and `objdump`
  the dynamic table defines six and two functions respectively, which makes
  their recall column almost vacuous, and it is reported rather than dropped
  only because dropping a column that looks bad for nobody is still editing.

## The numbers

Read the middle table with the caveat above: `aa` is rizin's cost floor, not a
setting anyone would analyze a stripped binary with.

### Wall time and peak memory

| binary | size | e5r load | e5r analyze | e5r peak | rizin load | rizin analyze | rizin peak |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `hello.a64.O2` | 71K | 0.00s | 0.00s | 5 MB | 0.02s | 0.05s | 24 MB |
| `hello.a64.O2.stripped` | 66K | 0.00s | 0.00s | 5 MB | 0.01s | 0.04s | 23 MB |
| `hello.static.a64` | 624K | 0.00s | 0.05s | 17 MB | 0.02s | 7.13s | 58 MB |
| `hello.static.a64.stripped` | 525K | 0.00s | 0.06s | 16 MB | 0.02s | 3.94s | 55 MB |
| `hello.go` | 1603K | 0.00s | 0.06s | 15 MB | 0.03s | 3.67s | 105 MB |
| `hello.go.stripped` | 1043K | 0.00s | 0.05s | 14 MB | 0.02s | 6.96s | 68 MB |
| `cpp-hierarchy.a64.O2.rtti` | 82K | 0.00s | 0.00s | 5 MB | 0.02s | 0.06s | 24 MB |
| `cpp-hierarchy.a64.O2.rtti.stripped` | 64K | 0.00s | 0.00s | 5 MB | 0.02s | 0.04s | 23 MB |
| `panicky` | 4469K | 0.08s | 0.14s | 56 MB | 0.02s | 5.12s | 136 MB |
| `driver.x64.O2` | 6K | 0.00s | 0.00s | 5 MB | 0.02s | 0.06s | 22 MB |
| `ls` | 194K | 0.00s | 0.02s | 12 MB | 0.02s | 0.91s | 35 MB |
| `objdump` | 393K | 0.00s | 0.03s | 16 MB | 0.02s | 0.62s | 52 MB |
| `bash` | 1506K | 0.00s | 0.11s | 33 MB | 0.03s | 9.81s | 142 MB |
| `libc.so.6` | 1682K | 0.00s | 0.14s | 43 MB | 0.04s | 12.25s | 153 MB |
| `libstdc++.so.6` | 2571K | 0.01s | 0.23s | 48 MB | 0.18s | 756.84s | 239 MB |
| `libcrypto.so.3` | 4554K | 0.01s | 0.24s | 53 MB | 0.08s | 65.55s | 452 MB |

### Function recovery alone, without the rest of a full analysis

| binary | named | e5r time | e5r found | e5r recall | e5r not in code | rizin time | rizin found | rizin recall | rizin not in code |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `hello.a64.O2` | 10 | 0.00s | 11 | 100.0% | 0 | 0.03s | 12 | 80.0% | 0 |
| `hello.a64.O2.stripped` | 10 | 0.00s | 10 | 100.0% | 0 | 0.03s | 5 | 30.0% | 0 |
| `hello.static.a64` | 913 | 0.05s | 917 | 99.6% | 0 | 2.69s | 952 | 95.3% | 0 |
| `hello.static.a64.stripped` | 913 | 0.06s | 915 | 99.5% | 0 | 0.08s | 2 | 0.1% | 0 |
| `hello.go` | 1300 | 0.05s | 1312 | 100.0% | 0 | 1.97s | 1305 | 99.2% | 0 |
| `hello.go.stripped` | 1300 | 0.05s | 1311 | 99.9% | 0 | 0.13s | 2 | 0.1% | 0 |
| `cpp-hierarchy.a64.O2.rtti` | 39 | 0.00s | 39 | 100.0% | 0 | 0.04s | 39 | 100.0% | 0 |
| `cpp-hierarchy.a64.O2.rtti.stripped` | 39 | 0.00s | 39 | 100.0% | 0 | 0.03s | 2 | 5.1% | 0 |
| `panicky` | 645 | 0.12s | 645 | 100.0% | 0 | 1.11s | 647 | 99.7% | 0 |
| `driver.x64.O2` | 40 | 0.00s | 40 | 100.0% | 0 | 0.04s | 40 | 100.0% | 0 |
| `ls` | 6 | 0.02s | 195 | 100.0% | 0 | 0.05s | 11 | 100.0% | 0 |
| `objdump` | 2 | 0.03s | 317 | 100.0% | 0 | 0.08s | 7 | 100.0% | 0 |
| `bash` | 1671 | 0.11s | 2299 | 100.0% | 0 | 2.69s | 1827 | 75.7% | 0 |
| `libc.so.6` | 2249 | 0.13s | 3497 | 99.9% | 0 | 2.88s | 2470 | 95.5% | 0 |
| `libstdc++.so.6` | 3917 | 0.23s | 4676 | 100.0% | 0 | 5.55s | 4274 | 68.8% | 0 |
| `libcrypto.so.3` | 5363 | 0.25s | 10690 | 100.0% | 0 | 5.34s | 5754 | 94.4% | 0 |

### Functions found by the full analysis, against the symbol table

| binary | oracle | named | e5r found | e5r recall | e5r missed | e5r unnamed | e5r not in code | rizin found | rizin recall | rizin missed | rizin unnamed | rizin not in code |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `hello.a64.O2` | symtab | 10 | 11 | 100.0% | 0 | 1 (1 inside a named function) | 0 | 12 | 80.0% | 2 (2 within 16 bytes) | 4 (1 inside a named function) | 0 |
| `hello.a64.O2.stripped` | symtab of unstripped twin | 10 | 10 | 100.0% | 0 | 0 | 0 | 10 | 60.0% | 4 (3 within 16 bytes) | 4 (1 inside a named function) | 0 |
| `hello.static.a64` | symtab | 913 | 917 | 99.6% | 4 (1 within 16 bytes) | 8 (8 inside a named function) | 0 | 970 | 96.5% | 32 (32 within 16 bytes) | 89 (85 inside a named function) | 2 |
| `hello.static.a64.stripped` | symtab of unstripped twin | 913 | 915 | 99.5% | 5 (1 within 16 bytes) | 7 (7 inside a named function) | 0 | 822 | 78.9% | 193 (47 within 16 bytes) | 102 (98 inside a named function) | 1 |
| `hello.go` | symtab | 1300 | 1312 | 100.0% | 0 | 12 (12 inside a named function) | 0 | 1367 | 99.9% | 2 (1 within 16 bytes) | 69 (69 inside a named function) | 0 |
| `hello.go.stripped` | symtab of unstripped twin | 1300 | 1311 | 99.9% | 1 | 12 (12 inside a named function) | 0 | 1352 | 98.7% | 17 (4 within 16 bytes) | 69 (69 inside a named function) | 0 |
| `cpp-hierarchy.a64.O2.rtti` | symtab | 39 | 39 | 100.0% | 0 | 0 | 0 | 39 | 100.0% | 0 | 0 | 0 |
| `cpp-hierarchy.a64.O2.rtti.stripped` | symtab of unstripped twin | 39 | 39 | 100.0% | 0 | 0 | 0 | 2 | 5.1% | 37 | 0 | 0 |
| `panicky` | symtab | 645 | 645 | 100.0% | 0 | 0 | 0 | 718 | 99.7% | 2 (2 within 16 bytes) | 75 (72 inside a named function) | 0 |
| `driver.x64.O2` | symtab | 40 | 40 | 100.0% | 0 | 0 | 0 | 40 | 100.0% | 0 | 0 | 0 |
| `ls` | dynsym only | 6 | 195 | 100.0% | 0 | 189 | 0 | 202 | 100.0% | 0 | 196 | 0 |
| `objdump` | dynsym only | 2 | 317 | 100.0% | 0 | 315 | 0 | 316 | 100.0% | 0 | 314 | 3 |
| `bash` | dynsym only | 1671 | 2299 | 100.0% | 0 | 628 | 0 | 2495 | 82.6% | 291 (291 within 16 bytes) | 1115 (475 inside a named function) | 1 |
| `libc.so.6` | dynsym only | 2249 | 3497 | 99.9% | 2 (2 within 16 bytes) | 1250 (3 inside a named function) | 0 | 3512 | 96.3% | 84 (84 within 16 bytes) | 1347 (132 inside a named function) | 8 |
| `libstdc++.so.6` | dynsym only | 3917 | 4676 | 100.0% | 0 | 759 | 0 | 18392 | 71.7% | 1108 (1108 within 16 bytes) | 15583 (1523 inside a named function) | 13260 |
| `libcrypto.so.3` | dynsym only | 5363 | 10690 | 100.0% | 0 | 5327 | 0 | 11451 | 97.5% | 133 (133 within 16 bytes) | 6221 (428 inside a named function) | 429 |

Across the rows where e5r's own time is above the timer's resolution, full
analysis is **21x to 3,291x** faster than `rizin -A`, and peak resident memory
is **2.4x to 8.6x** smaller. The spread on the time ratio is not measurement
noise: it is `libstdc++`, which is its own subject below.

The memory result is worth a sentence because it points the other way from the
rest of the scorecard. Against `objdump`, e5r uses about ten times the memory,
which that table calls the axis e5r is worse on. Against rizin it uses two to
nine times less, on every binary here. Both are true: `objdump` streams and
keeps nothing, and e5r and rizin both keep a program model in memory.

## What each tool found that the other did not

`scripts/compare_tools.py --explain` prints the set difference with the symbol
name at each address, because a count of disagreements says nothing about who
was right.

### rizin's exclusive entries are almost never at a symbol

On `hello.static.a64.stripped`, rizin reports 101 entries e5r does not, and
exactly **one** of them is at an address the symbol table names. e5r reports
194 that rizin does not, and **189** of those are named functions. The same
shape holds on every fixture with a complete symbol table.

Most of it is one systematic four-byte offset. On aarch64, `_init` begins with
a `nop`:

```
0000000000400250 <_init>:
  400250:  d503201f   nop
  400254:  a9bf7bfd   stp  x29, x30, [sp, #-16]!
```

rizin's entry for that function is `0x400254`. It is not a function rizin
failed to find; it is a function whose entry point it places one instruction
late, which is why the tables separate `missed` from `missed within 16 bytes`.
On `bash` every one of rizin's 291 missed entries is of this kind.

### Where the gap is real: evidence rizin does not read

`cpp-hierarchy.a64.O2.rtti.stripped` is a stripped C++ binary. e5r finds all
39 functions; `rizin -A` finds 2, and `-AA` finds the same 2. Every one of
e5r's 39 comes from an `.eh_frame` FDE:

```
$ e5r funcs fixtures/build/cpp-hierarchy.a64.O2.rtti.stripped --json | ...
38 ('.eh_frame FDE',)
 1 ('.eh_frame FDE', 'entry point')
```

The binary keeps its exception tables when it is stripped, and those tables
name the boundaries. e5r's function discovery reads them; rizin's does not,
so it is left with recursive descent from the entry point, and in a program
whose work is reached through virtual dispatch that gets nowhere. This is a
design difference rather than a bug, and it is the single largest recall gap in
the table.

### `libstdc++`, which is the outlier in every column

`rizin -A` takes **12 minutes 37 seconds** on `libstdc++.so.6` and reports
18,392 functions, against e5r's 0.23 seconds and 4,676. The count is the more
interesting number: **13,260 of rizin's 18,392 entries are at addresses in
sections that never become executable.** Its executable sections begin at
`0x9c7c0`; rizin reports functions at `0x3fc8`, `0x4000` and `0x4004`, which
are inside the dynamic symbol and string tables.

rizin's own `aa` on the same file takes 5.55 seconds and reports 4,274, none of
them outside executable memory. So the 12 minutes and the 13,260 both come from
what `aaa` adds on top, which is consistent with a prelude scan running over
the whole image rather than over code. This is one measured run of one version
on one binary, and it should be read as a lead rather than as a verdict on
rizin; the evidence for it is in the JSON the run wrote.

### Where e5r's extra entries come from

e5r reports more functions than the symbol table names on most system
binaries: 1,250 on `libc`, 5,327 on `libcrypto`. Those rows are `dynsym only`,
so the oracle names exports and nothing else, and a static function in `libc`
is not a false positive for not being exported. The column that would catch an
invention, entries outside executable memory, is **0 for e5r on every binary
in the corpus**. On the rows where the oracle is complete, e5r's unnamed
entries are 8 or fewer and every one of them falls inside a function the symbol
table already names, which is a boundary split rather than an invention.

## What e5r loses

One row, and it is the load row on `panicky`: `e5r info` takes 0.08s and
56 MB where `rz-bin -I` takes 0.02s and 19 MB. It reproduces, and the cause is
not the file size:

```
$ /usr/bin/time -f '%e s %M KB' e5r info fixtures/build/panicky
0.08 s 51332 KB
$ objcopy --strip-debug panicky panicky.nodebug
$ /usr/bin/time -f '%e s %M KB' e5r info panicky.nodebug
0.00 s 5376 KB
```

`panicky` is a 4.5 MB Rust binary carrying 1.8 MB of `.debug_str` and 1 MB of
`.debug_info`. `e5r info`, which prints the container header and nothing that
needs types, parses the debug information anyway, and pays 0.08 seconds and
46 MB for it. A 4.5 MB binary without DWARF, `libcrypto.so.3`, loads in 0.01s.
`rz-bin -I` does not read DWARF unless asked.

This is a defect in e5r and it is not fixed here: this task's brief is the
benchmark and its scripts, not the crates. It is the one place in this table
where the mature tool is doing the more sensible thing.

## The regression budget

The budget is [`scripts/bench-budget.json`](../scripts/bench-budget.json),
checked by [`scripts/check-bench-budget.py`](../scripts/check-bench-budget.py).
It is the same shape as the ratchets elsewhere in this repository: a ceiling
that only comes down, and a floor that only rises. It has two halves, and they
are checkable in different places.

**What the analysis found is deterministic.** Recall and the unnamed count are
the same bytes in, same numbers out, on any machine, at any thread count, on any
build profile. Those are checked everywhere, and either one differing from the
recorded value fails, in both directions: below the floor is a regression, and
above it is a floor that has stopped catching the regression that would take it
back. Moving either takes `--update` and a commit, so a reviewer sees the number
move.

**What it cost is not.** The wall time and peak memory ceilings belong to the
machine named in the file and to a release build. A shared runner on another
architecture would blow through them for reasons that have nothing to do with a
regression, so `--no-timing` drops that half, and any job that cannot reproduce
the recording machine passes it.

Each cost ceiling carries stated headroom over the measurement that set it,
recorded beside it in the file: 2x on wall time, because this machine runs other
work and a gate that fails on a busy afternoon is a gate people switch off, and
1.15x on peak memory, which barely varies. A 2x ceiling is a loose gate and is
meant to be: the number to compare against when the question is "did this change
make it slower" rather than "is it still acceptable" is `measured_seconds`,
recorded beside every ceiling. Improvements in either are reported rather than
failed, because noise moves them both ways and a ceiling that ratchets itself
down on a lucky run is a ceiling that fails on an ordinary one. Lower them with
`--update` when a change was meant to.

There is also a **speedup floor** against rizin, which is what the roadmap's
first bet asks to be regression-tested. It is capped at 10x however large the
measured ratio was. rizin takes twelve and a half minutes on `libstdc++` here, and
pinning a floor near that ratio would fail the day rizin fixes it, which is not
our regression to fail on.

Entries measured on system libraries are marked `portable: false`. This
machine's libc is not another machine's, so a runner checks only the fixtures,
which are built from sources in this repository.

```
scripts/check-bench-budget.py target/bench-tools.json                       # G8
scripts/check-bench-budget.py target/bench-tools.json --portable-only --no-timing
scripts/check-bench-budget.py target/bench-tools.json --update              # move it
```

## What CI does, and what it deliberately does not

**No benchmark runs in CI.** Wall time and peak memory are facts about a
machine. A GitHub runner is shared hardware with a neighbour you cannot see, so
a timing number measured there cannot be compared against the ceilings in
`bench-budget.json`, which were recorded on the machine at the top of this file
-- and cannot be compared against the next run on a different runner either. A
gate that fails for reasons unrelated to the commit is a gate people learn to
skip, and a published number that means nothing is worse than no number.

What does run, as the `recall` job in
[`.github/workflows/ci.yaml`](../.github/workflows/ci.yaml), is the half of the
budget that is deterministic: recall against the symbol table, and the count of
entries no symbol names. Those are the same bytes in and the same numbers out on
any machine at any thread count, so they gate on every push. It needs no tool but
this repository's own build and takes seconds. One run per binary, because the
fastest of three exists to beat down timing noise and there is no timing here.

Comparing against rizin is done by hand, on the machine named at the top of this
file, and the result is written down here. It was briefly a weekly CI job and
should not have been: it installed rizin to produce numbers that could not be
compared with the published ones, then checked a budget that had nothing to do
with rizin.

Ghidra is not installed on a runner either. It is a 400 MB download plus a JDK,
and a per-push job that spends four minutes fetching a JVM to analyze a 71 KB
fixture is a job people turn off. `scripts/compare-tools.sh` picks it up from
`GHIDRA_INSTALL_DIR` if a runner ever has one cached.

**The `recall` job has not been run.** It is written against the same scripts
that produced the numbers here, and those scripts run, but GitHub Actions cannot
be exercised from this machine. Unverified: that `build-fixtures.sh` produces
the same fixtures there, and that a release build plus a fixture build fits the
job's time budget.

## Rerunning this

```
cargo build --release
scripts/compare-tools.sh                                      # the default corpus
scripts/compare_tools.py --markdown target/bench-tools.json   # the tables above
scripts/compare_tools.py --explain  target/bench-tools.json   # the differences
scripts/check-bench-budget.py target/bench-tools.json
```

rizin comes from the distribution package; nothing needs building. Ghidra joins
the table by setting `GHIDRA_INSTALL_DIR` to an installation, and
[`compare-ghidra.sh`](../scripts/compare-ghidra.sh) compares function recovery
against it on its own.

The two largest libraries were measured once rather than three times, because a
single `rizin -A` on `libstdc++` takes twelve and a half minutes. Their rows say so.

## What this does not measure

- **Ghidra.** Not measured in this run, by decision rather than by accident. Its
  headless analyzer does run on this aarch64 host and `scripts/compare-tools.sh`
  will include it when `GHIDRA_INSTALL_DIR` is set, but its decompiler ships as
  an x86-64 binary only, so the comparison that would matter most cannot be made
  here at all. The earlier function-recovery comparison against Ghidra 12.1.3 is
  in [`scorecard.md`](scorecard.md).
- **Everything rizin does that e5r does not.** rizin is a debugger, a hex
  editor, a shell, an assembler and a scriptable session; e5r is none of those.
  The columns here cover the part of rizin that overlaps e5r, which is a small
  part of rizin.
- **Decompiler output quality**, which is [DecBench](decbench.md)'s job, and
  where e5r currently loses.
- **Anything but ELF on aarch64 and x86-64.** The corpus is what this machine
  can build and run.
- **A cold page cache.** Every run here is warm, which flatters whichever tool
  reads less of the file, and that is e5r, which memory-maps the image.
