# DecBench

[DecBench](https://decbench.com) is a third-party decompiler benchmark. It
compiles real projects from source with DWARF retained, strips the binaries,
hands each decompiler the stripped copy, and scores the C that comes back
against the original source on three axes. We did not choose the corpus, the
metrics or the thresholds, which is the point: `docs/scorecard.md` is us
grading our own work, and this is not.

This document records what was measured, how to reproduce it, and the numbers,
including the ones that go against us. The short version: on the one project
that could be run here, **r12e scores 23.4 union against angr's 37.0 on the
same binaries**: behind on structure, behind on types, level on
recompilation. It decompiles more of the corpus than angr does and thirteen
times faster, and neither of those is a DecBench metric.

Measured on 2026-09-13 against DecBench at commit `5818d67`. Every number
below was re-derived on the same day from the cached decompilations by a
second run of the driver; the scoreboard it produced is identical to the
first.

## The plugin interface

A decompiler joins DecBench by one of three routes (its `docs/decompilers.md`):
a plugin backend it runs itself, an LLM-agent backend, or an external
submission where the author scores a 250-function eval kit and mails back a
zip. We take the first route.

A backend is one class:

```python
@register_decompiler("r12e")
class R12eDecompiler(Decompiler):
    def is_available(self) -> bool: ...
    def get_version(self) -> str | None: ...
    def decompile_binary(self, binary_path, functions=None, output_dir=None,
                         function_names=None, progress_path=None
                         ) -> DecompilationResult: ...
```

`decompile_binary` returns one `FunctionDecompilation` per function, each
carrying at minimum the C text and the function's address **in ELF file
space**, which is what makes an address line up with the DWARF the metrics read
for ground truth. `function_names`, despite the name, is the set of DWARF
`low_pc` addresses the driver wants: it hands the backend a stripped binary, so
functions have no names at that point, and the driver relabels the results to
their DWARF names afterwards for evaluation. `progress_path` is a checkpoint
sink for backends slow enough to be killed on a timeout. Everything else is
optional: variable lists with ABI argument positions and line maps improve
fidelity, but a backend that fills in only code and address is still scored on
all three metrics, with type_match parsing types out of the C.

Ours is `scripts/decbench_r12e.py`. It shells out to `r12e decompile <binary>
all --json` once per binary and splits the JSON document into functions, which
is far cheaper than one call per function: every invocation re-analyzes the
whole image, so `all` pays the analysis once (5s for 158 functions of zlib's
`example`) instead of per function. It lives in this repository rather than in
the DecBench tree, so **the DecBench checkout is untouched**; DecBench's own
contract allows this ("out-of-tree plugins just need to be imported by your own
entry point"), and `scripts/decbench_run.py` imports it before consulting the
registry.

## What it needs, and what this machine has

| Requirement | State here |
| --- | --- |
| Python >= 3.10 with the `decbench` package | 3.12, installed in a venv from a copy of the checkout |
| angr, pyjoern, cfgutils, pyelftools, lief, scipy | pip, all resolved |
| Joern (the source and decompiled CFG parser) | 1.8 GB, downloaded by pyjoern on first use |
| A JDK for Joern | OpenJDK 21 |
| gcc for the corpus and for the recompile metric | gcc 13.3, aarch64 |
| Ghidra, IDA, Binary Ninja for their columns | see below |

Nothing was missing that could not be installed. Two notes on what is *not*
available, because they bound the comparison:

- **Ghidra's decompiler does not run on this machine.** The install here is
  12.1.3 and DecBench's backend reports it as available, but every function
  fails with "Could not find decompiler executable": Ghidra ships the native
  decompiler only as `os/linux_x86_64/decompile` and `os/win_x86_64`, and this
  host is aarch64. Building it from source is the only way to get a Ghidra
  column here.
- **IDA and Binary Ninja are not installed** and are commercial, so there is no
  Hex-Rays or Binja column either.

That leaves **angr** as the only other decompiler that can be run here, which
makes it the only honest like-for-like comparison in the table below.

## What was measured

- **Corpus:** `zlib` 1.2.13, from DecBench's `projects/sailr/zlib.toml`, built
  by DecBench's own compile pipeline: `gcc -g -fno-builtin -save-temps=obj -O0`.
  Seven ELF binaries (`example`, `example64`, `examplesh`, `libz.so.1.2.13`,
  `minigzip`, `minigzip64`, `minigzipsh`).
- **Functions:** 780 function slots, the DWARF `low_pc` set of the functions
  zlib's own translation units define, per binary. The same library functions
  appear in several binaries, which is how DecBench counts. 779 are scored:
  two addresses in `libz.so` carry the same DWARF name, and relabeling merges
  them.
- **Optimization level:** O0 only, which is DecBench's `unoptimized` dataset.
- **Architecture: aarch64.** This is the headline caveat. The published
  leaderboard is x86-64, because DecBench's machine is; the sailr TOMLs name
  plain `gcc`, so the corpus is built for whatever the host is, and this host is
  ARM. DecBench records the architecture per binary for exactly this reason.
  **Our number is not comparable to a published number**, and the table below
  keeps them apart.
- **What the decompiler saw:** a `strip --strip-all` copy. No symbols, no DWARF.
- **Versions:** r12e 0.1.0 at `523515a`, angr 9.3.4, DecBench `5818d67`,
  metrics as that commit defines them (`cache_version` ged 4, byte_match 7,
  type_match 6).

## Results

Percent of functions scored perfect on each metric, which is what DecBench
ranks on. Higher is better. Both columns are the same seven binaries and the
same 780 function slots on the same machine, 779 of them after the duplicate
DWARF name merges. The denominators differ, because
DecBench scores each decompiler over the functions it returned: 779 for r12e,
759 for angr, which returned nothing for twenty of them. Crediting angr with a
zero on those twenty instead of dropping them gives it 36.1 union rather than
37.0, so the choice does not change the ordering.

| | Union | Structure (GED) | Types | Recompile |
| --- | --- | --- | --- | --- |
| angr 9.3.4 | **37.0** | **34.6** | **10.2** | **0.66** |
| r12e 0.1.0 | 23.4 | 22.9 | 5.6 | 0.64 |

The per-metric distributions, because a perfect-count alone hides how far off
the rest are. GED is a distance, so lower is better; the other two are
similarities, where 1.0 is perfect.

| | GED mean | GED median | Types mean | Recompile mean | Functions that recompiled |
| --- | --- | --- | --- | --- | --- |
| angr | 9.2 | 3 | 0.50 | 0.175 | 88.5% |
| r12e | 21.1 | 13 | 0.10 | 0.181 | 96.1% |

So: **r12e is beaten on structure and on types, and is level on
recompilation.** Union is 23.4 against angr's 37.0, a third behind. The
recompile column is the one the roadmap bet on being open, and it is: r12e's
mean assembly similarity is marginally the higher of the two and it compiles
after fixup more often, while both land five perfect functions out of ~780.

**Do not read the recompile column as correctness.** byte_match recompiles the
function and compares the two assemblies by Jaccard similarity with
linker-dependent operands normalized away, which measures shape. A function
that drops every argument at every call, as defect 3 below says ours do,
still produces call instructions in roughly the right places and still scores.
This repository's own `cargo test --release -p r12e-decomp --test roundtrip`
gate compiles each pure decompiled function and runs it against the
interpreter, and at the time of this run it reported over a thousand calls
disagreeing with the machine across dozens of functions. Those two statements
are consistent: 0.181 mean byte_match and semantically wrong output are the
same output. The field-wide recompile floor, nobody above 3.0, is a statement
about the metric's strictness on perfect matches and not a licence to read the
mean as a correctness score.

Two things that DecBench does not score, and which are ours:

| | Functions returned | Wall time for all seven binaries |
| --- | --- | --- |
| r12e | 780 / 780 | 21s |
| angr | 760 / 780 | 278s |

### Against what the roadmap asked for

`ROADMAP.md` sets M6's exit criterion as beating Ghidra's published unoptimized
score, 32.2 union and 29.3 structure, and G12 as holding union and recompile at
or above the last release per dataset. **M6's bar is not met.** 23.4 union and
22.9 structure are short of it even before allowing that Ghidra's 32.2 was
measured on a corpus this slice is harder than: angr drops from 45.7 published
to 37.0 here, and applying that same 0.81 ratio to Ghidra would put it near 26
on this slice, still ahead of us. That scaling is an inference, not a
measurement, and the only way to settle it is to run Ghidra, which this machine
cannot. This run is the first G12 baseline; there is no previous release to
compare against.

### Against the published leaderboard

DecBench's published numbers are **x86-64**, on the whole 34,406-function
unoptimized set. Ours are **aarch64**, on 779 functions of one project. These
are different measurements and the table keeps them apart; the angr row appears
twice on purpose, as the only thing that bridges them.

| | Corpus | Union | Structure | Types | Recompile |
| --- | --- | --- | --- | --- | --- |
| Hex-Rays (IDA 9.2) | published, x86-64, 34,406 fns | 47.9 | 45.7 | 8.7 | 0.8 |
| kuna 1.121 | published, x86-64 | 46.8 | 44.8 | 8.1 | 3.0 |
| angr 9.2.223 | published, x86-64 | 45.7 | 41.2 | 12.1 | 0.6 |
| Ghidra 12.1 | published, x86-64 | 32.2 | 29.3 | 7.7 | 0.2 |
| Binary Ninja 5.3 | published, x86-64 | 28.9 | 24.0 | 10.4 | 0.2 |
| r2dec (r2-6.0.8) | published, x86-64 | 22.1 | 21.5 | 2.3 | 0.1 |
| dewolf v2026.7.11 | published, x86-64 | 4.4 | 4.5 | 0.1 | 0.0 |
| --- | --- | --- | --- | --- | --- |
| **angr 9.3.4** | **ours, aarch64, zlib O0, 779 fns** | **37.0** | **34.6** | **10.2** | **0.66** |
| **r12e 0.1.0** | **ours, aarch64, zlib O0, 779 fns** | **23.4** | **22.9** | **5.6** | **0.64** |

angr scores 37.0 on our slice against 45.7 on the published corpus, so this
slice is the harder of the two for reasons that have nothing to do with r12e.
r12e reaches 63% of angr's union on the binaries where both were run. That
ratio is the honest statement. It is not a projected leaderboard position, and
nobody should read one into it: the only way to get a comparable number is to
run the published corpus on x86-64, which needs a cross toolchain this machine
does not have, or to submit to the 250-function sample set.

Six of the thirteen published entrants are left out of the table: DecBench
marks Codex, Claude Code, Fission, Glaurung, Manifold and Ventris
`sample_set_only`, meaning they attempted only the sample set. Their full-set
rows are a scale artifact, not a score. Codex and Claude Code lead the sample
set and score 0.2 on the full one; recomputing from the checkout's
`site/data/samples.json` over the 243 functions each attempted gives 56.8 and
56.2 union, against 38.6 for Hex-Rays over the 500 it attempted. Quoting either
number without the other misleads.

### The three defects that cost the most

**1. Structuring, which is most of the gap on its own.** r12e
emits 1,545 gotos across the 780 functions, 1.98 per function, against angr's
433 and 0.57. Splitting our own functions by their goto count says the rest of
the decompiler is not the problem:

| r12e functions | count | GED-perfect | mean GED |
| --- | --- | --- | --- |
| no goto | 475 | 36.2% | 10.6 |
| 1-2 gotos | 175 | 2.9% | 18.4 |
| 3 or more gotos | 124 | 0.0% | 65.1 |

A function r12e structures without a goto scores 36.2% perfect, which is
*better* than angr's 34.6% over its whole set. Every function that needs one is
a near-certain zero. At that rate across all 774 scored functions the GED
column would read about 36 instead of 22.9, which is thirteen points and most
of the distance to angr. The goto ceiling in `docs/scorecard.md` is measured on
the fixture corpus, where it reads 0.00 to 0.24 per function; on real code at
O0 it is 1.98. The fixture corpus is not representative and the scorecard
number is optimistic.

**2. Locals reach the metric with no name, no offset and no type.** type_match
scores parameters and locals together, and 444 of libz's 768 ground-truth
variables (58%) are locals. DecBench matches locals by stack offset when the
backend supplies `VariableInfo`, and by name otherwise. `r12e decompile
--json` emits only a *count* of locals, so the adapter can supply neither, and
every local is a guaranteed miss: 596 of r12e's 764 scored functions score
exactly 0. Parameters are not much better: across libz's 151 functions r12e
emits 410 of them, 308 as a bare `uint64_t`, against angr's spread of
`unsigned int`, `long long` and pointer types over 317. They are still where
the 43 perfect functions come from. Exposing
per-variable name, type and stack offset in the JSON is the single cheapest
point of score on this list.

**3. Calls through the PLT lose their arguments and their return value.** 295
of the 780 functions contain at least one `name_plt()` call emitted with an
empty argument list; libz alone has 194 such call sites, and **30 of the 47
distinct callees are functions r12e decompiled with a full signature in the
same run**, reached through a PLT stub only because the library is built PIC. The result is then read from `__clobbered()`, so the value the call
produced is severed from everything downstream. In `all` mode, which is the mode the
benchmark runs because it is the only affordable one, the assignment
disappears entirely and the output reads a variable that is never assigned;
asking for the same function by name instead emits `v0 = sub_5f0();`. Two
modes, two different bodies for one function, one of them undefined. Compare,
on `compress2`:

```c
/* r12e */   deflateInit__plt();
             v13 = (uint32_t)v0;          /* v0 is never assigned */

/* angr */   i = deflateInit_(&v4, a4, "1.2.13", 112, &v4);
```

Reproduce it in three lines:

```bash
printf '#include <string.h>\nint f(const char*s){return strlen(s)>3;}\n%s\n' \
  'int main(int c,char**v){return f(v[0]);}' > /tmp/p.c
gcc -g -O0 -fno-builtin /tmp/p.c -o /tmp/p
./target/release/r12e decompile /tmp/p f     # v0 = (uint64_t)(sub_5f0());
./target/release/r12e decompile /tmp/p all   # strlen_plt();  and v0 never assigned
```

The argument is gone in both. The assignment is gone only in `all`, which is
the mode the benchmark runs.

This one does not show up as a GED loss, because a call is a call whatever its
arguments, but it is the reason a recompiled r12e function computes the wrong
thing, and it is a `docs/design/decompiling.md` violation: the design says the
decompiler does not silently drop anything, and this drops every argument at
the call.

### The working tree has already moved

Checked the same day, after the run: the binary at `0edd06e` decompiles the
same 158 functions of `example` into 133 identical bodies and 25 changed ones,
and the goto count over that fixed set rises from 289 to 407. Structuring is
the metric this document says costs us the most, and it has got worse by 41%
on this corpus since the measured commit. That tree has several agents mid-edit
in it and is not a release, so this is a warning rather than a number: whoever
re-runs this benchmark should expect the GED column to move, and should check
which direction before quoting it.

### What this run does not say

- **One project.** zlib at O0 is 779 of DecBench's 94,575 functions. A single
  project's score is not a leaderboard position.
- **O0 only.** DecBench's `optimized` (O2 with inlining disabled), `inlined`
  (plain O2) and `large` sets are where the whole field falls over, nobody
  clearing 2% union on `large`, and r12e has not been near them.
- **aarch64 only**, for the reason above.
- **No Ghidra, IDA or Binary Ninja column**, for the reasons above. The only
  peer measured here is angr.
- **The published numbers are a 2026-08-29 snapshot** read out of the DecBench
  checkout's `site/data/aggregates.json`, not a fresh run of those tools.

## How to reproduce from a clean checkout

```bash
# 1. A copy of the checkout to install from. `pip install -e` writes an
#    egg-info into the source tree, so installing from ~/Ref/decbench directly
#    would modify it. This is what the measured run did.
cp -a ~/Ref/decbench /tmp/decbench-work

# 2. A virtualenv with DecBench in it.
python3 -m venv /tmp/decbench-venv
/tmp/decbench-venv/bin/pip install -e /tmp/decbench-work

# 3. Build r12e.
cargo build --release

# 4. One command. It compiles the corpus project on the first run (network:
#    the project TOMLs name upstream tarballs and git remotes), then
#    decompiles and evaluates.
DECBENCH_REPO=/tmp/decbench-work DECBENCH_VENV=/tmp/decbench-venv \
  scripts/decbench.sh /tmp/decbench-r12e zlib O0 r12e,angr
```

The first run also downloads Joern (1.8 GB) the first time a metric needs a
CFG. Budget an hour for a single project at one optimization level on this
machine: the decompiling is minutes, the Joern parsing and the graph edit
distances are the rest. Results are cached in the tree, so re-running only
redoes the evaluation; `DECBENCH_REDO=r12e` forces the decompiling again after
a rebuild. Joern plants a `workspace/` directory of CPG stores next to
wherever it runs, so the driver chdirs into the results tree first, to keep it
out of this repository.

`scripts/decbench_run.py` is the driver. DecBench's own
`scripts/run_benchmark.py` was not used, because it decompiles through its own
`decompile_one.py` subprocess, which imports only the in-tree backends: an
out-of-tree column is invisible to it unless the DecBench tree is edited or a
`.pth` is smuggled into the virtualenv, and neither is a thing to do to
somebody else's benchmark. It also drives the whole corpus, which is not what
is wanted here. The driver is the same pipeline at one project's
scale (strip, decompile by DWARF address, relabel to DWARF names, evaluate,
aggregate), calling DecBench's library at every step, so the numbers come from
its code and not from a reimplementation of its metrics.

## What it would take to be scored by DecBench itself

Three things, in the order they are worth doing:

1. Fix the defects above, structuring first: it is the largest single loss and
   the evidence says the rest of the decompiler is already competitive on the
   functions it structures cleanly.
2. Submit to the 250-function sample set, which needs no harness at all:
   download the eval kit, decompile the listed functions, mail back the zip.
3. Upstream the backend. Ours is deliberately out-of-tree; moving it to
   `decbench/decompilers/raw/r12e_raw.py` is a rename and an import, plus
   filling in `VariableInfo` with ABI argument positions so type_match scores
   the recovered types rather than parsing them back out of the C.

Steps 2 and 3 both send something to DecBench, and its `AGENTS.md` refuses
end-to-end autonomous contributions: a person has to read, own and send the
submission or the pull request. Nothing in this document has been sent
anywhere.

## The corpus as fixtures, separately from the score

Everything above is DecBench grading our decompiler. The corpus itself is
worth having for a second reason, which `ROADMAP.md` states as an M12 task:
39 projects built at several optimization levels **with DWARF retained** is
function-boundary ground truth that already exists, and it feeds the G4 gate
as much as it feeds the decompiler work.

`scripts/decbench-fixtures.sh` makes that corpus available without copying it
into the checkout, and without any of the machinery `scripts/decbench.sh`
needs. It reads each project's recipe out of the DecBench TOML and drives gcc
itself: no virtualenv, no `decbench` package, no angr, no Joern, no JDK. The
DecBench checkout stays read-only, which is the same rule the backend follows.

```bash
scripts/decbench-fixtures.sh --list          # the recipes the checkout has
scripts/decbench-fixtures.sh zlib bzip2      # named projects
scripts/decbench-fixtures.sh --all           # everything that builds here
```

Where things go: the sources, the object trees and the binaries live in
`~/.cache/r12e/decbench` (`DECBENCH_FIXTURES` moves it). The only thing that
lands under `fixtures/` is `fixtures/build/decbench/manifest.tsv`, a text file
listing, per binary, the unstripped image, a stripped copy and a TSV of DWARF
function bounds read by `readelf`. `fixtures/build/` is gitignored, so nothing
is added to the repository.

The manifest is rebuilt from the cache on every run rather than from that run,
so asking for one more project adds to the corpus instead of replacing it, and
deleting a cache directory removes it by itself.

Recipes that need an autotools bootstrap, a sysroot or a missing dependency are
reported and skipped; each failure names its build log under
`~/.cache/r12e/decbench/log/`. The corpus is whatever actually builds here.

What consumes it is `scripts/boundary-gate.sh`, which is G4:
[`docs/boundaries.md`](boundaries.md) has the method and the numbers. The
decompiler score in this document and that boundary score are independent: one
is DecBench's metrics on our C output, the other is DWARF read by `readelf`
against our function list, and neither borrows the other's corpus preparation.
