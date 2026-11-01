# PTX kernel verification in Lean 4

This is scope P of the roadmap (owner authorization, 2026-10-31). The proof
subject is a `.ptx` file, the NVIDIA virtual ISA a model writes directly or a
compiler emits. Lean 4 checks three properties of it against a specification
written in Lean:

- memory safety;
- data-race freedom;
- functional correctness.

No CUDA C++, Triton or Rust source, no reference kernel and no equivalence
check is part of a proof. The input is PTX and a specification. The output is
a theorem the Lean kernel has checked, or a counterexample the Lean kernel has
replayed, or a verdict that says neither was obtained.

The question this scope is built to answer:

> Can we automatically prove memory safety, race freedom, and functional
> correctness of LLM-generated NVIDIA PTX kernels directly in Lean 4, without
> trusting the LLM or a high-level compiler?

For one class of kernels, elementwise maps over 32-bit arrays (`map32`,
below), the measured answer is yes: 102 of the 104 kernels the agent wrote to
be correct were proved by the same tactics with no per-kernel proof, the
other 2 use instructions outside the subset and are reported as unsupported,
and every seeded defect inside the subset was refuted with a counterexample
the Lean kernel replayed (`verification/ptx/m5/RESULTS.md`). Kernels with
shared memory, barriers or atomics (M4) are not covered.

"Proved" below means checked by the Lean kernel with only `propext`,
`Quot.sound` and `Classical.choice` among the axioms of every declaration
of the library (the audit, below). There is no `sorry`, no `native_decide`
and no `bv_decide`. The last two check their certificates by native
evaluation, which would put the compiler in the trusted base.

## Status

| Milestone | State | Evidence |
| --- | --- | --- |
| M1 semantics, sequential proofs (P1) | done | `sum_correct` |
| M2 SIMT, race freedom (P2) | done | `grid_sound`, `vadd_correct`, `saxpy_correct`, three refutations |
| M3 proof automation (P3) | done for `map32` | `e5r-verify ptx check`; 102 kernels proved, 20 of 21 mutants refuted |
| M4 shared memory, barriers, reduction (P4) | open | not started; see "Open" |
| M5 AI-written PTX benchmark (P5) | done, with the limits stated | `m5/RESULTS.md`; differential test against the A10G |

## Reproduce

```sh
./scripts/recheck-ptx.sh       # everything below, about 8 min on the development machine
```

It runs, in order, and fails on the first problem:

1. the parser tests, release profile: round trip, the ptxas agreement test
   (506 forms), grammar and mutation fuzzing, the CLI tests;
2. `scripts/check-lean-ptx.sh`: regenerate every kernel module from its `.ptx`
   and refuse a stale one, assemble every benchmark with ptxas when it is
   installed, build the Lean project from scratch, and run the axiom audit;
3. `e5r-verify ptx check` on every benchmark against
   `benchmarks/expected.txt` (2 proved, 3 refuted, 1 unsupported);
4. the mutation controls (`mutants/run.py`): no mutant may be proved;
5. the GPU differential test (`scripts/check-ptx-difftest.sh`), skipped with
   a note when there is no GPU.

The M5 benchmark is separate because it needs the GPU and takes 12 minutes:

```sh
python3.12 verification/ptx/m5/run.py ./target/release/e5r-verify /tmp/m5
python3 verification/ptx/m5/report.py /tmp/m5/results.json
```

Lean is core v4.35.0, the toolchain `verification/rv32` already uses. The
project has no `require`, so nothing is downloaded. Mathlib is not used.

Lean is capped on purpose: a Lean process was OOM-killed at 15 GB on the
development machine. The scripts run Lean with `LEAN_NUM_THREADS=2` under a
10 GB cgroup limit (`systemd-run`, no swap; override with `PTX_LEAN_MEMORY`).
`e5r-verify ptx check` runs one Lean thread under a 6 GB cap and a 600 s
timeout (`--memory-mb`, `--timeout`). Without systemd only the thread count
and the timeout apply.

## Command line

```
e5r-verify ptx export [--namespace NS] [--name NAME] FILE.ptx
e5r-verify ptx check FILE.ptx --spec SPEC.json [--project DIR] [--out RESULT.json]
                     [--keep DIR] [--timeout SECS] [--memory-mb MB] [--no-search]
e5r-verify ptx run --cases CASES FILE.ptx
```

`export` prints the Lean `Ptx.Module` of a file after the token round trip.
`run` executes differential-test cases on the concrete interpreter.

`check` is the verifier. It parses the PTX (refusing anything outside the
subset), reads the spec, generates a Lean file that states
`E5rCheck.correct : spec.Correct K` and proves it with the class tactics,
runs Lean on it under the caps, and audits the theorem's axioms. If that
does not produce a proof it searches for a counterexample with the concrete
interpreter and, if it finds one, generates `E5rCheck.refuted : ¬ spec.Correct K`
and runs Lean on that. `--keep DIR` keeps both Lean files.

Exit status and verdict, fail-closed (only `proved` exits 0):

| exit | verdict | meaning |
| --- | --- | --- |
| 0 | `proved` | Lean checked `spec.Correct K`, axioms within the three above |
| 1 | `refuted` | Lean checked `¬ spec.Correct K` from a concrete counterexample |
| 2 | `unsupported` | the PTX is outside the subset, or the spec or kernel outside the class |
| 3 | `unknown` | neither: the proof did not check and no counterexample was replayed, or a cap was hit |
| 4 | `error` | malformed spec, unreadable file, missing kernel, Lean library does not build |
| 64 | | the command line could not be understood |

The result is a JSON document with `"schema": "e5r.ptx.result.v1"`:
`verdict`; `properties` (`memory_safety`, `termination`, `race_freedom`,
`functional_correctness`, each `proved`, `refuted`, `unknown` or
`unsupported`); `theorem` (name, statement, axioms) for a proof;
`counterexample` (kind `fault`, `race`, `wrong_value` or `frame`, the launch,
bases, scalars, threads and steps, `replayed_in_lean`, the refutation
theorem); `input` with the SHA-256 of both files; `lean_spec` and `lean_loop`,
the Lean definitions the theorem is about; `reasons`; timings. A refuted
verdict marks only the violated property `refuted`; the others stay
`unknown`.

### The spec (`e5r.ptx.spec.v1`, class `map32`)

```json
{ "schema": "e5r.ptx.spec.v1", "kernel": "saxpy", "class": "map32",
  "arrays": ["saxpy_x", "saxpy_y"], "output": "saxpy_y", "length": "saxpy_n",
  "scalars": ["saxpy_a"], "element": "saxpy_a * saxpy_x + saxpy_y",
  "schedule": { "kind": "stride", "bound": "2^64",
    "loop": { "head": "$L_loop",
      "registers": { "%rd1": "base saxpy_x", "%rd2": "base saxpy_y",
                     "%r1": "scalar saxpy_a", "%rd3": "index64",
                     "%rd5": "stride64", "%rd6": "length" } } } }
```

- `arrays` are `.u64` parameters pointing at arrays of `n` 32-bit elements;
  `output` is one of them; `length` and `scalars` are `.u32` parameters. Every
  kernel parameter must be named.
- `element` is the value output element `i` must end with, over the elements
  `i` of the arrays (initial memory) and the scalars: `+ - * & | ^ ~`, shifts
  by a literal below 32, literals, parentheses, all modulo 2^32.
- `schedule` is `guarded` (thread `gid = ctaid.x·ntid.x + tid.x` handles
  element `gid`; `max_threads` is the largest `G·B` the spec claims, and
  `n ≤ G·B` is required) or `stride` (a grid-stride loop; `bound` is the largest
  `n + G·B` claimed; `loop` is the invariant: the label of the loop head and
  what each live register holds there, as `index64|index32`, `stride64|stride32`,
  `length`, `base A`, `ptr A` (address of element `i` of `A`), `ptr_stride`,
  `scalar S` or `const N`).

The claimed ranges are part of what is checked. The vadd that nvcc emits
compares a signed 32-bit index, so its spec claims `max_threads` 2^31 − 1;
claiming 2^32 − 1 is refuted with a thread whose index wraps negative
(`mutants/run.py`).

## What is proved

### The class theorem (M3)

`Ptx.Auto.MapSpec.Correct K` (`Ptx/Auto/Map.lean`) is the statement every
`check` proves. For every 1-D launch of `G` CTAs of `B` threads and every
argument tuple that meets `Pre`:

- every array fits in the address space and is 4-byte aligned;
- the output overlaps no other array (inputs may alias each other);
- the launch is in the schedule's claimed range;

and for every initial memory, every initial register content and every
interleaving of the launch's threads at instruction granularity:

- `∀ c, Reach c₀ c → ¬ Faults c`;
- `∀ c, Reach c₀ c → Done c ∨ ∃ c', Step c c'`, and a bound on the length of
  every execution;
- `RaceFree`;
- `∃ c, Reach c₀ c ∧ Done c`;
- when all threads are done and the launch has a thread: every output
  element `i < n` equals `f` of the initial elements `i`, and every byte
  outside the output elements is unchanged.

It is proved generically: `correct_of_threadOk` derives it from one
obligation per thread through `grid_sound`; `threadOk_of_guardedOk` and
`threadOk_of_stride` reduce that to local obligations (one element, or one
loop iteration with the generic memory invariant). The tactics in
`Ptx/Auto/Tactic.lean` discharge the local obligations for a concrete kernel:
`simp` runs the instruction table symbolically, `ptx_addrs` rewrites every
address to `elem base i` by reducing both sides to natural numbers modulo
2^64 and deciding them with `omega`, `ptx_branches` turns branch conditions
into linear facts, and `grind` closes the value equation (ring laws on
`BitVec 32`). The tactics are not trusted: they build a proof term the kernel
checks, and when they fail the verdict is `unknown`.

### Theorems in the library

All of these quantify over every initial register content and every
interleaving.

| Theorem | Kernel | Preconditions | Spec |
| --- | --- | --- | --- |
| `Ptx.Examples.Sum.sum_correct` (M1) | `benchmarks/correct/sum.ptx`, one thread, counted loop | `a` fits, `a`, `out` 4-aligned; `out` may alias `a` | `out[0] = a[0] + … + a[n-1] mod 2^32` for every `.u32` `n` |
| `Ptx.Examples.VectorAdd.vadd_correct` (M2) | `benchmarks/correct/vadd_nvcc.ptx`, nvcc 13.2 | `G·B ≤ 2^31`, `n ≤ G·B`, `n < 2^31`; arrays fit, aligned; `c` overlaps neither input | `c[i] = a[i] + b[i] mod 2^32` for `i < n` |
| `Ptx.Examples.Map.saxpy_correct` (M2) | `benchmarks/correct/saxpy.ptx`, grid-stride | any `G`, `B`, `n`; `x`, `y` fit, aligned, disjoint | `y[i] = a·x[i] + y[i] mod 2^32` |
| `Ptx.grid_sound` | every kernel | per-thread `Solo` runs, disjoint write footprints | the five clauses above |
| `Ptx.Auto.correct_of_threadOk`, `threadOk_of_guardedOk`, `threadOk_of_stride` | every `map32` kernel | the local obligations | `MapSpec.Correct` |
| `E5rCheck.correct` (generated) | each kernel `check` proves | `MapSpec.Pre` | `MapSpec.Correct` |

The vadd preconditions are the ones the PTX needs:

- `G·B ≤ 2^31`. `mad.lo.s32` computes the index in 32 bits and `setp.ge.s32`
  compares it as signed. With more threads the index wraps negative, passes
  the `i < n` check, and `mul.wide.s32` turns it into an address below `a`.
- `n < 2^31`. `n` is an `int`. The `.u32` parameter `2^31` is negative, so the
  kernel writes nothing.
- `n ≤ G·B`. There is no grid-stride loop, so a smaller launch leaves the tail
  of `c` unwritten.

### Refutations

A refutation is the theorem `¬ spec.Correct K`, proved by instantiating the
universal statement at a concrete launch, memory and register file, showing
`Pre` holds there, and exhibiting a reachable configuration (one thread run
alone, or all threads one after another, which are interleavings) that
faults, two reachable configurations whose pending accesses conflict, or a
finished configuration with a wrong element or a changed byte. The
counterexample search is untrusted; only the replayed theorem is reported.

| Kernel | Change | Theorem | Counterexample |
| --- | --- | --- | --- |
| `vadd_nobound.ptx` | `i < n` check removed | `nobound_faults`, and `check` | thread 1 of 2, `n = 1`, faults loading `b[1]` |
| `vadd_tid.ptx` | index is `%tid.x` only | `tid_races`, and `check` | two CTAs of one thread both store `c[0]` |
| `vadd_sub.ptx` | `sub` for `add` | `sub_wrong`, and `check` | one thread, `c[0]` wrong |

## Negative and mutation controls

`mutants/run.py` mutates the two proved benchmarks one change at a time,
in the PTX (13 for vadd, 8 for saxpy: bound test, index, element size,
offset, operation, operands, stored value, removed store, loop bound,
stride, an extra store to an input, a loop that never advances) or in the
spec (wrong element function, a launch range the kernel does not support).
Each changes behaviour inside the spec's range. Measured: 0 of 21 proved, 20
refuted with a replayed counterexample (8 faults, 3 races, 8 wrong values,
1 changed byte), 1 `unknown`: the loop that never advances. Non-termination
has no finite witness, so the checker cannot refute it; it does not prove it
either.

The axiom audit was checked the same way: a module with an `axiom` and a
`native_decide` added to the library makes `Audit.lean` fail, naming both.
The ptxas agreement test was checked by letting the parser accept `and.u32`;
it failed and listed the forms.

## Differential testing against the GPU

`scripts/check-ptx-difftest.sh` runs 829 launches of 419 generated kernels,
one per instruction form of the subset (every operation at every type the
parser accepts, register and immediate operands including edge values,
shifts by 0 to 100 and by 2^32 − 1, every comparison, every conversion,
loads and stores at every type and at positive and negative offsets,
`ld.param`, guards, branches, a loop, and all special registers on 3-D
launches), on 64 to 128 threads each with edge-value and pseudo-random
inputs (fixed seed). The same launches run:

- on the A10G from the PTX text (driver JIT);
- on the A10G from a ptxas cubin;
- in Lean, executing the definitions of `Ptx.Semantics` (`lake exe ptxdiff`);
- on the concrete interpreter of `e5r-ptx` (`ptx run`).

Measured on the A10G, driver 595.112.07, CUDA 13.2: all four outputs are
identical byte for byte on all 829 launches. Five misaligned accesses (loads
and stores of 4 and 8 bytes) fault in the model and are refused by the GPU
with `CUDA_ERROR_MISALIGNED_ADDRESS`. Out-of-bounds accesses are not
compared: the GPU reports only those outside its allocation granularity.

This supplements the review of the semantics; it does not replace it. It
tests single instructions and short sequences on one GPU, driver and
compiler, at the inputs drawn.

## The M5 benchmark

`verification/ptx/m5/` is specification to PTX to Lean to GPU. Each task in
`tasks.json` is a sentence, a spec and a kernel the agent (Claude, an LLM)
wrote in this session from the sentence. `run.py` assembles each with
ptxas, runs `check`, tests the kernel on the A10G against the spec on random
inputs at several lengths and launch shapes (every other array must be
unchanged), and times it against a CUDA C baseline with the same schedule
compiled by nvcc -O3. Results (`m5/RESULTS.md`):

| | kernels | proved | refuted | unknown | unsupported |
| --- | --- | --- | --- | --- | --- |
| written to be correct | 104 | 102 | 0 | 0 | 2 |
| written with a seeded defect | 11 | 0 | 9 | 0 | 2 |

- Proof time: median 3.5 s, maximum 8.8 s per kernel, one Lean thread.
- Speed: baseline time / PTX time median 1.00 (0.95 to 1.05) over the 102
  proved kernels, at 2^24 elements.
- All 102 proved kernels agree with their spec on the GPU. Of the 9 refuted
  ones, 2 pass the GPU test (an off-by-one read past the end of an array,
  and a 32-bit index that wraps above 2^32): the proof finds what the test
  does not.

What these numbers do not show:

- The corpus is small and from one model in one session. No model API was
  available on the development machine, so there is no automated generation
  loop; batch 4 shares one skeleton expanded from a table.
- The tactics were improved while the corpus was written. `RESULTS.md` lists
  the first-run verdict of each batch: 6 of 10, 1 of 2, 33 of 34, 28 of 31,
  20 of 23 and 16 of 16 proved before the fixes each batch prompted.
- No natural defect was found: the kernels written to be correct were
  correct. The refuted kernels are seeded.
- The class is narrow, and the baseline is equally simple CUDA C, so speed
  parity says only that verifying PTX costs nothing at run time for these
  kernels. Hopper and Blackwell features are not exercised (A10G only).

## How it works

```
.ptx --e5r-ptx--> AST --token round trip--> Lean Ptx.Module
spec.json --e5r-verify ptx check--> Proof.lean (template) --lake env lean--> axiom audit --> verdict
                                 \-> interpreter search --> Refute.lean --lake env lean--> verdict

Ptx/Semantics: Memory, Instruction (one thread), SIMT (grid, interleaving)
Ptx/Logic:     Hoare (Safe, wp, loop rule), RaceFreedom (grid_sound), Regions, Launch1D, Refute
Ptx/Auto:      Map (the map32 class, proved once), Tactic (ptx_guarded, ptx_stride_*)
Ptx/Tactics:   the ptx_eval simp set
Ptx/Examples:  the M1/M2 hand proofs and refutations
Diff/Main:     the model side of the GPU differential test
```

### Generic layer (proved once)

`action K c s` is the next thing thread state `s` does: an internal step, a
`load` with a continuation that takes the bytes read, a `store`, `done` or
`fault`. Memory is never read inside the instruction table. Every interaction
with global memory is a visible action with its address and size, so
locality holds by construction.

Memory is a total map from 64-bit addresses to bytes, read and written
little-endian. An access is legal when it is naturally aligned and lies inside
one allocation of the launch. Anything else is a fault.

Registers are 64 bits wide in the model. A 32-bit operation reads the low 32
bits and writes its result zero-extended, which is exactly `.b32` for a
well-typed kernel; the parser enforces the typing. Arithmetic wraps. Shift
amounts above the width are clamped to the width, as the ISA says.

`Step` runs one instruction of any thread that can step, so `Reach` covers
every interleaving. No lockstep or fairness is assumed.

A per-thread proof is a `Safe` derivation: the thread alone reaches its
postcondition with every access legal, loads in `R t ∪ W t`, stores in `W t`.
`wp_sound` turns the weakest precondition up to the next cut point into a
`Safe` derivation; `Safe.loop` is the loop rule; `Safe.solo` turns a
derivation that ends at `ret` into the trace `grid_sound` consumes.
`grid_sound` takes those for every thread and the condition that no thread
writes a byte another thread reads or writes, and proves the clauses for every
interleaving. A new kernel never re-proves concurrency.

### Parser

`crates/e5r-ptx` lexes, parses and type-checks the subset and refuses
everything else with a line number: other types (`.f32`, `.u16`), state spaces
(`.shared`), instructions (`atom`, `bar.sync`, `neg`, `mad.wide`,
`ld.global.nc`), special registers (`%laneid`), and forms ptxas rejects or
whose meaning is in doubt: an instruction type PTX does not define for the
opcode (`and.u32`, `add.b32`, `setp.lo.s32`, `cvt` with `.b` types), a
special register outside `mov` and the source of `cvt`, an immediate wider
than its operand, an address offset beyond 32 signed bits, a predicated
`bra.uni`, `-0`. `ld.param` must name a parameter of exactly its type.

The parser is not trusted on its own. `roundtrip` requires the canonical
printing of the parsed module to have exactly the tokens of the source, and
to parse back to the same module. `tests/ptxas_agreement.rs` requires every
form the parser accepts to be accepted by ptxas (426 of 506 generated forms
are accepted by both; 80 only by ptxas). `tests/fuzz.rs` runs token soup,
grammar-generated kernels and their one-token mutations (3,000 cases each by
default, 200,000 run once): no panic, every refusal names a line, every
accepted kernel round-trips and exports deterministically. The fuzzer found
`-0`, which the printer turned into `0`; it is now refused.

## Assumptions and trusted base

What a theorem here does and does not establish:

1. **The Lean kernel, and the statements.** Trusted: the definitions in
   `Ptx/Syntax.lean`, `Ptx/Semantics/*`, and the statement being proved. For a
   library theorem that is its statement. For `check` it is
   `Ptx.Auto.MapSpec.Correct` (with `Pre`, `launch`, `params`, `val`) and the
   generated `spec` and `loop` definitions, which the result prints as
   `lean_spec` and `lean_loop`; a person checks them against the JSON spec.
   A weak spec proves a weak property, and nothing here detects that.
   Not trusted: the tactics, `wp_sound` and the rest of `Ptx/Logic` and
   `Ptx/Auto` (proved), the counterexample search and the interpreter
   (replayed), the Lean file generator beyond the statement it emits.
2. **The verdict logic.** `e5r-verify ptx check` decides `proved` from Lean's
   exit status, the absence of `error:` and `sorry` in its output, and the
   axiom list of `E5rCheck.correct`. That code (`src/ptx/mod.rs`, `run_lean`
   and `check`) is trusted for the exit status.
3. **The semantics' fidelity to PTX.** Written from the PTX ISA manual and
   differentially tested on the A10G (above). Modelling decisions that are
   part of it:
   - `cvta.to.global.u64` is the identity, as it is for global allocations on
     current GPUs;
   - `ld.param` reads the launch's parameter values, `.u32` zero-extended;
   - `ret` and `exit` finish the thread; falling off the end faults;
   - misaligned accesses and accesses outside every allocation fault;
   - unpredicated `bra.uni` behaves like `bra` (predicated `bra.uni` is
     refused);
   - initial registers are arbitrary.
4. **The memory model.** The interleaving semantics is sequentially
   consistent, and PTX's memory model is weaker. `RaceFree` here is strong: no
   two different threads ever make conflicting accesses, so every byte two
   threads share is only read during the kernel. That under the PTX axioms
   (coherence, causality order through program order) such a load returns the
   initial value or the thread's own last store is an argument from NVIDIA's
   model (PTX ISA §8), not a theorem of this development.
5. **PTX is not what runs.** `ptxas` or the driver compiles PTX to SASS, and
   neither is verified. The differential test observes the result of that
   translation for single instructions; it is not a proof about SASS.
6. **The launch.** The theorems assume the allocations the launch names are
   really allocated, disjoint where `Pre` says so, and that nothing else
   writes them during the kernel.
7. **Generated modules.** They are trusted to be the PTX files they name,
   through the round trip and the stale-module check in the script; `check`
   prints the SHA-256 of the PTX it read.

## Prior work

The plan asked for `lean_kernel_verify`, Trident and Velvet to be read before
designing. All three were read at source level, from shallow clones under
`/tmp`.

**`facebookresearch/lean_kernel_verify` (LKV).**

What it does:

- Frontends lower TTGIR (TLX/Triton) or CuTe DSL MLIR to a small kernel IR,
  KIR. KIR has roles, structured control flow, exact-width integer
  expressions and events.
- Lean evaluates every role of every CTA on the concrete inputs of a case
  file into event traces.
- Each spec is a decidable proposition over those traces, decided by
  `native_decide`. The specs cover bounds, wrap on address paths,
  exactly-once output coverage, mbarrier protocol, trip-count agreement and
  TMEM reuse.
- Verdicts cover the case's inputs only, and numerics are out of scope.

What was taken:

- Specs are stated over the accesses each thread makes. LKV's
  "plain write outside its work item's segment" is our `W t`.
- Exactly-once coverage. Here it is the injectivity and coverage of `gid` and
  of the stride decomposition.
- A refutation must be a certain counterexample.

What was not taken:

- `native_decide`, which our audit forbids.
- Concrete-input evaluation. Our theorems are parameterised.
- KIR itself, which models compiler IR, not PTX instructions.

LKV's core-Lean, no-Mathlib setup matches this project's.

**`alinamiretai/trident`.**

What it does:

- It gives TTIR an executable semantics and a symbolic evaluator.
- It proves the two agree (`FaithfulWFI`, threaded through every instruction).
- It verifies vector add per output lane. Matmul is partly done, with about
  2,000 lines of hand-written loop invariant.
- It reasons about one program instance. It has no grid coverage and no races,
  and its parser erases float types.

What was taken:

- The symbolic evaluator must be sound by proof, not by testing. Here that is
  `wp_sound`, proved once. `simp` performs the symbolic run inside each proof,
  so no separate evaluator needs a faithfulness proof.
- Grid coverage and races have to be part of the theorem. Trident's README
  lists their absence as a limitation, so `grid_sound` puts them in from the
  start.

**`verse-lab/velvet`.**

What it does:

- Dafny-style verification of Lean programs embedded shallowly in a monad,
  with a weakest-precondition VCGen (`velvet_vcgen`) and `grind`.
- Loop invariants with exit conditions (`done_with`).
- Partial and total correctness are proved separately.

What was taken:

- Total correctness as a WP with loop invariants and a measure (`Safe.loop`).
- VCs generated by running the program to a cut point.

What was not taken:

- The shallow embedding. A PTX program is data here, a deep embedding.
- Its dependency on `plausible`.

**Not read at source level.** These come from the plan's survey and were not
checked here:

| Work | What it does, per the plan | Relation to this project |
| --- | --- | --- |
| SentryWard | checks PTX directly: Blackwell warp-specialized kernels, launch configuration fixed, synchronization, races, resource lifetimes, equivalence against PyTorch | not in Lean |
| *Proving LLM-Generated GPU Kernels Correct and Safe* (2026-10-17) | Velvet plus VerCors on CUDA source | proves source, not the compiled PTX |
| Kuiper (PLDI 2026) | F*, separation logic over shared memory, barriers and tensor cores | some proofs still admitted |
| NVlabs `ptxmemorymodel` | Coq formalisation of the PTX memory model | requires Coq 8.4 |
| VOLTA | PTX parser | `e5r-ptx` is independent of it |
| KernelBench-Verified | AI kernel-generation tasks | candidate source for P5 |

Theorem's RISC-V binary verification (`rocq-linux-process-semantics`) is in
Rocq, not Lean.

**Where this project sits.** As far as the survey above found, no open project
combines these four things:

- `.ptx` as the direct input;
- PTX instruction and concurrency semantics in Lean;
- safety, race freedom and functional correctness in one model;
- theorems parameterised over input size and launch configuration.

## Open

- **M4: shared memory, barriers, atomics, reduction and scan.** Not started.
  The parser refuses `.shared`, `bar.sync` and `atom`, so such kernels are
  reported `unsupported`, never proved. What it needs: a per-CTA shared state
  space and atomic read-modify-write actions in the model, a barrier rule in
  `Step` (a thread at `bar.sync` waits until every thread of its CTA is
  there), race freedom relative to barrier phases, a generic theorem that
  composes per-thread, per-phase obligations the way `grid_sound` composes
  whole runs, and then proofs of a tree reduction and a scan for every block
  size. That generic theorem is the size of `RaceFreedom.lean` or larger and
  was not attempted in this session; nothing here should be read as progress
  on it beyond the design sketch in this paragraph.
- **Non-termination is never refuted.** A kernel that loops forever is
  `unknown`, not `refuted`.
- **The class is `map32` only.** One output array of 32-bit elements, one
  element per index, 1-D launches. Reductions, stencils (neighbour reads),
  64-bit elements, 2-D indexing and kernels that load scalars from global
  memory are outside it and come back `unsupported` or `unknown`.
- **M5 at the plan's scale.** 115 kernels from one model in one session, no
  automated generation loop, no Hopper or Blackwell hardware.

Not in scope, and not to be described as done:

- SASS, or the translation from PTX to it;
- floating point;
- the PTX memory model beyond the data-race-free fragment;
- warp-level instructions, tensor cores, texture or surface memory;
- any kernel the theorems or a `check` result do not name.
