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
a theorem the Lean kernel has checked.

The question this scope is built to answer:

> Can we automatically prove memory safety, race freedom, and functional
> correctness of LLM-generated NVIDIA PTX kernels directly in Lean 4, without
> trusting the LLM or a high-level compiler?

The plan names three contributions:

1. PTX semantics in Lean 4 that includes GPU concurrency, aimed at the real
   PTX ISA.
2. Automatically generated proofs for AI-written PTX, generalised over
   threads.
3. A verification procedure whose soundness is proved in Lean, so neither the
   AI nor any solver is trusted.

M1 and M2 of the plan are done (roadmap items P1 and P2). M3 to M5 are open.
"Proved" below means checked by the Lean kernel by `scripts/check-lean-ptx.sh`,
with only `propext`, `Quot.sound` and `Classical.choice` in the axiom audit.
There is no `sorry`, no `native_decide` and no `bv_decide`. The last two
check their certificates by native evaluation, which would put the compiler
in the trusted base.

## Reproduce

```sh
./scripts/check-lean-ptx.sh            # about 30 s on the development machine
CARGO_BUILD_JOBS=2 cargo test --release -p e5r-ptx
```

The script does four things:

1. It builds `e5r-verify` in release mode. `E5R_VERIFY=path` uses an existing
   binary instead; CI does this with its dev-profile build.
2. It regenerates every kernel module from its `.ptx` and fails if a committed
   module differs. Run `--update` after reviewing a change.
3. If `ptxas` is installed it assembles every benchmark for `sm_86`. On the
   development machine that is CUDA 13.2; on CI it is absent and the step says
   it was skipped.
4. It deletes `.lake/build`, runs `lake build`, and audits the axioms of the
   theorems listed in `verification/ptx/Audit.lean`.

Lean is core v4.35.0, the toolchain `verification/rv32` already uses. The
project has no `require`, so nothing is downloaded. Mathlib is not used. If it
ever becomes necessary, the plan is to share h5i-pay's built copy, not to
fetch a second one.

To export one file:

```sh
./target/release/e5r-verify ptx --namespace Ptx.Kernels.Foo FILE.ptx > Foo.lean
```

## What is proved

All of these quantify over every initial register content (`r₀`, `p₀`).
PTX leaves registers undefined at entry, so a kernel that reads one before
writing it cannot be proved correct by luck. They also quantify over every
interleaving of every thread of the launch at instruction granularity.

Each kernel theorem has the same conclusion shape over its launch `L` and
initial configuration `c₀`:

- `∀ c, Reach c₀ c → ¬ Faults c`: no out-of-allocation or misaligned access,
  no unsupported form, no missing label, no running off the end of the body.
- `∀ c, Reach c₀ c → Done c ∨ ∃ c', Step c c'`, together with a bound on the
  length of every execution. So every execution terminates, and it ends with
  every thread having executed `ret`.
- `RaceFree`: no access any thread makes in any execution shares a byte with
  a store by another thread in any execution.
- `∃ c, Reach c₀ c ∧ Done c`: a finished execution exists, so the
  correctness clause is not vacuous.
- `∀ c, Reach c₀ c → Done c → spec ∧ frame`: the outputs are right and every
  other byte of memory is unchanged.

| Theorem | Kernel | Preconditions | Spec |
| --- | --- | --- | --- |
| `Ptx.Examples.Sum.sum_correct` (M1) | `benchmarks/correct/sum.ptx`, hand-written, one thread, counted loop | `a` fits in the address space and `a`, `out` are 4-aligned; `out` may alias `a` | `out[0] = a[0] + … + a[n-1] mod 2^32` for every `.u32` `n` |
| `Ptx.Examples.VectorAdd.vadd_correct` (M2) | `benchmarks/correct/vadd_nvcc.ptx`, emitted by nvcc 13.2 from `vadd_nvcc.cu` | 1-D launch with `G·B ≤ 2^31` threads, `n ≤ G·B`, `n < 2^31`; arrays fit and are aligned; `c` overlaps neither input, though the inputs may alias each other | `c[i] = a[i] + b[i] mod 2^32` for `i < n` |
| `Ptx.Examples.Map.saxpy_correct` (M2) | `benchmarks/correct/saxpy.ptx`, hand-written, grid-stride loop | any `G`, `B`, `n`; `x` and `y` fit, are aligned and are disjoint | `y[i] = a·x[i] + y[i] mod 2^32` for `i < n`, whenever the launch has a thread |
| `Ptx.grid_sound` | every kernel | per-thread `Solo` runs and pairwise disjoint write footprints | the five clauses above |

The vadd preconditions are the ones the PTX needs, not ones chosen for the
proof:

- `G·B ≤ 2^31`. `mad.lo.s32` computes the index in 32 bits and `setp.ge.s32`
  compares it as signed. With more threads the index wraps negative, passes
  the `i < n` check, and `mul.wide.s32` turns it into an address below `a`.
- `n < 2^31`. `n` is an `int`. The `.u32` parameter `2^31` is negative, so the
  kernel writes nothing.
- `n ≤ G·B`. There is no grid-stride loop, so a smaller launch leaves the tail
  of `c` unwritten.

`saxpy` uses 64-bit indices and a grid-stride loop, and needs none of these.

The three deliberate bugs in `benchmarks/buggy` are refuted in
`Ptx/Examples/Buggy.lean`. Each refutation is a kernel-checked counterexample,
in the same semantics, on a launch that meets every hypothesis of
`vadd_correct`:

| Kernel | Change | Theorem | Counterexample |
| --- | --- | --- | --- |
| `vadd_nobound.ptx` | `i < n` check removed | `nobound_faults` | thread 1 of 2, `n = 1`, faults loading `b[1]` |
| `vadd_tid.ptx` | index is `%tid.x` only | `tid_races` | with two CTAs of one thread, one reachable configuration has both threads about to store to `c[0]` |
| `vadd_sub.ptx` | `sub` for `add` | `sub_wrong` | the only execution with `a[0] = 1`, `b[0] = 2` ends with `c[0] = 1` |

## How it works

```
.ptx --e5r-ptx--> AST --token round trip--> Lean Ptx.Module (Ptx/Kernels/*.lean, generated)
                                                  |
Ptx/Semantics: Memory, Instruction (one thread), SIMT (grid, interleaving)
Ptx/Logic:     Hoare (Safe, wp, loop rule), RaceFreedom (grid_sound), Regions, Launch1D, Refute
Ptx/Tactics:   the ptx_eval simp set
Ptx/Examples:  per-kernel specs, per-thread proofs, grid theorems, refutations
```

The proofs have two layers, as the plan asked: a generic layer proved once,
and a per-kernel layer.

### Generic layer (proved once)

`action K c s` is the next thing thread state `s` does. It is an internal
step, a `load` with a continuation that takes the bytes read, a `store`, `done`
or `fault`. Memory is never read inside the instruction table. Every
interaction with global memory is a visible action with its address and size,
so locality holds by construction.

Memory is a total map from 64-bit addresses to bytes, read and written
little-endian. An access is legal when it is naturally aligned and lies inside
one allocation of the launch. Anything else is a fault, because PTX leaves it
undefined.

Registers are 64 bits wide in the model. A 32-bit operation reads the low 32
bits and writes its result zero-extended, which is exactly `.b32` for a
well-typed kernel. The parser enforces the typing. Arithmetic wraps: `add.u32`
is `(a + b) mod 2^32`.

`Step` runs one instruction of any thread that can step, so `Reach` covers
every interleaving. No lockstep or fairness is assumed.

A per-thread proof is a `Safe` derivation. It is inductive, so it describes a
finite run: the thread, alone, from its initial state and the initial memory,
reaches its postcondition with every access legal. Loads stay in `R t ∪ W t`
and stores stay in `W t`. Three results build and use these derivations:

- `wp_sound` turns the weakest precondition up to the next cut point (`wp`)
  into a `Safe` derivation.
- `Safe.loop` is the loop rule: an invariant indexed by a decreasing measure.
- `Safe.solo` turns a derivation that ends at `ret` into the step-indexed trace
  `Solo` that the grid theorem consumes.

`grid_sound` takes `Solo` for every thread and the condition "no thread writes
a byte another thread reads or writes". Reads may overlap. From these it proves
the five clauses for every interleaving. The invariant behind the proof records
how far each thread is along its solo trace. The shared memory agrees with each
thread's solo memory on that thread's footprint and with the initial memory
everywhere else. This is the "SIMT independence" lemma of the plan: a new
kernel never re-proves concurrency.

### Per-kernel layer

1. State the footprints. For `saxpy`, thread `g` owns `y[g + qS]` and reads
   `x[g + qS]`. State a postcondition and, for loops, an invariant at the loop
   head.
2. `simp only [ptx_eval, K]` runs the instruction table symbolically until a
   cut point, `ret`, or a branch it cannot decide. Every rewrite is a
   definitional unfolding or a proved lemma, so this evaluation is part of the
   proof. The verification condition left over is access legality, footprint
   membership, the invariant or postcondition, and branch conditions.
3. Close the conditions. Array arithmetic reduces to `toNat` and `omega`
   (`Regions.lean`). Thread-index arithmetic, injectivity and coverage are in
   `Launch1D.lean`.

The kernel proofs are about 100 to 150 lines each. Most of that is the
statement and the invariant. The symbolic run of vadd takes under 3 s.

### Parser

`crates/e5r-ptx` lexes, parses and type-checks the subset and refuses
everything else with a line number. Examples of refused input: `.f32`,
`.shared`, `atom`, `bar.sync`, `%laneid`, a 64-bit operation on a 32-bit
register, an ordered comparison on a `.b` type, an undefined label.

The parser is not trusted on its own. `roundtrip` requires the canonical
printing of the parsed module to have exactly the tokens of the source, minus
comments and whitespace, with integers compared by value. It also requires
that printing to parse back to the same module. A parser bug that changes
meaning would have to be cancelled by a printer bug. The printer and the Lean
emitter are both short tables, one line per construct, written to be read
against the PTX ISA. `ptxas` accepting a benchmark shows it is real PTX.

The plan's directory names map to this layout as follows:

- `Semantics/Thread.lean` → `Instruction.lean`
- `Logic/Separation.lean` → footprints `R`/`W` in `Hoare.lean`
- `Logic/VCGen.lean` → `wp` and `wp_sound` in `Hoare.lean`
- `Tactics/*` → `Tactics/Eval.lean`
- `crates/ptx-parser` and `crates/ptx-lean-cli` → `e5r-ptx` and `e5r-verify ptx`

## Assumptions and trusted base

What a theorem here does and does not establish:

1. **The Lean kernel, and the statements.** The trusted base is the definitions
   in `Ptx/Syntax.lean` and `Ptx/Semantics/*`, plus each theorem's statement:
   launch, footprints, specification. The specification is reviewed by a
   person. A weak specification proves a weak property, and nothing here
   detects that.
2. **The semantics' fidelity to PTX.** It is written from the PTX ISA manual
   and has not been differentially tested against a GPU (roadmap P5). These
   modelling decisions are part of it:
   - `cvta.to.global.u64` is the identity, as it is for global allocations on
     current GPUs.
   - `ld.param` reads the launch's parameter values, `.u32` zero-extended.
   - `ret` and `exit` finish the thread.
   - Falling off the end of the body faults.
   - Misaligned accesses and accesses outside every allocation fault.
   - `bra.uni` behaves like `bra`.
   - Initial registers are arbitrary.
3. **The memory model.** The interleaving semantics is sequentially
   consistent, and PTX's memory model is weaker. The PTX ISA (§8.7, "Conflict
   and Data-races") defines conflicts and data races. Unlike some GPU models,
   it does not promise sequential consistency to every data-race-free program
   (Lustig et al., ASPLOS 2019).

   `RaceFree` here is stronger: no two different threads ever make
   conflicting accesses. Every byte two threads share is only read during the
   kernel. We assume that, under the PTX axioms (coherence and causality order
   through program order), a load then returns either the initial value or the
   thread's own last store to those bytes. That is what the interleaving model
   gives. This is an argument from NVIDIA's model, not a theorem of this
   development. NVlabs `ptxmemorymodel` is a formalisation it could be checked
   against.
4. **PTX is not what runs.** `ptxas` or the driver compiles PTX to SASS, and
   neither is verified. A proof about PTX is not a proof about SASS or about
   the hardware.
5. **The launch.** The theorems assume the allocations the launch names are
   really allocated, disjoint where the statement says so, and that nothing
   else writes them during the kernel.
6. **Generated modules.** They are trusted to be the PTX files they name,
   through the round trip and the stale-module check in the script.

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

## Open milestones

The plan's milestones, with what is done:

1. **M1: semantics and sequential proofs.** Done (P1).
2. **M2: SIMT and data-race freedom.** Done (P2).
3. **M3: proof automation.** The model writes PTX and the invariants, a tactic
   proves the per-thread and grid obligations, and wrong PTX yields a
   counterexample that replays. In place today:
   - the `ptx_eval` evaluation;
   - `grid_sound`, which already removes concurrency from per-kernel work;
   - `omega` for the arithmetic.

   Still missing:
   - an invariant format a model can emit;
   - a tactic that discharges the footprint and coverage obligations from it;
   - a counterexample search that produces `Refute.lean`-style witnesses.
4. **M4: shared memory, barriers, reduction.** Not started. This needs
   `.shared`, `bar.sync` and atomics in the model, and a race-freedom notion
   with happens-before through barriers. Parallel reduction and scan are the
   targets.
5. **M5: AI-generated PTX benchmark.** Not started. The pipeline is
   specification, then PTX generation, then Lean verification, then a GPU
   benchmark. It would be evaluated on 100 to 500 generated kernels: the share
   proved, safety and correctness bugs found, proof time per kernel, and speed
   against a CUDA or Triton baseline. GPU time matters only here, and this is
   where the plan's AWS budget ($10k) goes, including Hopper and Blackwell
   features. The Lean work runs on CPU.

   Agreement on a GPU does not replace a proof, and a proof in this model says
   nothing about behaviour the model leaves out. Differential testing of the
   instruction semantics against the A10G on the development machine belongs
   here as a fidelity check.

Not in scope, and not to be described as done:

- SASS, or the translation from PTX to it;
- floating point;
- the PTX memory model beyond the data-race-free fragment;
- warp-level instructions, tensor cores, texture or surface memory;
- any kernel the theorems do not name.
