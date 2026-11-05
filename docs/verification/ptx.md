# PTX kernel verification in Lean 4

This is scope P of the roadmap (owner authorization, 2026-10-31). The proof
subject is a `.ptx` file, the NVIDIA virtual ISA a model writes directly or a
compiler emits. Lean 4 checks three properties of it against a specification
written in Lean:

- memory safety;
- data-race freedom;
- functional correctness.

No CUDA C++, Triton or Rust source is part of a proof. The input is PTX
and a specification, or two concrete PTX programs and an equivalence domain.
The output is
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
the Lean kernel replayed (`verification/ptx/m5/RESULTS.md`). For two
classes of block-level kernels with shared memory, `bar.sync` and atomics
(M4: `reduce32`, block tree reductions with a per-block or an atomic total
result, and `scan32`, Hillis-Steele block scans), 6 of 14 CUDA C kernels
written independently of the tactics and compiled by nvcc were proved, 3 were
refuted with replayed counterexamples (two of them defects nobody planted: a
signed `int` length that drops every element when `n ≥ 2^31`), 1 is `unknown`
and 4 are `unsupported` (`verification/ptx/m5/m4/RESULTS.md`); two of the
unsupported ones were later proved by supplied proofs the tool checked
(`--proof`, below). For kernels where every thread combines one element into
one word with an atomic (`accum`: `add`, `and`, `or`, `xor`, and signed and
unsigned `min` and `max`, at 32 and 64 bits), 16 nvcc kernels, one per
operation and type, were proved. `atom.exch` and `atom.cas`, whose result
depends on the order, are not covered. With `.f32` and `.f64` in the model
(every correctly rounded operation of the PTX ISA, its rounding modifiers,
`.ftz` and `.sat`), the model, the interpreter and the A10G agree bit for
bit on 311 float instruction forms, and float maps are proved bit-exact up
to NaN payloads: 5 nvcc kernels and all 16 float kernels the agent wrote to
be correct (`m5/float/RESULTS.md`); 5 of 6 seeded float defects were
refuted, the sixth uses an approximate instruction the model refuses.
Error bounds against exact real arithmetic, float reductions and
approximate instructions are not proved (Open).

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
| M3 proof automation (P3) | done for `map32` | `e5r ptx check`; 102 kernels proved, 20 of 21 mutants refuted |
| M4 shared memory, barriers, reduction (P4) | done for `reduce32` and `scan32` | `phase_sound`; `reduce_correct`, `scan_correct`, `reduce_atomic_correct`; `ptx check` on 3 benchmarks and 6 M5 kernels; 0 of 14 M4 mutants proved, 14 refuted |
| M5 AI-written PTX benchmark (P5) | done, with the limits stated | `m5/RESULTS.md`; differential test against the A10G |
| Supplied proofs (P6) | done | `ptx check --proof`; `a_direct` and `s_pingpong` proved; 10 negative controls refused |
| Commutative atomics (P7) | done for `accum`; `exch` and `cas` not covered | `phase_sound` over a cell algebra; 16 `accum` benchmarks proved; 0 of 11 `accum` mutants proved, 11 refuted |
| Floating point (P8) | done for the correctly rounded operations and bit-exact `.f32` maps; error-bound proofs, float reductions, `.f64` maps and approximate instructions open | 311 float forms identical on the A10G; rounding core proved equal to lean-ieee754; 5 nvcc and 16 M5 float kernels proved; 0 of 13 float mutants proved, 13 refuted |

## Reproduce

```sh
./scripts/recheck-ptx.sh       # everything below, about 90 min on the development machine
E5R_PTX_QUICK=1 ./scripts/recheck-ptx.sh   # Lean proofs, axiom audit and benchmark verdicts only
```

Pull requests run the quick form in CI (`ci.yaml`, `ptx-verification`). The
mutation controls and the supplied-proof controls start Lean dozens of times and
are not run per push; run the full form by hand, or start the `ptx-full`
workflow from the Actions tab.

It runs, in order, and fails on the first problem:

1. the parser tests, release profile: round trip, the ptxas agreement test
   (1025 forms), grammar and mutation fuzzing, the CLI tests;
2. `scripts/check-lean-ptx.sh`: regenerate every kernel module from its `.ptx`
   and refuse a stale one, assemble every benchmark with ptxas when it is
   installed, build the Lean project from scratch, and run the axiom audit;
3. `e5r ptx check` on every benchmark against
   `benchmarks/expected.txt` (26 proved, 3 refuted, 2 unsupported);
4. the mutation controls (`mutants/run.py`): no mutant may be proved;
5. the supplied proofs and their negative controls (`proofs/controls.sh`);
6. the GPU differential test (`scripts/check-ptx-difftest.sh`), skipped with
   a note when there is no GPU;
7. the cross-check of the rounding core against lean-ieee754
   (`scripts/check-ptx-ieee-crosscheck.sh`), skipped with a note when its
   Mathlib dependency (about 8 GB) has not been fetched.

The M5 benchmark is separate because it needs the GPU and takes 12 minutes
for the M3 part and about 2 hours for the M4 part (most of it failed proof
attempts on mutants running into the timeout):

```sh
python3.12 verification/ptx/m5/run.py ./target/release/e5r /tmp/m5
python3 verification/ptx/m5/report.py /tmp/m5/results.json
python3.12 verification/ptx/m5/m4/run4.py ./target/release/e5r /tmp/m5m4
python3.12 verification/ptx/m5/m4/run4.py --mutants ./target/release/e5r /tmp/m5mut
python3 verification/ptx/m5/m4/report4.py    # reads the copies in m5/m4/
python3.12 verification/ptx/m5/float/run_float.py ./target/release/e5r /tmp/m5f
python3 verification/ptx/m5/float/report_float.py   # reads the copies in m5/float/
```

Lean is core v4.35.0, the toolchain `verification/rv32` already uses. The
project has no `require`, so nothing is downloaded. Mathlib is not used.
The cross-check (`verification/ptx-ieee-crosscheck`) is a separate project
on lean-ieee754's toolchain (v4.33.1) with Mathlib; nothing in
`verification/ptx` depends on it.

Lean is capped on purpose: a Lean process was OOM-killed at 15 GB on the
development machine. The scripts run Lean with `LEAN_NUM_THREADS=2` under a
10 GB cgroup limit (`systemd-run`, no swap; override with `PTX_LEAN_MEMORY`).
`e5r ptx check` runs one Lean thread under a 6 GB cap and a 600 s
timeout (`--memory-mb`, `--timeout`). Without systemd only the thread count
and the timeout apply.

## Command line

```
e5r ptx export [--namespace NS] [--name NAME] FILE.ptx
e5r ptx check FILE.ptx --spec SPEC.json [--project DIR] [--out RESULT.json]
                     [--keep DIR] [--timeout SECS] [--memory-mb MB] [--no-search]
                     [--proof PROOF.lean]
e5r ptx run --cases CASES FILE.ptx
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
| 2 | `unsupported` | the PTX is outside the subset, or the spec or kernel outside the class (for the block classes also: outside the shape the class's proof handles, with no counterexample found) |
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

### Float maps (`map32` with `"element_type": "f32"`)

```json
{ "schema": "e5r.ptx.spec.v1", "kernel": "saxpy_f32", "class": "map32",
  "element_type": "f32",
  "arrays": ["saxpy_f32_param_1", "saxpy_f32_param_2"], "output": "saxpy_f32_param_2",
  "length": "saxpy_f32_param_3", "scalars": ["saxpy_f32_param_0"],
  "element": "fma.rn(saxpy_f32_param_0, saxpy_f32_param_1, saxpy_f32_param_2)",
  "result": "bit_exact",
  "schedule": { "kind": "guarded", "max_threads": "2^32" } }
```

- The arrays hold `.f32` elements and the scalars are `.f32` parameters.
- `element` is an expression of the model's own operations, spelled like
  the instructions: `add sub mul div fma sqrt rcp` with a rounding modifier
  (`.rn .rz .rm .rp`) and optional `.ftz`/`.sat` where PTX has them,
  `neg abs` with optional `.ftz`, `min max` with optional `.ftz`/`.NaN`, and
  `0fXXXXXXXX` literals. Each node is the operation of
  `Ptx/Semantics/Float.lean` (`Ptx.Auto.F32.*`), so the spec states exact
  bits, not real numbers.
- `result` is `"bit_exact"` (the default): every output element has
  exactly the bits of `element`, except that where `element` is a NaN the
  output is some NaN (`Ptx.Fp.feq32`). The exception is forced: PTX does not
  fix NaN bits (below). Or `{"max_ulps": k}`: both NaN, the same infinity,
  or both finite and at most `k` representable numbers apart
  (`Ptx.Fp.within32 k`). The checker proves `max_ulps` only where the kernel
  is bit-exact; a bound against a differently rounded or exact real
  computation is not proved (Open).
- `MapSpec.Correct` quantifies over the launch's NaN oracle as over every
  other launch input.

### The block specs (`reduce32`, `scan32`)

```json
{ "schema": "e5r.ptx.spec.v1", "kernel": "reduce", "class": "reduce32",
  "result": "per_block",
  "input": "reduce_param_0", "output": "reduce_param_1", "length": "reduce_param_2",
  "shared": "_ZZ6reduceE1s", "max_block": 1024,
  "barriers": {
    "after_load": { "%r1": "ntid", "%r2": "ctaid", "%r3": "tid",
                    "%r7": "shared_tid", "%rd2": "output" },
    "loop": { "%r22": "stride", "%r2": "ctaid", "%r3": "tid",
              "%r7": "shared_tid", "%rd2": "output" } } }
```

- The kernel has exactly three parameters: `input` and `output` (`.u64`) and
  `length` (`.u32`). `shared` names a `.shared` array of 32-bit words with
  room for `max_block` (a power of two up to 1024) words.
- `reduce32` claims, for blocks of `B = 2^j ≤ max_block` threads and any
  `G` with `G·B ≤ 2^32` and any `n`: with `result: per_block`, `out[b]` is
  the sum of block `b`'s segment `x[b·B .. b·B + B)` (elements at or past `n`
  count as 0); with `result: atomic`, `*out` ends as its initial value plus
  `x[0] + … + x[min(n, G·B) − 1]`, whatever order the blocks add in. `scan32`
  claims, for any `1 ≤ B ≤ max_block` and `n ≤ G·B`, that `out[i]` is the sum
  of `x[j]` from the start of `i`'s block to `i`. In both, every other byte
  is unchanged, and the clauses of the M3 theorem (no fault, progress,
  bounded executions, race freedom, a finished execution exists) hold.
- `barriers` is the phase invariant: what live registers hold right after
  each `bar.sync`, in program order (`reduce32`: `after_load`, `loop`;
  `scan32`: `after_load`, `after_read`, `after_add`). Roles: `ntid`, `ctaid`,
  `tid`, `gid` (`ctaid·ntid + tid`), `shared_tid` (address of `s[tid]`),
  `shared_base`, `input`, `output`, `length`, `stride` and `stride_prev`
  (`reduce32`, the stride of the phase that just ended and of the one before
  it), `offset` (`scan32`, the round's `2^k`), `read` (`scan32`, the value
  the thread read in the round), and the predicates `gid >= length`,
  `gid < length`, `tid < offset`. The roles are claims the proof
  establishes; a wrong role makes the proof fail, not the theorem false.

What the checker does with such a spec: the statement (`Reduce32.Correct`,
`Reduce32.Atomic.Correct` or `Scan32.Correct` of the generated `spec`) needs
only the parameters. If the kernel also has the class's shape (the shared
array, the number of `bar.sync`, declared registers for the roles), the
generated file proves the phase obligations and applies the class theorem.
Otherwise, or if that fails, the barrier-aware search runs. With no proof
and no replayed counterexample the verdict is `unknown` inside the shape and
`unsupported` outside it.

### The atomic spec (`accum`)

```json
{ "schema": "e5r.ptx.spec.v1", "kernel": "acc_min_s32", "class": "accum",
  "op": "min", "type": "s32",
  "input": "acc_min_s32_param_0", "output": "acc_min_s32_param_1",
  "length": "acc_min_s32_param_2" }
```

- `op` is `add`, `min`, `max`, `and`, `or` or `xor`; `type` is `u32`, `s32`,
  `b32`, `u64`, `s64` or `b64`. `min` and `max` compare signed for `s` types
  and unsigned otherwise; `add` takes `u` or `s`, the bitwise operations any
  type of their width. Each pair names one algebra of
  `Ptx/Logic/CellAlgs.lean` (`add32`, `mins32`, `maxu64`, ...). `exch` and
  `cas` are refused as `unsupported`.
- The kernel has exactly three parameters: `input` and `output` (`.u64`) and
  `length` (`.u32`).
- `Accum.Correct spec K` (`Ptx/Auto/Accum.lean`) claims, for every 1-D launch
  with `G·B ≤ 2^32`, any `n`, an input of `n` elements of the type's width and
  an output word that fit, are aligned to that width and do not overlap: the
  five clauses of the M3 theorem, and when all threads are done
  `*out = op(*out₀, x[0], …, x[min(n, G·B) − 1])` (the fold of the algebra,
  in index order, which any order equals), and no byte outside `*out`
  changed.

The generated proof is one phase obligation per thread (from `pc 0` to the
end, reading `x[gid]` when `gid < n`, combining it into `*out`); the class
theorem `Accum.correct_of` is proved once from `phase_sound`. The proof is
attempted only if every atomic in the kernel is `atom` or `red` with the
spec's algebra; otherwise, or if it fails, the search runs (worlds up to 3
blocks of up to 8 threads, lengths around the grid size, `2^31` and
`2^32 − 1`, inputs with sign-bit and all-ones patterns).

### Supplied proofs (`--proof`)

For a kernel the automation cannot handle, `check --proof PROOF.lean` checks
a proof someone else wrote. The tool, not the author, writes the theorem
statement:

1. It generates module `E5rSpec` from the PTX and the spec: the kernel as
   exported, the spec definition, and `E5rSpec.statement : Prop`, the same
   class statement the automation would prove (`spec.Correct K` for `map32`,
   `Reduce32.Correct`, `Reduce32.Atomic.Correct` or `Scan32.Correct` for the
   block classes, `Accum.Correct` for `accum`). Only the statement-level checks apply (parameter names and
   types); the class's proof shape (barrier count, roles, shared array) does
   not.
2. The supplied file must be module `E5rProof`, contain a manifest
   `/- e5r-proof ptx=<sha256> spec=<sha256> toolchain=<lean-toolchain> -/`
   naming the exact inputs it was written for, and prove
   `theorem E5rProof.correct : E5rSpec.statement`. A manifest that does not
   match the PTX, the spec or the project's toolchain is refused.
3. Both modules are compiled under the caps. Then the separate checker
   `proofcheck` (`Checker/ProofCheck.lean`, a `lake` executable) loads the
   compiled environment and: refuses imports other than `E5rSpec`, `Ptx.*`,
   `Init`, `Std`, `Lean`; refuses any `axiom` the proof declares; sends every
   declaration of the proof module to the kernel again
   (`Kernel.Environment.replay`) on an environment with only its imports, so
   `set_option debug.skipKernelTC` or a metaprogram that adds an unchecked
   declaration does not get through; requires `E5rProof.correct` to be a
   theorem whose type is the constant `E5rSpec.statement`; and requires its
   transitive axioms to be among `propext`, `Quot.sound`, `Classical.choice`.

Only then is the verdict `proved`, with `"theorem": {"generated": false,
...}` and `"proof": {"supplied": true, "sha256", "manifest", "check"}` in the
result. A refused proof is `unknown` (exit 3) with the reason; with
`--proof` no proof is generated and no counterexample is searched.

`proofs/controls.sh` (part of the recheck) checks the two supplied proofs
and ten refusals: a proof of `True`, a proof of a different statement,
`sorry`, a declared axiom, an unchecked declaration added with
`debug.skipKernelTC`, `native_decide` (it does not compile in this setting;
its `Lean.ofReduceBool` axiom would be refused by the audit if it did), a
forbidden import, a spec edited after the proof was written, a different
toolchain, and a missing manifest.

| Kernel | Why the automation does not apply | Supplied proof | Statement |
| --- | --- | --- | --- |
| `m5/m4/kernels/a_direct.ptx` | no shared array, no barrier: one `atom.global.add.u32` per element | `proofs/a_direct.lean`, one phase of `phase_sound` per thread with `*out` the accumulator cell | `Reduce32.Atomic.Correct` |
| `m5/m4/kernels/s_pingpong.ptx` | two shared buffers and one barrier per round, `scan32` expects three in place | `proofs/s_pingpong.lean`, `R + 2` phases; buffer `(k+1) % 2` holds `Scan32.V (k+1)` after round `k` | `Scan32.Correct` |

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

### M4: shared memory, barriers, atomics

The model (`Ptx/Semantics`) has, per CTA, a shared memory and a count of the
barriers passed. `ld/st.shared` address the CTA's shared window with the
32-bit register value; `atom`, `red` (`add min max exch and or xor`, `.u32
.s32 .b32 .u64 .s64 .b64` as PTX defines them) and `atom.cas` are one
read-modify-write action. `bar.sync 0` makes the thread wait; `Step` has a
second rule that releases a CTA when every thread of it waits at the same
`bar.sync`. A CTA where one thread waits and another has finished or waits at
a different `bar.sync` is `Diverged`, which `Faults` includes.

`RaceFree` is phase-relative: two different threads' pending accesses in any
two reachable configurations that share a byte, where one writes, must be
atomics on exactly the same location, or belong to one CTA in different
barrier phases.

`Ptx.Phased.phase_sound` (`Ptx/Logic/PhaseSound.lean`) is the composition
theorem. Its hypotheses are, per thread and phase, a `Run` derivation: from
the entry state the phase's code reaches the next barrier (or the end) with
every access inside the phase's read and write footprint, legal, and every
written location holding what the per-phase memory `M` says; footprints of
different threads of one CTA are disjoint within a phase; no global byte
one CTA writes is touched by another; and global atomics to designated
accumulator cells, outside every footprint, are recorded as ghost
contributions of the phased kernel's cell algebra (below). It concludes the
five clauses of the M3 theorem for every interleaving, the final memory on
every written location, and each accumulator cell's final value as
`op(initial value, fold of all contributions)`. `grid_sound` (M2) is
re-proved on the new `Step`.

The class theorems `Ptx.Auto.Reduce32.correct_of`,
`Ptx.Auto.Reduce32.Atomic.correct_of` and `Ptx.Auto.Scan32.correct_of`
(`Ptx/Auto`) are proved once from it: footprints, per-phase shared memory as
`cells` of the tree or window values, and the algebra (`V_tree`: after phase
`k`, `s[i]` is the sum of `2^k` elements strided by `B / 2^k`; `V_window`:
after round `k`, `s[i]` is the sum of the `2^k` elements ending at `i`). Their
only kernel-dependent hypothesis is the structure `Obligations`: one `Run`
per phase kind from the entry states a `Code` claims (the spec's roles). The
generated file supplies the `Code`, proves `Obligations` with the M4 tactics
(`Ptx/Auto/Tactic4.lean`), and applies the class theorem.

### Atomics: cell algebras

`phase_sound` is stated for a `CellAlg` (`Ptx/Logic/Phases.lean`): a size
(`.b4` or `.b8`), an operation `op` on values truncated to it, a unit `e`, and
proofs that `op` is commutative and associative, that `e` is its unit, and
that `op` stays truncated. In a `Run`, an atomic on a cell needs a
contribution `δ` with `Accum A g δ`: the instruction's update function `g`
(what the model's `atom`/`red` does to the old value) is `fun old => op old
δ` on every old value. The value the atomic returns is universally
quantified, so a kernel may use it, but the proof learns nothing about it.

`Ptx/Logic/CellAlgs.lean` defines the 16 algebras PTX's commutative,
associative atomics give and proves their laws: `add`, `and`, `or`, `xor`,
unsigned `min`/`max` (units all-ones and 0) and signed `min`/`max` (units
`2^(w−1) − 1` and `−2^(w−1)`), at 32 and 64 bits, and for each the lemma
`accum_<alg>` that the model's update for that instruction form is
`op old b`. 32-bit atomics act on the low 32 bits of the register value
zero-extended, so the 32-bit algebras work on `ext32 (lo32 v)`.

Not covered, and why:

- **`atom.exch` and `atom.cas`.** Their final value depends on the order the
  threads ran in. The ghost of `phase_sound` is a fold of a commutative
  operation, which is order-independent by construction. The update of exch,
  `fun _ => b`, has the form `op old δ` for every old value only when `b`
  absorbs the algebra (exchanging 0 is `and` with 0, all-ones is `or` with
  all-ones, an extreme value is `min` or `max` with it); the update of cas,
  `fun old => if old = a then b else old`, only in similarly degenerate
  cases. For what these instructions are used for (publishing a thread's
  own value, taking a lock) no algebra fits, `Accum` cannot be proved, and
  the kernel gets no proof; the `accum` class refuses both outright. A rule
  for them would need a different invariant: a set of values the cell may
  hold, preserved by every step of every thread (for exch: the initial value
  or one of the written values; for a lock or flag protocol: a relation
  between the cell and the data it guards, and for spin loops a fairness
  assumption the model does not make). That is not built. The model and the
  differential test have both instructions.
- **Atomics on shared memory** are in the model; `Run` has no rule for
  them, so a kernel accumulating in shared memory gets no proof.
- **Several operations on one kernel's cells.** A `Phased` has one algebra,
  so a kernel that, say, adds into one word and takes the max into another
  gets no proof from the classes.
- **The returned old value** carries no information (above).

### Floating point

**Model.** `Ptx/Semantics/FloatCore.lean` and `Float.lean`, written from
the PTX ISA 9.4 (9.7.3 floating-point instructions, Tables 23 to 25 of
9.3.1.2, 9.7.10.24 `cvt`) and IEEE 754-2019 (§4.3 rounding, §6.3 zero
signs, §7.4 overflow, §7.5 tininess). A value is its bit pattern. Each
correctly rounded operation computes the exact result as a rational (a
square root by comparing `q` with squares) and rounds it once:
`add sub mul fma div rcp sqrt` at `.rn .rz .rm .rp`, `min max` (with
`.NaN`), `neg abs`, `setp` with all 14 comparisons, and `cvt` between
`.f32`, `.f64` and the four integer types with every rounding (`.rn .rz .rm
.rp`, `.rni .rzi .rmi .rpi` for integers and for rounding to an integral
float). `.ftz` flushes subnormal inputs and results to sign-preserving zero
(f32 only, as the ISA allows); `.sat` clamps to `[+0.0, 1.0]` with NaN to
`+0.0`; float-to-integer conversions clamp and send NaN to 0, or to
`1 << (w − 1)` when the source is `.f64` or the destination is 64-bit.

Where the ISA's text is not a complete specification, the model does this:

- **`.ftz` on results** flushes a result that is tiny after rounding with
  an unbounded exponent (IEEE 754 §7.5's after-rounding test). The ISA only
  says "subnormal results"; the A10G flushes `fma.rn.ftz` of
  `2^-126 − 2^-150` (exactly representable below the smallest normal) and
  keeps `2^-126 − 2^-152` (which rounds to the smallest normal), which only
  this rule gives. Measured, and checked by the difftest.
- **`add`, `sub`, `mul` without a rounding modifier** are refused. The ISA
  says ptxas may fuse such a `mul` with an `add` into an `fma`, so their
  result is not determined by the instruction. nvcc emits them for `x + y`
  with its default `-fmad=true`; those kernels are `unsupported`
  (`benchmarks/correct/float/fadd_default.ptx`).
- **NaN results** follow the ISA's text, not measured hardware. The ISA
  says single-precision instructions "return an unspecified NaN" and that
  double precision supports payloads without saying which input's payload a
  result carries; for `neg`, `abs` and the `cvt` forms it is also
  unspecified. The A10G returns `0x7fffffff` for f32 arithmetic and
  `0xfff8000000000000` for invalid f64 operations, but which input's
  payload an f64 result carries depends on the operand order ptxas chose
  (`add(qa, qb)` returned `qb` with the operands loaded from memory and `qa`
  when ptxas constant-folded the same instruction), and `neg.f32` of a NaN
  returned a sign-flipped payload when folded and `0x7fffffff` at run time.
  Fixing any one rule would make theorems claim bits the hardware does not
  promise. So every NaN result takes its bits from the launch's NaN oracle
  (`Launch.nan : Tid → TState → Val`, forced to be a NaN of the format), and
  float theorems hold for every oracle. Integer instructions never read it,
  and every result that is not NaN is fully determined.
- **Approximate instructions** (`sin cos lg2 ex2 tanh rsqrt` and the
  `.approx`/`.full` forms of `div rcp sqrt`) are refused as unsupported.
  NVIDIA documents bounds for some of them (`rcp.approx.f32` at most 1 ulp,
  `sqrt.approx.f32` relative error `2^-23`, `div.approx.f32` 2 ulp for
  `|b|` in `[2^-126, 2^126]`), but a bound is a set of allowed results, and
  using one would need an oracle constrained by it in the launch, a GPU
  check of the bound (exhaustive over f32 for the unary ones), and
  error-bound reasoning in the proofs, none of which is built. Each bound
  in the documentation also has range conditions and special cases that
  would have to be modelled exactly.
- Not modelled: `.f16`, `.bf16`, `.f32x2`, `mad.f32`, `copysign`, `testp`,
  `min/max.xorsign.abs`, three-input `min/max`, `.rna`, `.rs`, float atomics
  and `cvt.f32.f32` without integer rounding.

**Differential test.** The float forms run like the integer ones (below):
311 kernels, every operation at every rounding with and without `.ftz` and
`.sat`, every comparison, every conversion, literals, moves, loads and
stores, each on 2176 threads whose inputs are the pairs of 45 (f32) or 42
(f64) edge values (zeros, subnormals, the smallest normal, `±1`, values one
unit in the last place apart, the largest finite number, infinities, quiet
and signalling NaNs, integer and overflow boundaries) and random patterns,
random normal numbers, values near the subnormal and overflow boundaries,
and pairs that cancel. A float result is stored with every NaN replaced by
one pattern first (`setp.nan`, `selp`), since its bits are unspecified;
every other result is compared bit for bit. Measured on the A10G: identical
on all 622 float launches (about 677,000 results). Planted errors were
detected: ties rounded away from zero (69 launches differ) and `.ftz`
deciding tininess before rounding (9 launches differ).

**Cross-check against lean-ieee754.** The rounding core
(`FloatCore.lean`) is in the trusted base, so it was compared with an
independent IEEE 754 specification. `verification/ptx-ieee-crosscheck`
proves, with Mathlib, for every rational, both formats and the four
rounding modes (`Crosscheck/Rounding.lean`):
`roundQ = roundWithMode`, `precRoundQ = precisionRoundWithMode`,
`overflows ↔ OverflowWithMode`, `tiny ↔ TinyWithMode`, and
`roundSqrtQ q = roundWithMode (√q)`, the finite result lean-ieee754's
`Sqrt` contract requires; `binary32` and `binary64` are the model's
formats. Its axiom audit covers the 838 declarations involved; all of
lean-ieee754 (3697 declarations, built at 529ed78 under a 7 GB cap in 4
minutes) uses only the three standard axioms. The bit-pattern layer
(decoding, encoding, special operands, zero signs, NaNs, `.sat`) is not
cross-checked; the difftest checks it.

The decision on lean-ieee754
(https://github.com/tunnellm/lean-ieee754, Apache-2.0, 529ed78): use it
only as an independent cross-check, not as a dependency and not vendored.

- Depending on it would put Mathlib in the main project's build and
  trusted base and pin it to Lean v4.33.1, against this project's v4.35.0
  (`.olean` files do not cross toolchains), and its definitions are
  noncomputable over `ℝ`. The model has to execute: the difftest runs it,
  and refutations are decided by the Lean kernel evaluating it.
- Vendoring parts would bring the same Mathlib dependency, since its
  `Spec` is stated with `ℝ`, `Int.log` and `Int.floor`.
- Its specification is not PTX. Its NaN policy (a deterministic choice of
  an input payload, a positive canonical NaN for invalid operations) is
  IEEE-style where PTX leaves NaN bits unspecified, and it has no `.ftz`,
  `.sat` or PTX `min`/`max`. Read against IEEE 754-2019, its rounding
  definitions (`roundInteger`, `roundWithMode` with
  `quantum = 2^(max(emin, ⌊log₂|x|⌋) − p + 1)`, `OverflowWithMode` on the
  unbounded-exponent result, `TinyWithMode` after rounding,
  `OverflowToInfinity` by direction, the zero-sign rule of §6.3 in
  `arithmeticCase`) agree with the standard; those are the parts the
  cross-check uses. Its README says it is mostly LLM-written without
  expert review, so agreement is evidence from a second, independently
  written statement, not an authority; the A10G difftest stays the
  hardware check.

**Automation.** `Ptx/Auto/FloatMap.lean`. The map class theorem is
unchanged except that the output relation is a parameter (`MapSpec.rel`,
equality for integer maps) and the launch carries the NaN oracle. After
the symbolic run, the kernel's output is `lo32 (fres c s .f32 R)` for an
operation tree `R`; the spec's is the same tree with `F32.lift`. `ptx_fnode`
matches them node by node: equal leaves (loaded words, scalars, literals),
inner results through `fres_nanEq_of_eq`, and each operation through a
congruence lemma (`fadd_congr`, ..., `fminmax_congr`) stating that it
gives the same result for any two NaN inputs, so the oracle's choice never
matters. `ffma_comm`, `fmul_comm` and `fadd_comm` (proved by cases on the
operands' classes) let it accept commuted operands, which nvcc produces.
The match backtracks; a mismatch leaves the goal open, so the verdict is
`unknown`, never `proved`. Refutations of float values are decided by
`decide +kernel`: the Lean kernel evaluates the model on the
counterexample.

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
| `Ptx.Phased.phase_sound` (M4) | every kernel | per-phase `Run` derivations, footprint disjointness, accumulator cells of one `CellAlg` | the five clauses, final memory, each cell = `op(initial, fold of contributions)` |
| `Ptx.Examples.Reduce.reduce_correct` (M4) | `benchmarks/correct/reduce_nvcc.ptx`, nvcc 13.2 | `B = 2^j ≤ 1024`, `G·B ≤ 2^32`, any `n`; arrays fit, aligned, disjoint; any shared placement ptxas could choose | `out[b]` = sum of block `b`'s segment |
| `Ptx.Examples.ReduceAtomic.reduce_atomic_correct` (M4) | `reduce_atomic_nvcc.ptx` | as above, one output word | `*out` = initial + sum of `x[0 .. min(n, G·B))` |
| `Ptx.Examples.Scan.scan_correct` (M4) | `scan_nvcc.ptx` | `1 ≤ B ≤ 1024`, `n ≤ G·B ≤ 2^32` | `out[i]` = inclusive prefix sum of `i`'s block segment |
| `Ptx.Auto.Reduce32.correct_of`, `Reduce32.Atomic.correct_of`, `Scan32.correct_of` (M4) | every `reduce32` / `scan32` kernel | `Obligations` | the class's `Correct` |
| `Ptx.Auto.Accum.correct_of` | every `accum` kernel, all 16 algebras | `Obligation` (one phase per thread) | `Accum.Correct` |
| `E5rCheck.correct` (generated) | `benchmarks/correct/accum/acc_*.ptx`, nvcc 13.2 | `Accum.Args.Pre` | `Accum.Correct` for `add.u32 add.u64 and/or/xor.b32 and/or/xor.b64 min/max.u32 min/max.s32 min/max.u64 min/max.s64` |
| `E5rProof.correct` (supplied) | `m5/m4/kernels/a_direct.ptx`, `s_pingpong.ptx` | the class's `Pre` | `Reduce32.Atomic.Correct`, `Scan32.Correct` |
| `E5rCheck.correct` (generated) | `benchmarks/correct/float/saxpy_f32.ptx`, `fdefault.ptx` (nvcc 13.2) | `MapSpec.Pre`, any NaN oracle | output = `fma.rn(a, x, y)`, `div.rn(x, y)`, `sqrt.rn(x)`, `max(x, 0)` bit for bit, any NaN where that is NaN |
| `Crosscheck.roundQ_eq`, `overflows_iff`, `tiny_iff`, `roundSqrtQ_eq` (separate project, Mathlib) | the rounding core | none | equal to lean-ieee754's `roundWithMode`, `OverflowWithMode`, `TinyWithMode` |

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

For the block classes the search runs small launches (up to 3 blocks of up
to 8 threads, lengths around the grid size and, for `reduce32`, `2^31` and
`2^32 − 1`) on the interpreter with one schedule of the whole grid: block
after block, each thread until it waits or finishes, then the barrier's
release. It records the schedule as the choices `Ptx.Cfg.exec`
(`Ptx/Logic/Schedule.lean`) replays, each run of a thread or release of a
barrier checked to be a `Step` (`exec_reach`). A fault or diverged barrier,
two accesses `RaceFree` forbids (two prefixes of the schedule, one ending
before each access), or a finished launch with a wrong output word or a
changed byte becomes `¬ Correct`, decided by `decide +kernel` over the
closed term: the Lean kernel evaluates the model on that launch.

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

The M4 benchmarks have 14 more (`reduce`, `reduce_atomic`, `scan`): a
removed `bar.sync` in the tree loop or between a scan round's read and add,
bound tests flipped, a halved first stride, every thread storing the block
result, the wrong value stored, `atom.add` replaced by a plain store or by
`atom.max`, the scan's offset multiplied by 4, the scan's store guard
removed, and the spec's `result` changed to `atomic`. Measured: 0 of 14
proved, 14 refuted with a replayed counterexample (2 faults, 5 races, 7 wrong
values).

The 16 `accum` benchmarks have 11 more: `min` replaced by `max`, `s32` by
`u32` in the instruction and, separately, in the spec, the bound check
removed, the load moved to `x[i+1]`, the atomic replaced by a plain store,
the spec's operation changed (`add` to `xor`), `and` to `or`, a 64-bit
element read with a 4-byte stride, unsigned `max` made signed, and a 64-bit
add done as a 32-bit add of the low word. Measured: 0 of 11 proved, 11
refuted with a replayed counterexample (3 faults, 8 wrong values). The plain
store is refuted as a wrong value (one thread, `*out` not combined), which
comes first in the search, not as a race.

The float benchmarks have 13 more: `fma.rn` to `fma.rz`, the fma split into
`mul.rn` and `add.rn`, `a·y + x`, `.ftz` and `.sat` added, the bound check
removed, a load from `x[i+1]`, the spec's rounding changed to `.rm` and to a
separately rounded product, `div.rn` to `div.rz`, `y / x`, `max` to `min`
and `sqrt.rn` to `sqrt.rp`. Measured: 0 of 13 proved, 13 refuted with a
replayed counterexample (2 faults, 11 wrong values).

The axiom audit was checked the same way: a module with an `axiom` and a
`native_decide` added to the library makes `Audit.lean` fail, naming both.
The ptxas agreement test was checked by letting the parser accept `and.u32`;
it failed and listed the forms.

## Differential testing against the GPU

`scripts/check-ptx-difftest.sh` runs 1693 launches of 856 generated kernels
(311 of them float forms, described under "Floating point"),
one per instruction form of the subset (every operation at every type the
parser accepts, register and immediate operands including edge values,
shifts by 0 to 100 and by 2^32 − 1, every comparison, every conversion,
loads and stores at every type and at positive and negative offsets,
`ld.param`, guards, branches, a loop, and all special registers on 3-D
launches; for M4 `ld/st.shared`, `bar.sync` between phases that exchange
values through shared memory, every `atom`, `red` and `atom.cas` form on
global and shared memory, uncontended, and with every thread on one address
for all 16 commutative, associative operation and type pairs),
on 64 to 128 threads each with edge-value and pseudo-random
inputs (fixed seed). The same launches run:

- on the A10G from the PTX text (driver JIT);
- on the A10G from a ptxas cubin;
- in Lean, executing the definitions of `Ptx.Semantics` (`lake exe ptxdiff`);
- on the concrete interpreter of `e5r-ptx` (`ptx run`).

The Lean side runs the CTAs with the same schedule as the interpreter
(`Diff/Main.lean`), so contended atomics compare the same order; their final
values do not depend on it for the commutative operations tested.

Measured on the A10G, driver 595.112.07, CUDA 13.2: all four outputs are
identical byte for byte on all 1693 launches. Ten misaligned accesses fault
in the model and are refused by the GPU with
`CUDA_ERROR_MISALIGNED_ADDRESS`. A planted error in the model (`atom.min.s32`
compared unsigned) was detected by the test. Out-of-bounds accesses are not
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

### M4 part (`m5/m4/`)

Fourteen CUDA C kernels written in one pass before any was checked
(reductions per block and with `atomicAdd`, scans, in the styles tutorials
use: `unsigned` and `int` indices, `/ 2` and `>>= 1`, `while` loops, a
256-word buffer, interleaved addressing, an early return, the old samples'
unrolled last warp, one `atomicAdd` per element, a double-buffered scan),
compiled by nvcc -O3, specs written from the PTX. Nothing was planted.

| run | proved | refuted | unknown | unsupported |
| --- | --- | --- | --- | --- |
| first run | 3 | 1 | 6 | 4 |
| after the fixes the first run prompted | 6 | 3 | 1 | 4 |

- The fixes: a fallback for `s[t+k] + s[t]` (operands commuted), two facts
  about strides (`stride 0 = B`, `stride k ≥ 2` before the last phase), two
  new roles (`stride_prev`, the predicate `tid < offset`) with the spec
  changes for `r_while` and `s_cond`, the path where a scan thread skips its
  add, and search lengths `2^31` and `2^32 − 1`.
- Refuted, and not planted: `r_int` and `a_int` declare the length `int`.
  For `n ≥ 2^31` the signed comparison makes every thread skip its load, so
  the result is 0 instead of the sum (`n = 2^31`, one thread). The GPU test,
  with small `n`, passes them. `r_earlyret` returns before `__syncthreads`
  when `i ≥ n`; with one thread and `n = 0` the block's `out[0]` is never
  written. The GPU test also fails it.
- `s_int` has the same signed length but needs `n ≤ G·B`, so the
  counterexample needs `2^31` threads; the search cannot run that and the
  proof fails at the signed comparison: `unknown`.
- Unsupported: `rem.u32` (interleaved addressing) and `ld.volatile.shared`
  (the unrolled warp, which is a race under PTX's memory model even where it
  works on the GPU) are outside the subset; one `atomicAdd` per element has
  no shared array, and the double-buffered scan has one barrier per round,
  outside the classes' shapes.
- After the run: `a_direct` and `s_pingpong` were proved by supplied proofs
  (`proofs/`), checked by `check --proof` against the statements their
  original specs generate. `a_direct` is also proved by the `accum` class
  with `specs/a_direct_accum.json` (13 s). That is not an independent test
  of the class: `accum` was built after this kernel was seen, and
  `benchmarks/correct/accum/acc_add_u32.ptx` is the same code.
- Proof time median 49 s (`reduce32` and `scan32` obligations run the
  instruction table per phase); replays 2 s.
- Random mechanical mutants of three proved kernels (24, seeded): see
  `m5/m4/RESULTS.md`.

### Float part (`m5/float/`)

22 `.f32` map kernels the agent wrote in one pass before any was checked,
but after the float automation was built, so not blind to it: 16 meant to
be correct (fused and unfused axpy, `.ftz` scaling, ReLU, clamping with
`.sat`, abs, negation, `sqrt`, division, reciprocal, lerp, a 3-way min,
Horner's rule with two fmas, `max.NaN`, round-toward-zero addition, a
grid-stride saxpy) and 6 with a seeded defect. 21 share one skeleton
(`write_kernels.py`); the stride kernel is written by hand. The GPU test
runs each kernel and a CUDA C baseline using the intrinsic of the same
rounding (`__fmaf_rn`, `__fdiv_rn`, ...; nvcc -O3, `-ftz=true` where the task
flushes) on the same 133,094 inputs (edge values, random patterns, random
normal numbers) and requires equal bits, any NaN matching any NaN. The
baseline does not use the Lean model.

| | kernels | proved | refuted | unknown | unsupported |
| --- | --- | --- | --- | --- | --- |
| written to be correct, first run | 16 | 16 | 0 | 0 | 0 |
| seeded defect, first run | 6 | 0 | 4 | 1 | 1 |
| seeded defect, after the fix | 6 | 0 | 5 | 0 | 1 |

- All 16 proved kernels agree with their baselines on the GPU; all 6
  seeded kernels differ from theirs. Proof time median 4.1 s, max 10.3 s.
  Speed against the baseline: median 1.00.
- The fix: `fbug_axpy_fused` (an fma where the spec rounds the product
  first) was `unknown` because the search, 44 small launches of random bit
  patterns, found no input where the two roundings differ. The search now
  also draws normal numbers of nearby magnitude and tries 2000 one-element
  launches for float maps; the counterexample it then found was replayed in
  Lean.
- `fbug_div_approx` (`div.approx.f32`) is `unsupported`: the model refuses
  approximate instructions.
- The nvcc benchmarks (`benchmarks/correct/float/`), compiled from plain
  CUDA C with nvcc's defaults: `a * x[i] + y[i]` (nvcc contracts it to
  `fma.rn.f32` with the operands in the order `x, a, y`), `x / y`
  (`div.rn.f32`), `sqrtf` (`sqrt.rn.f32`) and `fmaxf(x, 0)`. First run: div,
  sqrt and max proved, axpy `unknown`, because the matcher required the
  spec's operand order; after `ffma_comm`/`fmul_comm`/`fadd_comm` were added,
  all four are proved. `x + y` compiles to `add.f32` with no rounding
  modifier and is `unsupported` (above).

## How it works

```
.ptx --e5r-ptx--> AST --token round trip--> Lean Ptx.Module
spec.json --e5r ptx check--> Proof.lean (template) --lake env lean--> axiom audit --> verdict
                                 \-> interpreter search --> Refute.lean --lake env lean--> verdict

Ptx/Semantics: Memory, Instruction (one thread), SIMT (grid, interleaving)
Ptx/Logic:     Hoare (Safe, wp, loop rule), RaceFreedom (grid_sound), Regions, Launch1D, Refute,
               Phases, PhaseSound (phase_sound), PhaseWp, Cells, Sums, Schedule (replay with barriers)
Ptx/Semantics/FloatCore, Float: rounding core and the float instructions on bit patterns
Ptx/Auto:      Map (the map32 class, proved once), Tactic (ptx_guarded, ptx_stride_*),
               FloatMap (float element functions, NaN congruence, ptx_fvalue),
               Block, Reduce32, Scan32, Accum (the M4 classes, proved once), Tactic4
Ptx/Logic/CellAlgs: the 16 atomic algebras and their laws
Checker:       proofcheck, the supplied-proof checker
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
everything else with a line number: other types (`.u16`, `.f16`), state spaces
(`.local`, `.const`), instructions (integer `neg`, `rem`, `mad.wide`, `ld.global.nc`,
`ld.volatile`, `barrier.sync`, `bar.arrive`, `bar.sync` with another barrier
or a thread count, a predicated `bar.sync`), special registers (`%laneid`),
and forms ptxas rejects or
whose meaning is in doubt: an instruction type PTX does not define for the
opcode (`and.u32`, `add.b32`, `setp.lo.s32`, `cvt` with `.b` types), a
special register outside `mov` and the source of `cvt`, an immediate wider
than its operand, an address offset beyond 32 signed bits, a predicated
`bra.uni`, `-0`. `ld.param` must name a parameter of exactly its type.

The parser is not trusted on its own. `roundtrip` requires the canonical
printing of the parsed module to have exactly the tokens of the source, and
to parse back to the same module. `tests/ptxas_agreement.rs` requires every
form the parser accepts to be accepted by ptxas (618 of 714 generated forms
are accepted by both; 96 only by ptxas). `tests/fuzz.rs` runs token soup,
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
   For the block classes it is `Reduce32.Correct`, `Reduce32.Atomic.Correct`
   or `Scan32.Correct` (with `Pre`, `Block.Args.launch`, `params`, `seg`) and
   the generated `Block.Spec`, printed as `lean_spec`. The `Code` and the
   roles are not trusted. For `accum` it is `Accum.Correct` (with `Args.Pre`,
   `launch`, `params`, `elt`), the algebra definitions of
   `Ptx/Logic/CellAlgs.lean` the spec names (`op` and `e` are part of the
   statement; their laws are proved), `afold`, and the generated
   `Accum.Spec`. For a supplied proof it is the generated `E5rSpec`
   module, and the checker `Checker/ProofCheck.lean` with the Lean kernel's
   `replay`.
   A weak spec proves a weak property, and nothing here detects that.
   Not trusted: the tactics, `wp_sound` and the rest of `Ptx/Logic` and
   `Ptx/Auto` (proved), the counterexample search and the interpreter
   (replayed), the Lean file generator beyond the statement it emits.
2. **The verdict logic.** `e5r ptx check` decides `proved` from Lean's
   exit status, the absence of `error:` and `sorry` in its output, and the
   axiom list of `E5rCheck.correct`. That code (`src/ptx/mod.rs`, `run_lean`
   and `check`) is trusted for the exit status.
3. **The semantics' fidelity to PTX.** Written from the PTX ISA manual and
   differentially tested on the A10G (above). The float definitions
   (`Ptx/Semantics/FloatCore.lean`, `Float.lean`) are part of it; their
   rounding core is cross-checked against lean-ieee754, their bit layer by
   the difftest, and their modelling decisions (the `.ftz` tininess rule,
   refused unrounded `add`/`sub`/`mul`, NaN bits from the oracle, refused
   approximate instructions) are listed under "Floating point". A float
   theorem also trusts that ptxas does not change the result of an
   instruction with an explicit rounding modifier, which the ISA states
   ("treated conservatively by the code optimizer"). Modelling decisions
   that are part of it:
   - `cvta.to.global.u64` is the identity, as it is for global allocations on
     current GPUs;
   - `ld.param` reads the launch's parameter values, `.u32` zero-extended;
   - `ret` and `exit` finish the thread; falling off the end faults;
   - misaligned accesses and accesses outside every allocation fault;
   - unpredicated `bra.uni` behaves like `bra` (predicated `bra.uni` is
     refused);
   - initial registers are arbitrary;
   - a shared address is the register's value, a byte offset in the CTA's
     window; theorems hold for every placement of the shared variables that
     is aligned as declared, inside the 32-bit window and non-overlapping
     (`LayoutOk`), which is all they assume about where ptxas puts them;
   - `bar.sync 0` only, unpredicated (it is `.aligned`); a CTA where one
     thread waits and another has exited is `Diverged`, a fault. The
     hardware lets exited threads count as arrived, so the model rejects
     kernels the GPU runs (stricter, never more permissive);
   - shared memory starts arbitrary in every CTA.
4. **The memory model.** The interleaving semantics is sequentially
   consistent, and PTX's memory model is weaker. `RaceFree` here is strong: no
   two different threads ever make conflicting accesses, so every byte two
   threads share is only read during the kernel. That under the PTX axioms
   (coherence, causality order through program order) such a load returns the
   initial value or the thread's own last store is an argument from NVIDIA's
   model (PTX ISA §8), not a theorem of this development. In M4, conflicting
   accesses are allowed only when they are atomics on one location (morally
   strong) or in different barrier phases of one CTA (ordered by the
   barrier); that this makes the interleaving result the PTX result is the
   same kind of argument, now also relying on `bar.sync` giving the
   ordering PTX §8 states for it. Global atomics with one commutative,
   associative operation per kernel are in the phase theorem; `exch`, `cas`,
   shared-memory atomics and mixed operations are in the model and the
   differential test only, and a kernel relying on them gets no proof.
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

- **M4 beyond two classes.** `reduce32` and `scan32` fix the algorithm: the
  sequential-addressing tree, the Hillis-Steele read/add double barrier, one
  shared array, blocks of up to `max_block` threads, a power of two for the
  reduction. Interleaved addressing, double-buffered scans, warp shuffles,
  multiple shared arrays, accumulators in shared memory (atomics on shared
  memory are in the model, not in the phase theorem), histograms and
  multi-block scans are `unsupported` or `unknown`, unless someone supplies
  a proof.
- **`atom.exch`, `atom.cas`, mixed atomic operations.** Not covered by
  `phase_sound` (see "Atomics: cell algebras" for why and what a rule would
  need). Locks and flag protocols are not verified.
- **Specs need register roles at each barrier.** They are read off the PTX;
  nothing infers them.
- **Proof time.** About 50 s per M4 kernel, and a failing attempt runs to its
  timeout before the search starts.
- **Non-termination is never refuted.** A kernel that loops forever is
  `unknown`, not `refuted`.
- **The M3 class is `map32` only.** One output array of 32-bit elements, one
  element per index, 1-D launches.
- **M5 at the plan's scale.** 115 M3 kernels and 14 M4 kernels from one
  model in one session, no automated generation loop, no Hopper or Blackwell
  hardware.
- **Float error bounds.** The `max_ulps` spec form exists, but the checker
  proves it only where the kernel is bit-exact. A bound against exact real
  arithmetic or a differently rounded computation needs rounding-error
  lemmas on the model (`|roundQ q − q| ≤ ulp/2` and their propagation); the
  main project has none (they exist in lean-ieee754, on Mathlib, which the
  main project does not use). Not built.
- **Float reductions.** Not proved, with or without an error bound: the
  reduction classes are integer (`CellAlg` needs an associative operation,
  and float addition is not), a float tree reduction would need the error
  bound above per phase, and float atomics (`atom.add.f32`) are not in the
  model, their order-dependent rounding being exactly what `phase_sound`'s
  fold cannot express.
- **`.f64` maps.** The model, parser, interpreter and difftest have `.f64`;
  the map class is 32-bit, so no `.f64` kernel is proved.
- **Approximate instructions** are refused (see "Floating point" for why).
- **NaN bits.** By design nothing is proved about them; a kernel whose
  output depends on the bits of a NaN (through `mov.b32` and integer
  operations) cannot be proved.

Not in scope, and not to be described as done:

- SASS, or the translation from PTX to it;
- floating-point formats other than `.f32` and `.f64`;
- the PTX memory model beyond the data-race-free fragment;
- warp-level instructions, tensor cores, texture or surface memory;
- any kernel the theorems or a `check` result do not name.

## Direct concrete-program equivalence demo

[demos/ptx-equivalence](../../demos/ptx-equivalence/README.md) freezes CUDA,
nvcc flags/version and original PTX hashes, then directly edits PTX and proves
universal observable equivalence by nested symbolic execution. The main proof
does not pass through a common algorithm specification. Both sides satisfy
safety, progress, bounded termination, race freedom and existence of a final
run. Complete final global memory agrees for every independent pair of
completed schedules, and bytes outside all output footprints are preserved.

The supplied-proof-only JSON class `equivalence-unpack4` describes the exact
allocation/launch domain of this example. `original_ptx` is resolved relative
to the contract; `original_sha256` must match. The checker exports both kernels
itself with identical parameter signatures, then strictly replays the proof
against `Equivalence.Spec.Equivalent`. The result reports
`direct_observable_equivalence: proved` and `functional_correctness:
not_claimed`, because equivalence alone does not prove an independent operator
specification. Unsupported forms, stale bindings and failed proofs are never
accepted. The original and candidate benchmark show essentially equal speed;
this is a negative optimization result with a completed relational proof.

The [concrete stencil edit](../../demos/ptx-stencil/README.md) extends this
track to different thread ownership and independent original/edited launches.
The `equivalence-stencil17` supplied-proof class checks
`Stencil.Spec.Equivalent`: universal final output-word equality for every pair
of completed interleavings, external-byte preservation, and separate safety,
progress, bounded termination, race freedom and nonvacuous completion. The
accepted scalar rolling edit uses a continuation-parametric symbolic execution
of the frozen original, with no shared operator-spec correctness premise.
Its performance regresses; the paired-store and later coalesced-ownership GPU
experiments do not inherit its proof. See the demo for exact artifact binding,
launch/allocation assumptions and the complete retained timing sweep.

The related `packing` class supports unequal input/output allocation sizes
through `Packing.Spec.Correct`. Only the unpack candidate has accepted replay;
pack/fusion proof drafts remain experimental. See the [packing report](../../demos/verified-packing/README.md).

The only added instruction is immediate `bfi.b32` with position + length <= 32.
All 561 admitted ranges have Lean/Rust/GPU reference checks in the demo;
other forms remain unsupported. Boundary observations and trust limits are
recorded alongside the evidence. The extension does not treat unsupported
instructions as successful execution or strengthen the allowed axiom set.
