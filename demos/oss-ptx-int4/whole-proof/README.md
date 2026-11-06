# Whole-kernel proof work, FP32 first

The requested whole-kernel proof is **not accepted**. This directory tracks
prerequisite implementation and proof obligations against the exact original
and edited FP4 entry; it does not replace that target with a small decoder.
The frozen artifacts and negative performance conclusion at `14d8ee2` remain
unchanged. [CHECKLIST.md](CHECKLIST.md) records all obligations.

The original entry hash remains
`ea210ee92fb2c104abbc9256b5ac3b11c18a643c7e96b4624821e86d29a8ee29`,
and edited remains
`bea226c117624d7c2f33b0a2b0ae6becbface97717fe71cdd4d5175fd87e75ef`.
`extract.py` checks each body byte against the frozen full translation unit and
retains all 67 original module-global declarations, including both codebooks
and compiler-generated definitions. It changes no original instruction.
Full-TU unrelated predicate-destination syntax is deferred; exact-entry
extraction was explicitly authorized.

Implemented prerequisites:

- Preserved narrow integer support was validated and checkpointed, including
  correcting missing 8/16-bit `Map.Role.eval` cases. The Rust PTX suite and its
  ptxas acceptance oracle pass. The CLI timeout regression actually runs and
  confirms descendants cannot retain output pipes after timeout.
- Module globals now have structured exact little-endian load images in the
  Rust AST and Lean `Module`, preserving original declaration tokens as well.
  Explicitly sized arrays, scalar literal initializers, and implicit zero data
  are supported. Relocations, partial initializer lists, extern definitions,
  malformed values, duplicate symbols, shared/global name collisions, and
  unsupported sizes remain rejected. Limits are 1 MiB per definition and
  16 MiB per module image. A module symbol address requires a 64-bit `mov`.
- `initialize_globals` validates all placements before writing any bytes:
  missing/unaligned/wrapping/overlapping symbols and aliases with caller
  allocations fail without partially initializing memory. It returns explicit
  allocation regions. Initialization happens at module load, not at each
  launch; normal stores can change global data and must be proved disjoint.
- `Ptx.Semantics.Globals` supplies the actual initializer and `GlobalsReady`
  launch/initial-memory condition. Universal Lean proofs establish initialized
  bytes, existence of the initialized image for every arbitrary caller memory,
  exact 32-bit little-endian reads, the frame outside all definitions, and
  preservation under stores whose footprints exclude the table. The existing
  launch symbol map also places globals; only declared shared names contribute
  to the shared-memory regions. There is no silent table-memory oracle.
- `Ptx.Logic.RelationalPhases` supplies a shared-memory relational contract
  and composes the existing checked per-phase executions into direct final
  memory equality, safety, race freedom, progress, bounded termination, actual
  completed executions and frame. A concrete existing reduction with shared
  memory exercises it. This is CTA-phase infrastructure; it does not erase
  FP4 warp barriers or change any existing checker statement.
- `FiniteScale.lean` imports the existing checked `TableSign.lean`. For finite
  binary32 scales, it proves scale multiplies have a specified result, so
  `fres` does not consult either arbitrary context's state/PC-indexed NaN
  oracle. This explicitly narrows the proposed first theorem's scale domain;
  exceptional scales in the public API are not thereby covered. Whole-kernel
  reachability of the finite-table/scale invariants remains to be proved.
- `Domain.lean` proves eager scale-index coverage with logical tensor storage
  for public block sizes 1024/2048/4096 and arbitrary positive tails. Smaller
  block sizes have coverage for complete 1024-output tiles. It also establishes
  the concrete small-tail coverage failure below. These are address-domain
  lemmas, not kernel execution certificates.

The eager scale load in the unchanged kernel precedes tail predicates. At
`n=1`, block size 32 and thread 2, the emitted arithmetic selects scale index
1 while the quantizer creates a logical scale tensor of length 1. A physical
allocator may provide padding, but that is not a consequence of the logical
public shape. Safety cannot be claimed over only the one-element region.
The first whole-kernel domain must therefore state complete eager-read storage
coverage, rather than silently assuming allocator padding. Public shapes with
large blocks or complete tiles avoid that extra-storage assumption. Inactive
lanes may read otherwise uninitialized padding, so assuming finite padding is
also an additional restriction, not a fact about finite user input.

Remaining hard obligations include proving this entry in the new warp/NC model
(two warp barriers with 64 threads/CTA), volatile shared publication and
cache-qualified scale-read immutability,
whole-thread/phase relations, safety/races/progress/termination/frame, exact
checker statement binding and a rebound whole-kernel semantic negative.
The old relational theorem requires empty shared declarations and cannot be
applied to this kernel. Warp barriers cannot be treated as no-ops or CTA
barriers. FP16/BF16 conversion and their whole-kernel proofs follow FP32.

All new lemmas use ordinary kernel checking and only the permitted standard
axioms; no checker policy was relaxed. Rust/Lean exporter, nvcc/ptxas/driver,
SASS/hardware, and the assumed correspondence of race-free SC executions to
PTX's weaker memory model remain outside the proof kernel boundary.

Validation at this milestone: complete Rust PTX baseline suite (including its
ptxas acceptance oracle), four global-image tests, nine metadata tests, the
new CLI domain gate regression, descendant-timeout regression, and strict
release clippy for both touched crates pass. All 55 imported model/checker
modules were freshly compiled serially; the new shared bridge and concrete
regression were checked as well. Official simpleMultiCopy and CatBoost
ZeroSegments supplied-proof checks both return `proved` with kernel replay.
Those results are regressions, not FP4 acceptance. See `evidence/`.

The legacy checker domains and differential case format reject referenced
module globals until a dedicated initialized-module domain is bound. This
prevents newly admitted global symbols from silently reading default address
zero. Exporting the declarations is supported; proving a kernel still needs
its actual module state contract.

Reproduction from repository root (release binary and pinned Lean toolchain):

```sh
CARGO_TARGET_DIR=/mnt/scratch/e5r-oss-ptx/cargo CARGO_BUILD_JOBS=1 \
  cargo test --release -p e5r-ptx --test globals --test metadata --test narrow
CARGO_TARGET_DIR=/mnt/scratch/e5r-oss-ptx/cargo CARGO_BUILD_JOBS=1 \
  cargo test --release -p e5r-verify --test ptx_cli \
  global_symbols_cannot_escape_the_module_initialization_domain
python3 demos/oss-ptx-int4/whole-proof/build_model.py
python3 demos/oss-ptx-int4/whole-proof/extract.py
```

The build helper uses one direct Lean process at a time, `-j1 -M2048`, CPU
and wall caps, and private process-group cleanup. It checks actual modules,
not a modified checker. A Lake target build stalled on a generated 68-line
kernel and was terminated after its 600-second cap; that log is retained.
Direct source compilation succeeded and the subsequent official checker build
and regressions completed. No GPU measurements were repeated in this phase.

## Instruction milestone

Grouped register declarations, `clz.b32`, `min.s32`, `%laneid`, explicit
16-bit integer/f32/f64 conversions and absent-modifier add/sub/mul are now
implemented in parser, printer, exporter and Rust/Lean execution. The missing
rounding modifier is retained as `fbinDefault`; its per-instruction semantics
is RN, while its compiler contraction permission remains distinct from an
explicit `.rn`. See NVIDIA [PTX ISA 9.2 Table 29](https://docs.nvidia.com/cuda/archive/13.2.2/parallel-thread-execution/index.html#floating-point-instructions).
This is not a theorem about ptxas contraction or final SASS.

`Ptx.Logic.FP4Forms` proves the default-RN execution identity, arbitrary-PC
NaN-oracle independence for narrow integer conversions, the exact clz-derived
shift for all eight public block sizes, and one-dimensional lane numbering.
The actual original and edited entry hashes are still unchanged; both now
reach `ld.global.nc.f32` as the first unsupported operation. Warp, noncoherent
read and volatile-shared support remain separate obligations.

`semantic_regression.py` checks nine forms, each with 64 or 128 threads and
1D/3D geometry: 18 launches, 1,728 thread records. Independent Python results,
Rust, the actual Lean exec/tstep definitions, GPU JIT and ptxas cubin match
all bytes. Each 48-byte output record keeps 44 canary bytes. GPU execution
holds the shared flock and checks foreign compute PIDs. This is an ISA
regression fixture, not an optimization baseline, benchmark, FP4 execution
proof or a rerun of the published FP4 measurements.

The complete Rust PTX suite, strict release clippy, all 14 CLI regressions,
and the official simpleMultiCopy / ZeroSegments supplied-proof checks pass.
All 58 imported model/checker modules compile serially. Explicit `-j1` now
controls both package builds and supplied-proof compilation; the latter also
passes the requested heap cap. These are resource controls only; expected
theorem, kernel replay, import and axiom policies are unchanged. The old
warm-up finished before an attempted stop; no process was killed. Bounded
replays were then run and retained separately.

## Warp and initialized-table milestone

Both exact FP32 entries now export and compile as complete Lean ASTs. Their
bodies, all 67 module globals and published hashes are unchanged.
`compile_entries.py` regenerates those ASTs directly from the frozen entry
bytes. `ExactTable.lean` checks that both global lists are identical, identifies
the actual 32-byte LUT, derives its exact loads from `Module.GlobalsReady`,
proves preservation under actual reachable write exclusion, and connects those
loads to the existing immutable `TableSign.lean`. Reachable write exclusion is
still an obligation of the complete kernel, not an assumed write protection.

`Ptx.Semantics.Warp` adds a separate execution relation over the original AST:
full-mask barriers require 32 actual warp members at the same PC; their release
advances only those members. CTA synchronization is separate. Partially
populated full-mask warps and different-PC same-mask rendezvous are outside this
supported subset, even where hardware can execute them. This is deliberately
stricter than sm86's general barrier behavior. Volatile shared loads/stores
remain individual SC memory actions. See NVIDIA [warp barrier semantics](https://docs.nvidia.com/cuda/archive/13.2.2/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar-warp-sync).

NC loads read an explicit launch snapshot. The new `Total` contract includes
snapshot identity and a **proved** readonly obligation excluding all reachable
global writes/atomics from every NC load footprint, including same-thread
writes. Universal frame and reachability lemmas establish snapshot/current
load equality under that obligation; mutable NC kernels cannot satisfy it.
Hardware correspondence for readonly NC loads remains a stated model boundary:
NVIDIA explicitly [excludes NC from the PTX memory consistency model](https://docs.nvidia.com/cuda/archive/13.2.2/parallel-thread-execution/index.html#scope-and-applicability-of-the-model).
No assumption about coupling different-PC NaN oracles is introduced.

`WarpSchedule` proves that its checked executable schedules are actual grid
executions. `Ptx.Examples.Warp` kernel-checks a completed 64-thread warp/CTA
schedule, confirms that a fast warp at the CTA barrier can coexist with the
other warp at its local barrier, and refuses partial full-mask release. The
isolated `model_mutation.py` replaces warp release by CTA release and reaches
an actual semantic frame-theorem failure. It is a model regression negative;
the required rebound FP4 whole-kernel negative remains outstanding.

`warp_regression.py` compares independent Python, actual Lean Warp.res/action,
GPU JIT and ptxas cubin for four launches (576 threads), 64/128-thread CTAs and
one/two CTAs. It covers volatile warp permutation, CTA scalar publication,
readonly NC f32 loads including NaN payloads, and 36 canary bytes per output
record. All agree. GPU execution holds the shared lock and checks foreign PIDs.
These are semantic tests, not measurements; published timing is unchanged.

`FP32Domain.lean` makes the proposed first scope concrete over the exact real
entries: blocksize 1024, positive `n < 2^31`, block(64,1,1), grid ceil(n/1024),
packed ceil(n/2) input bytes, exactly ceil(n/1024) finite scale values, aligned
float outputs/scales, nonwrapping/disjoint caller/module allocations, valid
shared placement and actual initialized module bytes. Shared bytes and all
registers/predicates are arbitrary. It checks both real entries' parameter ABI,
shared declarations and unused codebook parameter. Its `Obligation` is explicitly
an **unproved target proposition**, not an accepted result. Its preconditions
assume no execution property; finite-scale reachability and eager-load coverage
must still be connected to the actual instructions. Smaller block sizes and
NaN/infinity scales are outside this first scope.

The existing official checker and simple differential runner **refuse** warp
and NC instructions until the initialized-module warp-aware domain is bound.
The new execution contract does not replace any old checker statement. No real
FP4 whole-kernel theorem, official acceptance or qualifying speedup is claimed.
The remaining specific obligations are listed in [CHECKLIST.md](CHECKLIST.md).

Additional reproduction after the serial model build:

```sh
python3 demos/oss-ptx-int4/whole-proof/extract.py
python3 demos/oss-ptx-int4/whole-proof/compile_entries.py
python3 demos/oss-ptx-int4/whole-proof/model_mutation.py
python3 demos/oss-ptx-int4/whole-proof/warp_regression.py
```

Prerequisite replay checks every declaration of the new model/scheduler/regression,
both exact entry ASTs, reused table/finite-scale lemmas, exact table bridge and
proposed domain: 663 declarations across ten modules, standard axioms only.
This uses the unmodified Lean kernel replay API in `ReplayPrerequisites.lean`;
it does not claim the official checker accepted FP4. Compilation uses `-j1
-M2048`; independent replay uses isolated `-j1 -M3072` processes after a retained
2 GiB replay memory-limit failure. CPU/wall caps and private process-group cleanup
remain enabled. Run direct model builds sequentially with Rust aggregate tests
and official checks because those invoke Lake against the same worktree cache.
An initial overlapping build's transient missing-olean failure is retained.

`inventory_variants.py` records precise exact-byte admission: FP32 original and
edited succeed; FP16/BF16 first encounter their real braced inline assembly
blocks containing `cvt.rn.f16.f32` / `cvt.rn.bf16.f32`, whose formats/conversions
are not yet modeled. Full translation units still reject unrelated predicate
destination `|` syntax. These remain explicit gaps; no entry is simplified.

`SharedWarp.lean` adds a separate kernel-checked concrete execution with 64
threads, nonzero fixture register/predicate/shared initialization,
per-warp single-lane volatile publication and every lane reading its warp ID.
The checked scheduler gives actual Reach and completion; the result is also
independently replayed. It validates shared execution infrastructure, not FP4.
The principal remaining infrastructure gap is a compositional total-correctness
rule for warp/CTA phases under all interleavings. Existing CTA `phase_sound`
cannot be applied to these warp barriers; concrete schedules prove existence
only. The exact FP4 phase invariants, read/write footprints, stuttering relation
and official initialized-module contract must then be supplied.

New exact PTX/AST evidence is derived from the pinned bitsandbytes source under
[its MIT license](../bitsandbytes-screen/LICENSE.bitsandbytes); the unchanged
upstream/build/dispatch provenance remains in the frozen screen/sign reports.
The table-load cut-point lemmas refer to the actual exported load statements
(original PC203, edited PC202), prove allocation/alignment from module readiness,
and execute `Warp.res` into the actual `%f22` register. Reaching those cut points
with the required address invariant remains open; these rules do not establish
whole-entry reachability, safety or equivalence.

Final validation of this milestone: complete release PTX suite including ptxas
oracle, strict all-target clippy for both crates, 15 CLI regressions, 61 direct
model/checker modules, library-wide audit of 6,180 declarations, 663 independently
replayed prerequisite declarations and official simpleMultiCopy/ZeroSegments
acceptance all pass. [Evidence summary](evidence/warp-milestone.json) and
[artifact hashes](evidence/warp-artifacts.json) retain raw semantic test outputs
and both resolved resource failures. FP4 whole-kernel acceptance remains false.
