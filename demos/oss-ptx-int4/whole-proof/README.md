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

Remaining hard obligations include actual `bar.warp.sync -1` semantics (two
warp barriers with 64 threads/CTA), volatile shared publication, cache-qualified
scale reads and their immutability condition, `%laneid`, `clz.b32`, `min.s32`,
grouped register declarations, default FP rounding, narrow FP conversions,
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
