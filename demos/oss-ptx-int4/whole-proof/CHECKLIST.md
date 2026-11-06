# FP4 direct whole-kernel equivalence checklist

Scope starts with the unchanged FP32 entry selected by the pinned public CUDA
FP4 dequantization dispatch. The frozen full-TU original/edited hashes and all
published measurements remain in `../fp4-sign/`. This phase does not introduce a
new optimization or a new speed claim. No whole-kernel proof is accepted yet.

- [x] Exact-entry extraction: copy original and edited entry bytes and all module
  global declarations, verify byte correspondence against the two frozen full
  modules, retain launch/dispatch/provenance. Existing extracted original hash
  `ea210ee92fb2c104abbc9256b5ac3b11c18a643c7e96b4624821e86d29a8ee29` and edited
  `bea226c117624d7c2f33b0a2b0ae6becbface97717fe71cdd4d5175fd87e75ef` remain intact.
- [ ] Initialized globals: structured declarations, exact little-endian bytes,
  zero initialization, bounded/aligned/disjoint module placement, allocated
  symbol resolution, initial memory relation, table preservation.
  Structured load images, initialization/frame/read lemmas and a ready-state
  constructor are implemented. ExactTable now connects the actual module table
  to the checked local sign lemma. Actual reachable write exclusion and binding
  the initialized module to the official whole-entry domain remain open.
- [ ] Full-TU predicate destinations: lexer rejects `|` in unrelated entries.
  Exact-entry extraction is sufficient for FP32; full TU admission is not an
  excuse to erase table declarations or change its entry body.
- [x] Narrow support: preserved uncommitted u8/u16/b16 semantics require focused
  tests; dependency checkpoint includes the missing Map.Role widths repair.
  Rust suite/ptxas oracle, Narrow/Map proofs and timeout regression pass.
- [x] FP32 syntax admission: `%laneid`, `clz.b32`, `min.s32`, multiple register
  declarations in one `.reg` (edited entry), `ld.global.nc.f32`, volatile
  shared ld/st, `bar.warp.sync -1`, `cvt.rn.f32.u16`, implicit-rounding sub/mul.
  Grouped registers, laneid, clz, min, explicit 16-bit FP conversions and
  default-RN instructions are now implemented and differentially tested.
  Both unchanged exact entries now export and their complete ASTs compile.
  NC/warp forms retain distinct constructors; volatile shared accesses remain
  individual memory actions. Syntax admission is separate from execution proof.
- [ ] Implicit rounding/FTZ: preserve original syntax and distinguish default RN
  instruction semantics from explicitly rounded instructions and compiler
  contraction permissions. Reuse exact finite-table and signed-zero lemmas.
- [ ] NaNs: current oracle takes the entire thread state, including PC. Identical
  scale operands do not imply equal oracle results after different-length
  rewrites. Either prove an explicitly stated result-set equivalence with
  oracle transport, or state justified public-API finite-scale conditions and
  prove no oracle use. Do not silently assume matching PCs or payloads.
- [ ] Barriers and actual threads: 64 threads/CTA, two 32-lane warps, three CTA
  barriers and two full-mask warp barriers in the real entry. Existing SIMT
  release and RaceFree track only CTA phases; extending warp synchronization
  needs a faithful progress/race model and regressions. No treating it as nop
  or replacing it with a CTA barrier.
- [ ] Shared state: CUB byte and float transpose buffers, warp-local producer /
  consumer ownership, volatile shared count publication, table-global loads.
  Existing relational equivalent_of_paired requires empty shared declarations;
  existing phase_sound supports CTA phases but cannot erase warp boundaries.
- [ ] Domain: public block sizes 32..4096 powers of two, packed high nibble first,
  output n float elements, grid ceil(n/1024), block(64,1,1), valid raw params,
  nonoverlapping input/output/scales/module storage and all eagerly read scale
  slots allocated even in the last partial CTA. Spell out nonempty host launch,
  integer/address overflow, alignment and host zero-length handling.
- [ ] Tails: arbitrary legal n including odd tails, guarded packed loads,
  padded per-lane scale reads, and predicated stores; preserve arbitrary initial
  registers/predicates/shared bytes and bytes outside outputs.
- [ ] Safety/races/termination/frame: establish no fault for every reachable
  configuration, progress, finite bound for all schedules, race freedom with
  warp ordering, actual completed executions and frame for both programs.
- [ ] Direct relation: concrete original/edited executions, including unchanged
  prefix/suffix and sixteen rewritten sign regions. No pair of abstract decoder
  specifications and no abstract surrogate kernel.
- [ ] Checker: exact hashes, initialized-module/launch preconditions bound into
  official expected theorem; independent kernel replay; only propext,
  Quot.sound and Classical.choice; semantic negative with candidate hash rebound
  must reach a wrong actual operation rather than fail early provenance checks.
- [ ] Regressions: parser rejection/security, Rust/Lean consistency and ptxas
  oracle where relevant; existing accepted simpleMultiCopy and CatBoost
  ZeroSegments checker acceptance; no GPU timing rerun needed.
- [ ] FP16/BF16: follow FP32 with faithful half/bfloat conversion and exceptional
  value semantics; currently Ty and conversion model admit only f32/f64. Exact-byte variant
  inventory first rejects the braced inline-assembly blocks around their
  cvt.rn.f16.f32 / cvt.rn.bf16.f32 instructions.

Compiler/exporter/hardware boundaries remain explicit. Parser admission, local
lemmas and tests are milestones, not whole-kernel acceptance.

Synchronization milestone: `Ptx.Semantics.Warp` and `Ptx.Logic.WarpSchedule`
implement a new, explicitly restricted full-mask/same-PC/full32-member execution
model over the unchanged AST. Warp release advances only its actual warp and
has its own clock; CTA release remains separate. `Total` requires actual
completion, no faults, progress, a finite bound, race freedom, initial snapshot
identity and readonly NC footprints against **all reachable writes**, including
same-thread writes. The NC snapshot/current-read equality is proved from those
footprints. Race-free SC-to-hardware correspondence is still a model assumption;
PTX excludes NC from its formal memory consistency model. No old checker
contract is generalized silently. Old proof/run domains refuse warp/NC.

A kernel-checked 64-thread schedule, same-scope readiness, legal mixed waits,
partial-member refusal, universal release frames and an isolated semantic model
mutation regression pass. GPU JIT/cubin and independent Python agree with actual
Lean Warp execution for 576 threads in four launches. Those are prerequisite
proofs/tests, **not** a certificate about the real FP4 kernel's executions.

Precise next obligations:

1. Prove the unchanged host grid/block dispatch gives one signed-safe loop
   iteration per CTA, including the final tail and all branch paths.
2. Establish compositional warp/CTA phase total correctness for all
   interleavings (checked concrete schedules prove existence only). Prove CUB byte/float shared permutations and scalar publication with actual
   warp/CTA clocks, ownership and bounds, across every interleaving.
3. Derive global write exclusion for initialized globals, input and scale
   allocations from the real instructions. Establish finite values for every
   eager scale read under the explicit public shape/storage domain.
4. Relate actual register/PC states through all 16 sign rewrites and reuse the
   exact table/finite-scale lemmas at the reached operations. Arbitrary NaN
   oracles indexed by differing PCs cannot be assumed coupled.
5. Compose actual runs into safety, races, bounded termination, progress,
   existence, global frame and independently completed observable equivalence.
6. Add the official exact-module/initialized-state FP4 proof statement/domain
   and accepted supplied proof, kernel replay, full axiom audit and rebound
   semantic negative reaching the edited sign operation.
7. Only after the FP32 result, extend conversion/model/proofs to FP16/BF16.
