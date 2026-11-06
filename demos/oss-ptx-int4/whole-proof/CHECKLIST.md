# FP4 direct whole-kernel equivalence checklist

Scope starts with the unchanged FP32 entry selected by the pinned public CUDA
FP4 dequantization dispatch. The frozen full-TU original/edited hashes and all
published measurements remain in `../fp4-sign/`. This phase does not introduce a
new optimization or a new speed claim. No whole-kernel proof is accepted yet.

- [ ] Exact-entry extraction: copy original and edited entry bytes and all module
  global declarations, verify byte correspondence against the two frozen full
  modules, retain launch/dispatch/provenance. Existing extracted original hash
  `ea210ee92fb2c104abbc9256b5ac3b11c18a643c7e96b4624821e86d29a8ee29` and edited
  `bea226c117624d7c2f33b0a2b0ae6becbface97717fe71cdd4d5175fd87e75ef` remain intact.
- [ ] Initialized globals: structured declarations, exact little-endian bytes,
  zero initialization, bounded/aligned/disjoint module placement, allocated
  symbol resolution, initial memory relation, table preservation. Current
  initial parser retained only unreferenced scalar globals as opaque metadata.
  Structured load images, initialization/frame/read lemmas and a ready-state
  constructor are now implemented; binding them to the complete target remains.
- [ ] Full-TU predicate destinations: lexer rejects `|` in unrelated entries.
  Exact-entry extraction is sufficient for FP32; full TU admission is not an
  excuse to erase table declarations or change its entry body.
- [x] Narrow support: preserved uncommitted u8/u16/b16 semantics require focused
  tests; dependency checkpoint includes the missing Map.Role widths repair.
  Rust suite/ptxas oracle, Narrow/Map proofs and timeout regression pass.
- [ ] Remaining FP32 forms: `%laneid`, `clz.b32`, `min.s32`, multiple register
  declarations in one `.reg` (edited entry), `ld.global.nc.f32`, volatile
  shared ld/st, `bar.warp.sync -1`, `cvt.rn.f32.u16`, implicit-rounding sub/mul.
  Grouped registers, laneid, clz, min, explicit 16-bit FP conversions and
  default-RN instructions are now implemented and differentially tested.
  Both exact entries reach nc loads next. Volatile and warp semantics remain.
  Inventory is checked against real parser errors, not source rewriting.
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
  value semantics; currently Ty and conversion model admit only f32/f64.

Compiler/exporter/hardware boundaries remain explicit. Parser admission, local
lemmas and tests are milestones, not whole-kernel acceptance.
