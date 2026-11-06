# CatBoost exploratory direct PTX batch

Five distinct real CatBoost kernels have frozen original builds, direct PTX
edits, independent GPU differential tests and fair original/edit/tuned AOT
measurements. These are **exploratory optimization attempts, not completed production
optimization+proof attempts or accepted wins**. No universal proof is accepted.

Pinned CatBoost5686f8c6cc9def4b0df343488d2f887ec5609d1f, Apache-2.0
(full license LICENSE.catboost). Each subdirectory records exact source identity,
normal callsite/dispatch, unchanged upstream full source, extracted unmodified
kernel body and build-only adaptation in freeze.json. No baseline CUDA body was
edited. Original emitted PTX was frozen before author-edit.py generated direct
text edits. tuned.cu/ptx are separate competent CUDA comparators, not candidates.

| Kernel | Concrete edit | Result |
| --- | --- | --- |
| ZeroPartitions | Guarded64-bit zero store with4-byte-aligned fallback; covering-launch loop removal | Near parity, approximately1.02x in some large cases |
| ReverseImpl<ui32> | Remove grid-stride backedge for ordinary uncapped covering dispatch | Near parity |
| ZeroSegmentStartsImpl<ui32> | Reuse input byte offset for conditional output store | Near parity |
| FillQueryEndMaskImpl | Load next doc using current doc address+4 | Near parity |
| ComputeGroupIdsImpl<128> | Early invalid-query return, reuse query byte offset | Often regresses, particularly small workloads |

No significant speedup threshold was predeclared before these exploratory
measurements, so no performance-target success is claimed. Actual explicit
launch/alignment/alias/index domains are in edit.json; loop removals require
covering launches. No claimed reduction in compulsory unique DRAM traffic.

Each kernel passed234 tests (1170 total) across original/edit/tuned, independent
NumPy reference, edge/tail sizes0 through65537, zero/all-one/random patterns,
canaries, input preservation, and buffers offset by1 or4 uint32 words. Timing
uses preallocated buffers, shared exclusive GPU flock, foreign-process check,
20 warmups,32-node CUDA graphs,4 replays,7 repeats and randomized variant order.
All60 shape/regime rows and raw latency samples remain in */gpu.json. Large
simple-array shapes include8-buffer rotation. Identical PTXAS -O3 sm86 applies
to original/edit/tuned. Measurements cover extracted kernels only, not API cost.
GPU tests and exporter success do not constitute formal proof.

Normal full CatBoost TU/API runtime equivalence remains unvalidated. Source
extraction adapts project host includes/typedefs/instantiation only. Prior scratch
screen established byte-identical entry code with/without unused CUB includes.
A full transform TU build attempt currently fails because the existing sparse
checkout lacks util/generic/fwd.h; this is a local dependency gap, not an external
blocker. It must be resolved before claiming a completed normal-OSS baseline.

Reproduction, after installing the prior demo's pinned environment and fetching
the recorded CatBoost checkout in scratch:

```
python3 demos/oss-ptx-catboost/freeze.py
python3 demos/oss-ptx-catboost/author-edit.py
python3 demos/oss-ptx-catboost/tuned.py
source demos/oss-ptx-simple-multicopy/env.sh
/mnt/scratch/e5r-oss-ptx/venv/bin/python demos/oss-ptx-catboost/gpu.py
python3 demos/oss-ptx-catboost/report.py
```

ledger-rows.json supplies explicit machine-readable phases and exact PTX hashes.
NVIDIA compiler/JIT/SASS/hardware correspondence remains outside Lean's boundary.

ZeroSegments now has a strict accepted direct universal equivalence proof:
`zero_segments/proof-attempt.json`,60 independently replayed declarations,
only propext/Quot.sound/Classical.choice. The theorem quantifies arbitrary
initial memory/registers/predicates and arbitrary32bit flag mask, aligned
nonwrapping disjoint input/output arrays, n<2^31 and a covering1D launch with
at most2^31 launched threads. Zero/tails, mask-false unchanged output bytes,
both-side safety/race freedom/progress/bounded termination/completed execution,
entire final global memory equality and frame preservation are included.
The exact source PTX is related directly to the exact edited PTX; no common
operator spec substitutes for this relation. `zero_segments/negative.py` changes
the stored zero to one and rebinds the candidate proof hash; `negative.json`
records rejection on actual semantic obligations, rather than a stale hash.
Other four kernels remain unproved. ZeroSegments has no meaningful performance
win; normal full CatBoost TU/API baseline validation is still open. Thus this
accepted theorem is a proof milestone on the exact extracted original, not a
completed production optimization result. NVIDIA compilation/JIT/hardware and
Rust export remain outside the Lean proof boundary.

```sh
source demos/oss-ptx-simple-multicopy/env.sh
"$CARGO_TARGET_DIR/release/e5r" ptx check demos/oss-ptx-catboost/zero_segments/edited.ptx --spec demos/oss-ptx-catboost/zero_segments/equivalence.json --proof demos/oss-ptx-catboost/zero_segments/equivalence.lean --out "$E5R_OSS_SCRATCH/zero-proof.json" --timeout 600 --memory-mb 3072 --no-search
"$E5R_OSS_SCRATCH/venv/bin/python" demos/oss-ptx-catboost/zero_segments/negative.py
```
