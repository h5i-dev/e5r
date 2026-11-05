# Direct PTX stencil edits with universal equivalence

The agent froze ordinary CUDA -> nvcc PTX, then directly edited that concrete
17-tap uint32 stencil. The final [wide-branch.ptx](wide-branch.ptx) computes
two outputs per thread, reuses the rolling sum, and uses coalesced u64 input
loads and output stores on its checked aligned full-pair path. Scalar paths
retain arbitrary four-byte input/output alignment and odd tails.

Lean proves direct universal observable equivalence to the exact frozen
[original.ptx](original.ptx), including safety, termination and preservation
of external memory. The proof does not pass through two shared-spec proofs.
Strict kernel replay accepts 204 declarations, using only `propext`,
`Quot.sound`, `Classical.choice`: [proof result](results/wide-branch-proof.json).

The measured gain is **1.71x at one MiB with a hot buffer**, versus 1.04x
against competent CUDA using the same wide-load technique. Across all seven
predeclared shapes the geometric mean is **1.068x** at block128. Other measured
launch configurations give 1.064x at block256 and 1.041x at block512. The full-
sweep 1.5x target was missed; large workloads still regress. A separate
16-buffer rotating diagnostic gives about 1.08x at one MiB. The hot-buffer
result is not a general cold-cache or streaming guarantee.

| Output bytes | Original us | Earlier paired PTX us | Final PTX us | Wide CUDA us | Original/final |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.062 | 1.082 | 1.086 | 1.095 | 0.977x |
| 256 | 1.072 | 1.101 | 1.093 | 1.103 | 0.981x |
| 4096 | 1.117 | 1.185 | 1.159 | 1.167 | 0.964x |
| 65536 | 1.254 | 1.256 | 1.226 | 1.233 | 1.023x |
| 1048576 | 3.640 | 2.830 | 2.124 | 2.203 | 1.714x |
| 16777216 | 69.299 | 69.780 | 69.906 | 69.942 | 0.991x |
| 134217728 | 544.002 | 548.743 | 550.688 | 551.064 | 0.988x |

This table uses fixed block128 for every kernel and shape, selected among the
three predeclared block configurations. [COALESCED.md](COALESCED.md) retains
every configuration, shape, comparator and negative result. Raw
[wide-branch-performance.json](results/wide-branch-performance.json) includes
all seven repeats, variance, ordinary CUDA-event/host timings, launch geometry,
versions and exact hashes. The matching CUDA is close: this demonstrates a
concrete PTX edit and proof, without claiming an intrinsically PTX-only algorithm.

## Accepted proofs and domain

| Direct relational proof | Replayed declarations | Edited SHA256 prefix |
| --- | ---: | --- |
| wide input/output | 204 | afd811056b3c |
| paired output | 175 | 625bd86836e9 |
| two-output scalar | 144 | 5de84f86cbfb |
| four-output scalar | 192 | a79f34aabc16 |

The final proof, [paired2 proof](results/paired2-proof.json),
[scalar2 proof](results/scalar2-proof.json), and preserved
[four-output proof](results/proof.json) each bind exact PTX/contract/proof bytes.
The model audit checks 5459 Ptx declarations:
[model-axioms.txt](results/model-axioms.txt). Other exploratory PTX files do
not inherit these accepted proofs.

[DOMAIN.md](DOMAIN.md) states the allocation and launch assumptions. For the
accepted two-output kernels, n is arbitrary uint32 with n <= 2^31. Input has
n+16 uint32 words and output has n words, with disjoint nonwrapping allocations
and four-byte-aligned bases. Zero and odd lengths are included. Original and
edited one-dimensional launches vary independently: n <= G0*B0 and
ceil(n/2) <= G1*B1; both thread products are <= 2^31.

The theorem quantifies over these parameters, arbitrary initial global/shared
memory, register and predicate maps, and every independent pair of completed
schedules. Observations are final output uint32 words and preservation of
all global bytes outside the output. Each side separately has fault freedom,
progress, bounded steps, race freedom and an actual completed execution.
Wide input loads require both the actual input alignment test and a complete
pair, so the last high word is inside the input allocation. Output u64 stores
have a separate checked alignment condition. Scalar paths cover the remaining
cases. No eight-byte base-alignment or divisibility assumption was substituted.

The relational proof executes each concrete edited thread, then the concrete
original owners of its outputs. A continuation-parametric symbolic execution
summary of the frozen original gives its actual store expression; postconditions
compare final memories directly. Input b8 accesses are proved to cover two
valid input words. Bitwise lemmas prove u64 reads/packing and actual alignment;
all use bit extensionality/omega and existing semantics. No sorry, new axiom,
native_decide or bv_decide is used.

## Reproduce

Recorded hardware: A10G, sm_86. Lean4.35.0 and nvcc13.2.51 are pinned for the
proof/compiler artifacts. Heavy state lives under `/mnt/scratch/e5r-ptx-demo`.

```sh
bash demos/ptx-stencil/run.sh setup
source demos/verified-packing/env.sh
cargo build --release -p e5r-verify
bash demos/ptx-stencil/run.sh wide-branch-proof
bash demos/ptx-stencil/run.sh wide-branch-negative
bash demos/ptx-stencil/run.sh wide-branch test
bash demos/ptx-stencil/run.sh wide-branch benchmark
bash demos/ptx-stencil/run.sh wide-branch profile 1048576 128
bash demos/ptx-stencil/run.sh wide-branch profile
"$E5R_DEMO_SCRATCH/venv/bin/python" demos/ptx-stencil/cache-regimes.py
bash demos/ptx-stencil/run.sh wide-branch report
```

Preserved proofs use `paired2-proof`, `scalar2-proof`, and `proof` (four-output
scalar). Other measured families use `coalesced|tiled|paired2|paired2-pointer|wide-input`
with `test|benchmark|profile|report`. Default profiles use 128 MiB output and
block256; explicit sizes/blocks get separate filenames. Proofs need no Python
or GPU. Public GPU commands acquire `/mnt/scratch/e5r-gpu-benchmark.lock` and
check foreign compute processes before and during timing. Handover polling
waits for prior CUDA teardown and never bypasses checks. One excluded first
coalesced attempt stopped by the contention guard is retained separately.

## Evidence and limits

The original CUDA/PTX, exact nvcc command/version and hashes were frozen in
[freeze.json](freeze.json) before editing. Candidates are directly authored or
edited PTX; no changed CUDA generated them. CUDA files are comparators only.
The final [wide-input.cu](wide-input.cu) implements the same checked u64
input/output paths. [paired2-pointer.cu](paired2-pointer.cu) strengthens the
initial comparator by hoisting pointers before unrolled loads. All earlier
comparisons and regressions remain separate. Sources are project-authored;
Python dependency/license pins are shared with
[the unpack requirements](../ptx-equivalence/requirements.txt).

The final family passed 42,624 GPU/NumPy cases, including n=0..20, block/tail
boundaries, adversarial/random uint32 values, all 16 independent input/output
offset combinations 0/4/8/12 bytes, input-preservation checks and output
canaries. These complement the universal proof. Semantic negative controls
rebind mutant hashes and retain independent GPU witnesses; the odd-tail
witness uses n=7. Proof rejection is not presented as a checked Lean refutation.

At 128 MiB/block256, input load sectors fall from about 81.79M (earlier paired
edit) to 40.89M, and stores remain 4,194,304 sectors. DRAM traffic remains about
301 MB; the final kernel is around 551 us versus 540 us original in the separate
profile. Reduced L1 transactions cannot halve that DRAM traffic. At one MiB,
the first wide-load edit reduced sectors but ptxas if-converted its fallback
loads, issuing predicated-off scalar slots. Computing sums inside each branch
reduces the executed-instruction metric from 266240 to 184320, with the same
319488 input sectors, and improves 3.085 us to 2.124 us. Loaded SASS and raw
profiles are retained. This is empirical compiler/hardware evidence.

The cache diagnostic was declared after observing the local gain. One hot
buffer gives 3.642 us original versus 2.125 us final. Sixteen rotating pairs
(about 32 MiB, exceeding L2) give 5.667 us versus 5.264 us; this is not a forced
cold-cache guarantee. Warmup, allocations, JIT and reference computation are
outside timing; buffers and functionality match across candidates/comparators.

Lean interprets parsed PTX. Rust parsing/exporting, nvcc compilation of the
original/comparators, NVIDIA ptxas/driver JIT and hardware are outside the
proof. No SASS or CUDA compiler correctness claim is made.
