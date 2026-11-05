# Concrete PTX stencil edit with direct equivalence

The agent directly edited frozen nvcc PTX for a 17-tap uint32 stencil.
The accepted [two-output edit](paired2.ptx) keeps rolling-window reuse and
uses aligned u64 stores to cover contiguous warp addresses, with scalar
alignment/tail fallbacks. Lean proves universal observable equivalence to
[the exact original PTX](original.ptx), including safety and termination.
The proof does not pass through a shared algorithm specification.

The gain is local and modest overall: at one MiB output, 1.288x versus the
original and 1.042x versus the stronger matching CUDA comparator. Across all
seven shapes at block=128 the geometric mean is 1.017x versus original
(CUDA: 1.009x). Large workloads still regress. The 1.5x engineering target
was missed. This is not a claim that PTX inherently beats tuned CUDA.

| Output bytes | Original us | Edited PTX us | Tuned CUDA us | Original/PTX |
| ---: | ---: | ---: | ---: | ---: |
| 32 | 1.065 | 1.086 | 1.091 | 0.980x |
| 256 | 1.063 | 1.106 | 1.110 | 0.961x |
| 4096 | 1.120 | 1.188 | 1.190 | 0.943x |
| 65536 | 1.258 | 1.260 | 1.264 | 0.999x |
| 1048576 | 3.644 | 2.830 | 2.950 | 1.288x |
| 16777216 | 69.302 | 69.792 | 69.921 | 0.993x |
| 134217728 | 544.003 | 548.733 | 549.973 | 0.991x |

These are graph-replay medians at fixed block=128, without shape selection.
[COALESCED.md](COALESCED.md) includes every shape, blocks128/256/512, initial
and stronger CUDA comparators, transaction counts and proof acceptance.
[results/paired2-pointer-performance.json](results/paired2-pointer-performance.json)
retains all seven repeats, variance, ordinary event/host timings, hashes and
versions. The larger four-output scalar/u64 edits missed the target and are
preserved in [RESULTS.md](RESULTS.md), without replacing their raw data.

## Proof and exact domain

| Direct relational proof | Replayed declarations | Edited SHA256 prefix |
| --- | ---: | --- |
| four-output scalar | 192 | a79f34aabc16 |
| two-output scalar | 144 | 5de84f86cbfb |
| two-output paired | 175 | 625bd86836e9 |

Each result binds exact original/candidate PTX, contract and proof bytes;
transitive axioms are exactly `propext`, `Quot.sound`, `Classical.choice`.
See [paired proof](results/paired2-proof.json),
[scalar proof](results/scalar2-proof.json), and
[earlier four-output proof](results/proof.json). The full current model audit
checks 5459 Ptx declarations: [model-axioms.txt](results/model-axioms.txt).
The four-output `edited64.ptx` and shared/striped/tiled experiments do not
inherit these proofs.

[DOMAIN.md](DOMAIN.md) states the allocation/launch assumptions. For the
accepted two-output kernels, n is arbitrary uint32 with n<=2^31. Input has
n+16 uint32 words; output has n words; their allocations are disjoint,
four-byte aligned, and do not wrap. Zero and odd lengths are included.
Original and edited launches vary independently: n<=G0*B0 and
ceil(n/2)<=G1*B1, with both thread products<=2^31.

The theorem quantifies over these parameters, arbitrary initial global/shared
memory, register and predicate maps, and every independent pair of completed
schedules. Observations are final output uint32 words plus preservation of
all global bytes outside the output. Each side separately has fault freedom,
progress, a finite step bound, race freedom and an actual completed execution.
The u64 path proves its actual eight-byte alignment test and full-pair bounds;
no eight-byte base-alignment assumption replaces the four-byte domain.

The relational argument executes the concrete edited thread, then each
concrete original output owner. A continuation-parametric symbolic execution
summary of the frozen original supplies its actual store expression; the
postcondition compares final memories directly. The paired-store proof
proves byte-level u64 packing, reads, bounds and footprint composition using
bit extensionality and omega. No native_decide, bv_decide, sorry or new axiom.

## Reproduce

Use the repository Lean4.35.0 toolchain, release Rust, nvcc13.2.51 and an A10G
(sm_86) for the recorded hardware results. Heavy dependencies, caches and
proof outputs live under `/mnt/scratch/e5r-ptx-demo`.

```sh
bash demos/ptx-stencil/run.sh setup
source demos/verified-packing/env.sh
cargo build --release -p e5r-verify
bash demos/ptx-stencil/run.sh paired2-proof
bash demos/ptx-stencil/run.sh scalar2-proof
bash demos/ptx-stencil/run.sh proof       # preserved four-output scalar
bash demos/ptx-stencil/run.sh paired2-negative
bash demos/ptx-stencil/run.sh paired2-pointer test
bash demos/ptx-stencil/run.sh paired2-pointer benchmark
bash demos/ptx-stencil/run.sh paired2-pointer profile 1048576 128
bash demos/ptx-stencil/run.sh paired2 profile
bash demos/ptx-stencil/run.sh coalesced report
```

Other measured variants use `run.sh coalesced|tiled|paired2 test|benchmark|profile`.
Default profiles use128MiB/block256; explicit size/block profiles retain their
own filenames. Proofs can run without Python or a GPU. GPU commands acquire
`/mnt/scratch/e5r-gpu-benchmark.lock` and check foreign compute processes
before and during timing. A handover wait allows previous CUDA context
teardown; it never bypasses contention checks. The excluded first coalesced
attempt, stopped by the contention guard, remains in a separately named JSON.

## Measurements and limits

The original CUDA/PTX, compiler version/flags and hashes were frozen in
[freeze.json](freeze.json) before editing. All candidate PTX was authored or
edited directly, never compiled from changed CUDA. CUDA files are comparators
only: [paired2-pointer.cu](paired2-pointer.cu) hoists pointers to avoid repeated
32-bit index address arithmetic; [paired2.cu](paired2.cu) retains the initial
comparison. Both match the same operator/domain. Sources are project-authored;
shared Python dependency/license pins are in
[the unpack requirements](../ptx-equivalence/requirements.txt).

Tests cover n=0..20, block/tail boundaries, random and adversarial uint32
values and input/output offsets0/4/8/12 bytes, with NumPy convolution as the
independent oracle, input-preservation checks and output canaries. The
coalesced/tiled families each passed10656 cases; each two-output comparator
family passed8880. Tests complement the universal proofs. Semantic negative
controls rebind mutant hashes before proof checking and retain independent
GPU witnesses; see the negative-controls JSON files in results.

Input u32 loads in this two-output edit remain stride-two; the coalescing
improvement is in aligned output stores. Input-tiled variants measure fully
coalesced global input/output but regress across the sweep.

At128MiB/block256 paired stores restore4,194,304 global store sectors versus
8,388,608 for two-output scalar stores. Global load sectors drop from about
85.82M to81.79M. The original already approaches the DRAM bandwidth limit,
which leaves little large-workload headroom. At1MiB/block128 the candidate
and stronger CUDA both use26 registers and have64 loaded SASS instructions;
the executed-instruction metric is196608 versus217088, with equal memory
sector counts. These observations are consistent with a cache-resident
instruction-count benefit, not a general DRAM bandwidth win. Loaded SASS and
profiles are retained; they are empirical evidence.

Lean interprets parsed PTX. Rust parsing/exporting, nvcc compilation of the
original/comparators, NVIDIA ptxas/driver JIT and physical hardware remain
outside the proof. No SASS or CUDA compiler correctness claim is made.
