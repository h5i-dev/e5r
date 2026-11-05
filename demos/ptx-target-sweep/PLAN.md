# Bounded concrete PTX target sweep

Authorization: 2026-11-05 follow-up broadens this worker beyond stencil.
Preserve pushed 2f386ea. Deliver individual directly edited PTX artifacts,
not optimizer/scheduling research. No candidate is compiled from CUDA.

Initial batch: five families, one initial edit each, at most one follow-up
unless results justify selecting that artifact for proof. Screening budget:
approximately 20 minutes engineering per family plus one complete GPU sweep;
proof work is reserved for selected gains. Reject unsupported original PTX
explicitly, with its bytes/error retained; never silently rewrite its semantics.

| Target | Ordinary frozen CUDA | Direct edit | Declared sweep | Domain |
|---|---|---|---|---|
| advance256 | 256 unrolled LCG32 updates | affine jump-ahead | n=256,4096,65536,1048576,16777216 | n uint32, disjoint aligned n-word input/output; complete 1D coverage |
| transpose | contiguous-read naive uint32 transpose | shared 32x32 tile, four rows/thread, padded stride33 | square N=32,128,512,1024,2048,4096 | N positive multiple32, <=32768; full tiles, disjoint aligned arrays |
| laplace | uint32 five-point Laplacian, width1024, halo | shared 32x8 tile plus cooperative perimeter | rows=32,128,512,1024,4096,16384 | rows positive multiple8; input(rows+2)*1026, output rows*1024 |
| xor8 | one XOR checksum per eight-word record | four aligned u64 loads and xor64 reduction, scalar input fallback | same n as advance256 | records n; input8*n, output n; arbitrary four-byte base alignment |
| crc32word | 32 unrolled reflected IEEE polynomial steps | eight four-step linear groups using predicated XOR constants | same n as advance256 | raw transform of one word, polynomial0xEDB88320, no initial/final complement |

All integer arithmetic modulo2^32, except xor8's exact xor64 intermediates.
These are project-authored operators, not a claim of a whole upstream API.
Independent CPU references precede timing. Source/compiler/flags/PTX hashes are
frozen before candidate authoring. Competent matching CUDA uses the same known
technique and is a separately labeled comparator; algorithmic gains are not
marketed as intrinsically PTX-only.

Main statistic: geometric mean original/candidate across ALL listed shapes,
plus every per-shape latency and original/tuned-CUDA ratios. Map block=256;
transpose/laplace block=(32,8), full declared grids. Repeated CUDA events and
100-node CUDA graph replay, seven repeats, warmup, preallocated buffers, no JIT
or allocation in timing. Large shapes exceed L2. Report variance and host time.
All GPU work uses shared exclusive /mnt/scratch/e5r-gpu-benchmark.lock and checks
foreign compute PIDs. Retain every outcome, including failures/regressions.

Promising selected edits must prove universal DIRECT original/edited observable
I/O equivalence, both-side safety/progress/bounded termination/races/nonvacuous
completion, external-memory frame, exact hashes, strict kernel replay and
standard-axiom audit. Unproved exploration is never a verified success.

## Sixth screen, declared after initial batch

advance256 was already optimally folded by nvcc. Test a different useful
fixed PRNG-state advance: 64 steps of 32-bit xorshift (left13,right17,left5).
Original uses ordinary -O3 CUDA; additionally time fully unrolled iterative
CUDA so a loop-unrolling weakness cannot manufacture a win. Direct PTX uses
the known GF(2) jump matrix, concretely encoded as 32 constant conditional-XOR
columns. Tuned CUDA applies the same jump. Same map sweep and full four-byte
aligned disjoint n-word domain. This is one concrete kernel, not a general
optimizer or matrix-synthesis product. If it gains robustly, prioritize its
complete direct proof alongside the promising transpose.
