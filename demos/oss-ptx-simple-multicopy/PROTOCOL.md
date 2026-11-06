# Predeclared experiment, before candidate edit

Source: frozen complete NVIDIA CUDA Samples TU, commit in freeze.json.
Actual purpose: illustrative copy/compute overlap workload; not a production
hash/compression algorithm. Default N=2^22, inner_reps=5, block512, separate
input/output cudaMalloc. No alternate tuned dispatch exists upstream.

Proof domain: exact frozen PTX, inner_reps=5 (actual upstream default), signed
nonnegative n<2^31, one dimensional covering grid/block with <=2^31 threads,
4-byte-aligned nonwrapping disjoint n-word input/output allocations. Every
initial input/output/global byte and register/predicate/shared value. n=0,
tails, all uint32 bit patterns including wrapping increment are included.
The original PTX supports other repeat counts and aliasing; this demo does
not claim equivalence there. Default launch is tested exactly; ceiling-grid
launches for tails are an explicitly generalized launch adapter.

Shapes (n uint32 words): 0,1,31,32,255,256,511,512,513,4096,65536,
1048576,4194304,16777216,33554432. Time positive shapes. Report every shape,
raw seven-repeat CUDA-event graph samples, median and sample standard deviation.
Preallocate all buffers, warmup, graph batches, randomized/interleaved variant
order, no allocation/JIT/H2D/D2H in kernel timing. Distinguish cache-hot repeated
buffers and rotating buffers exceeding L2 where applicable. GPU exclusive flock
/mnt/scratch/e5r-gpu-benchmark.lock, inspect foreign compute PIDs, no clock changes.

Compare actual frozen OSS original, direct PTX candidate, and matching tuned
CUDA using restrict on otherwise identical kernel body (compiler can remove
repeated stores when alias is excluded). Also run original normal CMake executable
and compare extracted/full-TU kernel symbols. No claim about sample end-to-end
transfer/overlap speedup. Success target: accepted direct universal equivalence
and >=1.10x kernel speedup against original at default n; report honestly if
candidate does not beat tuned CUDA or fails speed target.

Independent NumPy uint32 reference, original/candidate/tuned differential,
edge/random/adversarial/canary/4-byte offset buffers, positive-tail lengths,
hash-rebound semantic proof negatives. Tests supplement the Lean theorem.
NVIDIA CUDA compiler/JIT/SASS/hardware and Rust exporter remain outside theorem.

Follow-up declared before AOT runs: the first experiment used driver JIT for all
three PTX programs. The ordinary upstream executable instead loads its nvcc
ptxas sm_86 cubin. Retain the first dataset as performance-jit.json, and also
measure the exact normal-build cubin plus candidate/tuned cubins assembled with
the same nvcc13.2 ptxas, alongside the JIT variants. This checks whether the
normal upstream compilation path changes the comparison. Same shapes/protocol.
