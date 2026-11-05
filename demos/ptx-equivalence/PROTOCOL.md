# Frozen translation-validation experiment

Original: `original.cu`, nvcc 13.2.51, `-O3 -arch=sm_86 --ptx`.
`freeze.json` records original source/PTX hashes before candidate editing.
Original uses a two-stage bit spread. `optimized.ptx` is edited directly
from the frozen PTX, replacing the spread with a masked multiply. No CUDA
candidate generates this PTX. The competent CUDA comparator may express the
multiply too; equality in performance with it is an algorithmic result.

Domain: n is the number of four-byte output words, n divisible by 8,
0 <= n <= G*B <= 2^31; any one-dimensional grid and block in this range.
Input holds n/8 aligned u32 words, output n aligned u32 words. Regions are
allocated, disjoint, and do not wrap 64-bit addresses. All input/global-memory
values and initial registers/predicates/shared-memory values are arbitrary.
Zero length is included. The host uses no launch for zero length.

Observation: the entire final byte-addressed global memory, including bytes
outside the output allocation. Original and candidate schedules are quantified
independently. Require no faults, progress, bounded steps, race freedom and
existence of a completed execution on both sides. Internal registers, shared
memory, traces and step counts need not be identical.

Proof strategy: symbolic execution of original then candidate in a nested
relational postcondition, arithmetic equality of the two concrete store
expressions, and lifting related solo traces via disjoint ownership to all
interleavings. No common operator specification is in the equivalence proof.
Parser/exporter and NVIDIA ptxas/JIT/hardware are outside the Lean theorem.
The supplementary original/CuPy/CPU comparisons do not establish equivalence.

Before measurement, declare output byte sizes
32, 256, 4096, 65536, 1048576, 16777216, 134217728. Compare frozen original PTX,
directly edited candidate PTX and competent matching CUDA multiply kernel.
Each uses 256 threads/block and ceil(n/256) blocks. Preallocate; warm up;
CUDA event timings and 100-launch graph replay, seven repeats with variance,
and host elapsed time. Report every shape, original/candidate ratio and the
geometric mean across all shapes, separately for graph and ordinary launches.
The goal is >=1.5x, not a promised outcome. No size is discarded after timing.
All GPU execution holds /mnt/scratch/e5r-gpu-benchmark.lock exclusively and
refuses foreign compute PIDs before and throughout the run.

The only needed PTX extension is bfi.b32 with immediate position/length in
0..32 with position + length <= 32; other forms remain rejected.
Semantics follow NVIDIA's PTX ISA 9.2
[bit-field insert](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html#integer-arithmetic-instructions-bfi).
Validation compares the Lean definition, Rust interpreter and real GPU with
an independent per-bit insertion loop, including every admitted position/length pair, empty and full-width
insertion. Initial broad probes found mismatches for out-of-range fields,
e.g. a=0,b=0xffffffff,pos=1,len=32 returned 0xffffffff rather than the
documented per-bit result 1. See results/bfi-boundary-observation.json.
Those ranges are refused; no diagnosis of which external layer caused the
discrepancy is claimed. This restriction does not alter either frozen program.
