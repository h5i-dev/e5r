# Frozen operator specification and measurement plan

Frozen before candidate implementation or timing, 2026-11-05.

Upstream CuPy **13.6.0**, commit
`25e552d5d679dcdc6f7cc3d81310a9b265463137`,
[cupy/_binary/packing.py](https://github.com/cupy/cupy/blob/25e552d5d679dcdc6f7cc3d81310a9b265463137/cupy/_binary/packing.py).
Inspected the actual implementation as explicitly requested by the task;
this is an operator benchmark, not a reimplementation of a reverse engineering
tool. CuPy is MIT licensed; call the installed package as the OSS baseline.
No upstream implementation is copied into the candidate.

For contiguous flattened uint8 input x of length L, `packbits(x, bitorder='little')`
has length ceil(L/8); output byte j has bit k equal to [8j+k < L and
x[8j+k] != 0], for 0 <= k < 8. Missing tail bits are zero. `unpackbits`
has length 8L; output byte 8j+k is the integer bit k of input byte j.
Big bit order instead maps k to 7-k. These describe observable bytes,
independently of load width, instruction order, and thread assignment.

Initial proof and optimized execution subset: little bit order, axis=None,
contiguous uint8 buffers, L divisible by 4 for unpack, L divisible by 32
for pack. Zero length is included, with no launch in the host wrapper.
Pack predicates are arbitrary nonzero uint8 (not just 0/1). Input/output
allocations do not overlap, both are 4-byte aligned, allocation ends do
not wrap the 64-bit address space. A thread owns one group of 32 unpacked
bytes (one 4-byte packed word); group count n is uint32, launch covers n
with at most 2^31 threads. All other bytes must remain unchanged.
Unsupported bit orders, dtype/axis/strides and partial groups must be
explicitly rejected by the optimized entry point, not silently accepted.
Boundary tests will exercise those rejections. Full API tails are a follow-up,
not a theorem of the initial subset. No candidate benchmark may quietly use
unproved tail code. The proof must quantify over every byte value and valid
allocation/launch in this subset.

Separately identified fusion: uint8 threshold x > 127 followed by little
packbits, same aligned length domain. Exact comparison, no rounding or
clamping. Compare both two-pass CuPy and a matching fused CUDA implementation.
A fusion speedup is reported separately from primitive speedup.

TorchAO follow-up: inspected version **0.14.1**, commit
`d94bb192966a2e8d66d1b8f5d9ef5d393dcfed76`,
[quant_primitives.py](https://github.com/pytorch/ao/blob/d94bb192966a2e8d66d1b8f5d9ef5d393dcfed76/torchao/quantization/quant_primitives.py).
Must identify its actual GPU layout before claiming a compatible transform.
No custom nibble layout may stand in for an upstream operator.

## Predeclared performance sweep

Unpacked byte counts: 32, 256, 4096, 65536, 1048576, 16777216, 134217728.
Unpack consumes one eighth of this number. Pack/fusion consumes this number.
Report every shape, including misses. Primary summary: geometric mean of
baseline/PTX device latency over the four sizes >=65536, separately for
operations and each baseline. Goal >=1.5x, not an acceptance criterion for
truthfully reporting results. Also report minimum/maximum ratios.

256 threads/block initially; changing configuration during tuning is allowed
but must be recorded before final measurements. CUDA events, preallocated
buffers, current stream, warmup, 7 repeats, >=100 launches per repeat (reduce
only when runtime warrants), median and min/max/stddev. Report CUDA graph
replay for small shapes and synchronized host end-to-end latency separately.
Correctness is checked before timing with independent NumPy/reference logic
and pinned CuPy. Baselines: actual CuPy kernel with preallocated output
(and the required zero initialization for pack), competent CUDA warp ballot
pack/fusion and coalesced unpack. OSS public API end-to-end includes its
allocations and is explicitly identified. No host transfers in device timing.

All GPU use in this demo takes an exclusive advisory flock on
`/mnt/scratch/e5r-gpu-benchmark.lock`. Check nvidia-smi before the run and
sample usage; refuse timing if another compute PID is active. The lock only
coordinates cooperating jobs; it does not authorize stopping other jobs.

## Recorded engineering amendment before final measurements

Initial sweep is retained as `results/initial-performance.json` with the exact
PTX in `results/initial-kernels/`. It exposed host enqueue gaps in plain
CUDA-event loops. Final runs therefore add graph replay at **every** size;
primary device summaries use graph replay, with event-loop and host numbers
retained. Raw prevalidated PTX launches are timed to avoid charging Python
argument validation only to the candidate. Candidate validation is separately
tested. CUDA baselines now include both grid-stride ballots/coalesced unpack
(cap 4096 blocks, 256 threads) and a matching grouped CUDA algorithm.

Unpack optimization assigns one output u32 (four uint8 values) per thread,
with eight threads sharing a read-only packed word. The mathematical domain
is unchanged. The PTX `n` parameter now consistently counts output u32 words;
for unpack it is divisible by 8. For pack/fusion input length is 32n bytes;
for unpack it is n/2 bytes, output is 4n bytes. The theorem states these
relationships explicitly. This avoids a serial sequence of eight scattered
stores per thread and reduces thread count fourfold against byte maps.

## Frozen TorchAO follow-up spec (before its implementation/timing)

The pinned quant_primitives.py returns sub-byte values in uint8 containers;
physical packing is a separate operator. Inspected actual
[torchao/dtypes/uintx/bitpacking.py](https://github.com/pytorch/ao/blob/d94bb192966a2e8d66d1b8f5d9ef5d393dcfed76/torchao/dtypes/uintx/bitpacking.py).
Select its real `pack(data, elem_size=4, dim=-1)` on contiguous one-dimensional
uint8 CUDA data. For length L divisible by 8, it returns a one-element tuple
containing L/2 bytes, byte j = (x[j] mod 16) + 16*(x[L/2+j] mod 16).
This is **split-half nibble layout**, not adjacent-nibble packing. All uint8
values are allowed; high nibbles are discarded by upstream masks. Zero length
is included. This exact integer transform has no scales, zero points,
rounding, floating point, or clamping; it packs already quantized containers.

Use map32 with two read-only pointers into the two halves of the same input,
and one disjoint output. Each half and the output has n=L/8 aligned u32
words. The model permits overlapping read-only arrays; here halves are
disjoint. Bound n <= G*B <= 2^31. Exact byte-layout corollary must connect the
word-level spec to the independent mathematical specification above. No
alternative uint4 layout may be substituted.

Follow-up sweep uses the same unpacked byte sizes 32 through 134217728 and
same repeat/event/graph procedure, separately labelled. Compare actual pinned
TorchAO and fused CUDA; report any inability to run torch.compile or a baseline.
