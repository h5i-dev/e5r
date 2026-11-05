# Follow-up optimization protocol

Frozen before further variant measurements, after milestone ccfec80.
Primary domain and original PTX do not change. Output byte sweep remains
32,256,4096,65536,1048576,16777216,134217728; n counts output words and is
multiple of eight. All device buffers have at least 4-byte alignment.
Vector paths must check stronger alignment dynamically and use scalar
fallbacks. Group tails and inactive threads must be guarded explicitly.

First measure original, accepted scalar candidate and matching CUDA against
copy (equal input/output bytes, count traffic twice), write-only and traffic-
matched broadcast read/write. Distinguish logical unique bytes from DRAM
bytes including ECC/transaction overhead. Collect loaded-JIT SASS using ncu,
resource attributes/theoretical and achieved occupancy, cache hits and DRAM
throughput at 1MiB and 128MiB output; profiler cache flushing is explicit.
Offline ptxas resource/SASS diagnostics are labeled separately.

Explore scalar blocks 64/128/256/512/1024; multiple output words/thread
2/4/8; vector stores four/eight/sixteen words/thread with 4-byte-safe scalar
fallback; grid-stride/unrolled variants; supported-by-hardware cache hints
cg/cs/wt. Test candidate and fair CUDA with equal algorithm, traffic and
launch config. Each variant is a directly authored PTX experiment; it is not
accepted merely because GPU tests pass. Unsupported model instructions/cache
hints remain explicit gaps. Winning replacement requires direct universal
concrete-PTX equivalence, strict replay and exact axiom audit before adoption.

All selected variants run all seven shapes; retain regressions. Use graph
replay at every shape, seven repeats, and ordinary events on relevant finalists.
Primary headroom summary: geometric mean across all seven shapes and separately
the four sizes >=65536, with all per-shape latencies and variance. A material
replacement should improve >=10% on the larger-shape geometric mean without
>5% regressions elsewhere; original 1.5x target remains an aspiration.
Any faster unproved configuration is reported as exploratory only, not a
verified result. Optimize geometry for CUDA fairly too; do not market host
launch tuning or fusion as a PTX-specific advantage.

Every GPU activity takes /mnt/scratch/e5r-gpu-benchmark.lock and checks foreign
compute PIDs. Profiling and timing are separate runs; no profiler data is
substituted for ordinary benchmark timing. Retain ccfec80 measurements unchanged.

Subsequent highest-priority scope correction: complete the bounded bandwidth/
geometry/SASS diagnosis above. Broader variant exploration is superseded by
one concrete stencil17 edit using known rolling-window reuse. No optimizer or
new transformation algorithm is in scope. No unproved variant is adopted.
