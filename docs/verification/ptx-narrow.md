# Narrow integer PTX

The executable subset admits `.u8` unsigned loads/stores and 16-bit
`.u16`, `.s16`, `.b16` registers. Bitwise operations and shifts use their
instruction width; comparison interprets the low 16 bits according to the
instruction signedness. Selection and movement keep the low 16 result bits.
Integer conversions truncate or extend according to source signedness.
Eight-bit arithmetic, narrow atomics, signed narrow loads, floating-point
conversions involving 16-bit integers, and signed 16-bit conversion destinations
in wider registers remain refused. Sixteen-bit add/sub/mul also remain outside
this deliberately limited extension.

The public specification is NVIDIA's [PTX ISA 8.8, operand type
checking](https://docs.nvidia.com/cuda/archive/12.9.1/parallel-thread-execution/index.html#type-information-for-instructions-and-operands),
[relaxed type checking for ld/st/cvt](https://docs.nvidia.com/cuda/archive/12.9.1/parallel-thread-execution/index.html#operand-size-exceeding-instruction-type-size),
and [integer conversion](https://docs.nvidia.com/cuda/archive/12.9.1/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-cvt).
These forms allow integer/bit registers wider than an ld/st/cvt instruction
type. Loads zero-extend unsigned values, stores discard excess source bits,
and conversions first interpret the declared source width, then truncate or
extend. Other 16-bit instructions retain exact-width register checks. The
existing 32/64-bit relaxed-width admission remains unchanged.

The Lean representation still stores register values in 64 bits. New
`Width.w8/w16` and `Size.b1/b2` constructors make narrow operations and
byte-addressed accesses explicit. Existing 32/64 branches retain their old
reduction behavior. `Ptx.Logic.Narrow` proves universal normalization,
unsigned-widening, signed-widening/truncation compatibility, read-after-write,
and byte/halfword frame facts. The general memory locality/frame theorems
cover every new size. No native evaluation or bit-vector decision certificates
are used in these proofs.

Run `scripts/check-ptx-narrow.sh` with CUDA, ptxas, Lean, and a release build.
`E5R_VERIFY` and `NARROW_OUT` can select the CLI and persistent output directory.
The generator makes 45 kernels, 953 fixed edge/random inputs each, 42,885 thread
cases in 675 launches. An independent Python implementation computes every
output byte, including canaries. GPU driver JIT, ptxas cubin, Rust interpreter,
and the compiled Lean instruction semantics must all match those bytes.
The GPU runner holds `/mnt/scratch/e5r-gpu-benchmark.lock` and refuses existing
compute PIDs without terminating them. Focused Rust tests additionally cover
misaligned halfword faults, exact write footprints, high discarded bits,
round trips, and refusal boundaries.
