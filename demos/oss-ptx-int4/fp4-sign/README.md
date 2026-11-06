# FP4 sign insertion: measured negative result

This candidate removes compiler-generated floating-point sign work from the
ordinary bitsandbytes CUDA route. It does **not** establish an accepted
whole-kernel equivalence proof or a useful performance win under the declared
criterion. A matching CUDA bitcast implementation obtains the same instruction
counts and matches or beats the direct edit. No CUDA expressiveness limitation
is claimed.

The upstream is bitsandbytes
[`a616886cacf86701514f0cb1d6be760f967481c0`](https://github.com/bitsandbytes-foundation/bitsandbytes/tree/a616886cacf86701514f0cb1d6be760f967481c0),
MIT, with its license retained in `evidence/source.tar.gz` and
`../bitsandbytes-screen/LICENSE.bitsandbytes`. Implementation source was read;
no reverse-engineering tool implementation was consulted. The earlier screen's
`result.json` freezes the normal dispatch, compiler flags and original hashes.

## Direct edit and controls

`build.py` verifies the upstream source hashes and frozen full-TU PTX hash before
editing. It changes only the three FP4 instances of `kDequantizeBlockwise` in
that PTX. Each has sixteen unrolled sign chains. It leaves the table, scale
multiplication, CUB load/store layout, barriers, tail handling, host dispatch,
and launch geometry intact. This is FP4 codebook decoding, not uniform INT4.

The original computes a 0-or-2 integer, converts to float, subtracts from 1,
multiplies a table magnitude by that sign, then multiplies by scale. The edit
inserts the nibble sign into the exact table bits, then keeps the original
scale multiply. High nibbles use byte bit7; low nibbles use bit3. All eight
magnitudes are nonnegative finite normals or positive zero. The table bits
come from emitted PTX, including `0x3baaaaab` rather than a new decimal rounding.
The edit preserves negative zero in its table/sign intermediate.

The controls are the unchanged full translation unit and a separate full-TU
CUDA build with only `dDequantizeFP4Tree` replaced by `__float_as_uint`, sign-bit
OR, and `__uint_as_float`. See `cuda-bitcast.patch`; flags, algorithm, fusion,
layout, runtime parameters and launch are equal. This is a strong source-level
implementation of the proposed transformation, with no inline PTX required.
The public CUDA dequantization dispatch is the applicable standalone baseline;
fused GEMV/matmul and nested scale decompression are different operations.
Marlin's existing inline-PTX LOP3/half2 path is separately retained in the LLM
screen; it is not a standalone FP4 substitute or a new technique here.

CUDA 13.2.51 targets sm_86. `build.json` records commands, PTX/cubin hashes and
all SASS/resource summaries; `evidence/` contains full original/edited/control
PTX and cubins compressed losslessly, source, assembler logs and disassembly.

| Output | Original SASS | Edited SASS | CUDA bitcast SASS | Registers, all | Spills, all |
| --- | ---: | ---: | ---: | ---: | ---: |
| FP32 | 480 | 424 | 424 | 48 | 0 |
| FP16 | 536 | 480 | 480 | 48 | 0 |
| BF16 | 536 | 480 | 480 | 48 | 0 |

Counts include NOP/control/tail paths. Without NOPs the counts are
470→414, 520→464 and 520→464. Shared bytes remain 4768 for FP32 and 2656 for
FP16/BF16; stack/local bytes remain zero. The edit removes sixteen conversions,
sixteen FP additions and sixteen sign multiplies, adding bit operations.
The complete FP16/BF16 disassembled instruction streams match the CUDA control;
FP32 has the same counts but different scheduling/register assignment.

`v1/` preserves the first direct edit, its artifacts and all measurements.
That version removed 24 static instructions, retained redundant sign extraction,
and was weaker than the CUDA control. Its `build.py` is a historical snapshot,
not a standalone runner from that subdirectory. The current edit removes 56.
No unsuccessful version has been counted as a win.

## Proof status

`TableSign.lean` proves the exact finite-table/sign identity in E5R's existing
binary32 semantics, plus equality of the subsequent modeled scale multiply
for arbitrary scale bits. `byte_sign_masks` checks the old and new sign masks
for every byte. The proof uses Lean 4.35.0 `decide +kernel`, which performs
kernel reduction, with no native evaluation, `bv_decide`, new axioms or
admitted terms. Transitive axiom output contains only `propext`,
`Classical.choice` and `Quot.sound`. `check.py` checks exact artifact hashes,
replays the direct edit, and binds the lemma's table to the frozen PTX bytes.
A wrong bit30 insertion has a kernel-proved semantic counterexample at the
zero table entry; it produces the wrong sign/value bits.

**These are local lemmas, not the requested direct theorem about completed
original and edited kernel executions.** The full-TU exporter rejects `|`
predicate syntax in another entry; unchanged extracted FP4 entries reject
initialized module globals. Both original and edited exact hashes and failures
are in `proof-status.json`. No parser/checker weakening or baseline simplification
was used. No whole-kernel hash-rebound semantic negative passed these admission
barriers. The local semantic counterexample is explicitly narrower.

Remaining obligations include table initialization/global-memory invariants,
all thread/shared-memory/barrier executions, tails, safety, races, termination
and frame preservation, implicit rounding in the emitted FP operations, and
FP16/BF16 conversion support. The scale lemma equates `Option Nat` outcomes:
`none` represents an unspecified NaN, not a fixed NaN payload. Whole-kernel
oracle coupling across changed instruction positions also remains unproved.
GPU bit equality on the tested NaNs does not close that gap.

The proof boundary excludes nvcc, ptxas, driver/JIT, SASS and GPU hardware.
The Rust exporter and its binding to PTX are outside Lean's kernel. This report
claims no verified SASS optimization and no end-to-end inference result.

## Differential validation and timing

Each session uses exclusive `flock /mnt/scratch/e5r-gpu-benchmark.lock`, checks
for foreign compute PIDs before context creation, and changes no clocks.
`driver.py` holds the lock throughout GPU activity.

There are 408 configurations per validation session: three output types, all
eight public block sizes (32 through 4096), and seventeen lengths including
odd/tail cases around 32, 64, 512 and 1024. Packed inputs mix all 256 byte values
with seeded random bytes. Scale patterns cover signed zero, subnormals,
minimum normals, ±1, maximum finite, infinities and quiet/signaling NaNs.
Exceptional or negative scales extend beyond the public quantizer's usual
nonnegative scale output and are raw-kernel adversarial tests.

Every original/edited/CUDA output agrees bitwise; both 64-byte output canaries
survive. Independent NumPy reference results agree on finite bits and signed
zeros, and compare NaNs by class. Session 2 also checks input/scale preservation
and uses a valid one-byte offset packed input. These are execution checks,
not equivalence proofs, memory-sanitizer results, or exhaustive scale tests.
`negative_gpu.py` changes all 48 sign masks to the wrong bit and produces
768 wrong outputs out of 1024 while preserving canaries. Its rebound candidate
hash and artifacts are retained in `gpu-negative.json` and `evidence/`. This
is an execution negative, not a strict whole-kernel proof negative.

Before timing, `measure.py` declares four sizes, all three dtypes, block sizes
64/4096, hot/rotating modes and a success criterion: at least 5% median speedup
at two adjacent representative sizes without material regression, plus direct
proof for an accepted win. Each configuration preallocates buffers, builds
32-launch graphs, warms each five times, and collects 21 CUDA-event samples
per implementation in seeded randomized order. Transfers, allocations, graph
construction and module loading are excluded equally. No end-to-end API or
application integration timing was performed because the kernel candidate
missed these gates.

`measurement-session1.json` is the first tightened-edit session; `measurement.json`
is the repeat with the byte-offset input. Both retain all 48 timing
configurations, sample orders and raw times. `timings.csv` contains medians
from both sessions; raw JSON is authoritative. The first weak edit has its
own 48 configurations in `v1/measurement.json`.

Representative hot-buffer results, block size 64, repeat session:

| Output | Values | Original μs | Edited μs | CUDA bitcast μs | Original/edited |
| --- | ---: | ---: | ---: | ---: | ---: |
| FP32 | 4,096 | 2.112 | 2.112 | 2.048 | 1.000 |
| FP32 | 65,536 | 2.080 | 2.080 | 2.016 | 1.000 |
| FP32 | 1,048,576 | 5.152 | 5.120 | 4.864 | 1.006 |
| FP32 | 16,777,216 | 165.120 | 165.120 | 164.960 | 1.000 |
| FP16 | 4,096 | 2.048 | 2.048 | 2.048 | 1.000 |
| FP16 | 65,536 | 2.048 | 2.048 | 2.048 | 1.000 |
| FP16 | 1,048,576 | 4.768 | 4.544 | 4.544 | 1.049 |
| FP16 | 16,777,216 | 91.744 | 91.519 | 91.584 | 1.002 |
| BF16 | 4,096 | 2.048 | 2.048 | 2.079 | 1.000 |
| BF16 | 65,536 | 2.048 | 2.048 | 2.048 | 1.000 |
| BF16 | 1,048,576 | 4.864 | 4.640 | 4.640 | 1.048 |
| BF16 | 16,777,216 | 91.680 | 91.584 | 91.584 | 1.001 |

The 1M FP16/BF16 gains repeat around 4–5%; small cases approach launch latency
and the largest cases show essentially no improvement. A few individual
configurations approach 5%; no adjacent-size pair meets the criterion.
CUDA bitcasts achieve the same improvement and outperform the direct edit
in FP32's middle-size hot case. There is no broad, source-exclusive, or
statistically established application speedup.

Rotating mode uses 16 output buffers for the first three sizes and four for
the largest. Input/scale buffers remain shared. Small rotating cases still fit
in L2; each row records footprint and slot count rather than labeling all
rotating measurements cold. Hardware is an A10G; driver and observed clocks
are recorded in raw JSON. Clock/thermal drift, event quantization and two
sessions limit conclusions about changes this small.

## Reproduction

From repository root, with the pins/tools described by the preceding screen:

```sh
python3 demos/oss-ptx-int4/fp4-sign/build.py
python3 demos/oss-ptx-int4/fp4-sign/check.py
/mnt/scratch/e5r-oss-ptx/venv/bin/python demos/oss-ptx-int4/fp4-sign/measure.py \
  --input-offset 1 --output /mnt/scratch/e5r-oss-ptx/int4/repeat.json
```

The existing Lean semantic library and E5R release binary are prerequisites;
use the repository's constrained release-only build instructions. Build/check
are CPU-only. Local proof replay uses one Lean thread, a 2 GiB Lean heap
cap, a CPU-time cap, and a private process group cleaned up on timeout. The benchmark acquires its own GPU lock. Set `FP4_SCRATCH` to
place build artifacts elsewhere under scratch. This environment uses NVIDIA
disassemblers from the read-only `/mnt/scratch/e5r-ptx-demo/tools` installation.

Address-space caps of 3 GiB (Lake) and 4 GiB (direct Lean) failed to create
runtime threads; those failures are retained in `evidence/replay-cap*g-failure.log`.
Lean reserves substantially more virtual space than its resident heap. The
final runner uses Lean's own `-M2048` heap limit, one thread and process CPU/wall
time limits, rather than limiting virtual address reservations.
