# Directly authored packing PTX: preserved specification experiment

The primary complete result here is **unpack**: directly authored PTX,
an independent byte/bit specification, an accepted universal Lean proof of
functional correctness, memory safety, race freedom and termination, and
GPU correspondence/performance measurements. This is complementary to the
[direct CUDA-PTX equivalence demonstration](../ptx-equivalence/README.md),
whose main theorem uses a direct relation between concrete programs.

[Scope and frozen measurement plan](SPEC.md) · [unpack proof](unpack.lean) ·
[accepted replay](results/unpack-proof.json) · [raw measurements](results/performance.json).

## Proof and implementation scope

Little bit order, contiguous uint8, aligned/disjoint nonwrapping allocations.
Unpack requires input length divisible by 4. One thread writes four 0/1 output
bytes; eight threads may read the same input word. n is output words,
n divisible by 8, n <= G*B <= 2^31. The theorem quantifies over all byte values,
initial memory/registers/predicates and valid launches, every interleaving,
with no faults, progress, finite bounded steps, race freedom, existence of a
completed run and preservation of bytes outside output. Empty arrays are
included; the host wrapper skips their launch. This is a subset of CuPy's
API, not support for arbitrary tails, axes, strides, bit orders or dtypes.
The wrapper explicitly rejects unsupported layouts/tails.

`Packing.Spec.bit` states each output bit from the original input memory;
it does not transcribe the candidate arithmetic. `Spec.correct_of` lifts
candidate-specific symbolic execution to the complete grid. Strict replay
accepts only propext, Quot.sound and Classical.choice. Parser/export and
NVIDIA ptxas/JIT/hardware correspondence remain outside the theorem.

**Pack and threshold-fusion are experimental, not verified.** Their GPU tests
and timing rows are retained, including initial tuning results. `pack.lean`
and `threshold.lean` are unfinished development scripts with outstanding
goals. A long-running pack proof was stopped during recovery; no accepted
candidate proof or safety claim is made for either kernel. The generic
packing contract compiling does not constitute a proof of these candidates.

The optional TorchAO split-half INT4 candidate has an accepted map32 **word
expression** proof in results/torchao-proof.json. Its independent byte-layout
corollary and real TorchAO differential/performance tests were not completed.
It is not advertised as a finished TorchAO-compatible demonstration. The
frozen actual operator/layout and exact remaining obligations are in SPEC.md.
Optional Torch 2.9.1+cu128 was installed only in scratch; it is not needed for
the complete unpack or relational demonstration.

## Measurements

CuPy 13.6.0 is the actual pinned OSS baseline. Sources/commits/license and the
independent operator definition are in SPEC.md. All selected shapes are
reported below. Device graph timing is primary, since plain Python enqueue
loops expose launch gaps. Seven repeats, preallocated outputs, matching
streams, CUDA-event synchronization; all samples, variance, min/max,
synchronized host times and public-API allocation-inclusive times are in raw
JSON. The GPU benchmark held the common exclusive flock and sampled foreign
compute PIDs throughout. CuPy pack includes its required output zero fill;
threshold CuPy includes a separate predicate pass. Fusion gains therefore
are reported separately from standalone unpack/pack.

### unpack (proved)

| Unpacked bytes | ptx | cupy_preallocated | cuda_grid_stride | cuda_grouped | cuda_word | CuPy/PTX |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.0148 | 1.0854 | 1.0004 | 1.0609 | 1.0138 | 1.07× |
| 256 | 1.0199 | 1.0957 | 1.0199 | 1.0701 | 1.0209 | 1.07× |
| 4,096 | 1.0803 | 1.1612 | 1.0721 | 1.5032 | 1.0783 | 1.07× |
| 65,536 | 1.1387 | 1.4746 | 1.2257 | 2.4320 | 1.1397 | 1.29× |
| 1,048,576 | 2.0172 | 6.8372 | 4.3817 | 7.1158 | 2.0173 | 3.39× |
| 16,777,216 | 39.6227 | 96.0614 | 66.5774 | 67.5420 | 39.6196 | 2.42× |
| 134,217,728 | 307.8943 | 758.0518 | 524.5031 | 475.8651 | 307.8984 | 2.46× |

Device microseconds, medians. Predeclared summary over the four sizes >=65,536 bytes: cupy_preallocated/PTX **2.26×** (range 1.29–3.39×); cuda_grid_stride/PTX **1.61×** (range 1.08–2.17×); cuda_grouped/PTX **2.11×** (range 1.55–3.53×); cuda_word/PTX **1.00×** (range 1.00–1.00×).

### pack (experimental, unproved)

| Unpacked bytes | ptx | cupy_preallocated | cuda_grid_stride | cuda_grouped | CuPy/PTX |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.1039 | 3.1427 | 1.0486 | 1.0721 | 2.85× |
| 256 | 1.1121 | 3.1058 | 1.0670 | 1.0803 | 2.79× |
| 4,096 | 1.2810 | 3.4468 | 1.1059 | 1.2483 | 2.69× |
| 65,536 | 1.5606 | 2.4873 | 1.2708 | 1.4930 | 1.59× |
| 1,048,576 | 2.1740 | 3.6680 | 4.8179 | 2.1084 | 1.69× |
| 16,777,216 | 38.2444 | 42.7919 | 68.1656 | 38.1870 | 1.12× |
| 134,217,728 | 295.4680 | 353.9661 | 526.3606 | 295.4475 | 1.20× |

Device microseconds, medians. Predeclared summary over the four sizes >=65,536 bytes: cupy_preallocated/PTX **1.38×** (range 1.12–1.69×); cuda_grid_stride/PTX **1.55×** (range 0.81–2.22×); cuda_grouped/PTX **0.98×** (range 0.96–1.00×).

### threshold (experimental, unproved)

| Unpacked bytes | ptx | cupy_preallocated | cuda_grid_stride | cuda_grouped | CuPy/PTX |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.1213 | 4.3008 | 1.0649 | 1.1141 | 3.84× |
| 256 | 1.1233 | 4.3254 | 1.0742 | 1.1151 | 3.85× |
| 4,096 | 1.2769 | 4.6029 | 1.1080 | 1.2698 | 3.60× |
| 65,536 | 1.5677 | 3.9137 | 1.2698 | 1.5268 | 2.50× |
| 1,048,576 | 2.2252 | 10.4868 | 4.8148 | 2.1933 | 4.71× |
| 16,777,216 | 38.2362 | 146.7505 | 67.8216 | 38.2095 | 3.84× |
| 134,217,728 | 295.5284 | 1140.3325 | 526.4241 | 295.4936 | 3.86× |

Device microseconds, medians. Predeclared summary over the four sizes >=65,536 bytes: cupy_preallocated/PTX **3.63×** (range 2.50–4.71×); cuda_grid_stride/PTX **1.53×** (range 0.81–2.16×); cuda_grouped/PTX **0.99×** (range 0.97–1.00×).

Optimized matching CUDA removes much of the apparent advantage. The main
unpack benefit against CuPy is output-word ownership instead of a byte per
thread; it is an algorithm/thread-layout gain, not evidence of an inherently
PTX-only speedup. Pack misses the 1.5× target across the larger sizes.
Threshold fusion benefits against two-pass CuPy are substantial but remain
experimental until a candidate proof is accepted.

## Reproduction

```bash
bash demos/verified-packing/setup.sh
source demos/verified-packing/env.sh
"$E5R_VERIFY" ptx check demos/verified-packing/unpack.ptx \
  --spec demos/verified-packing/unpack.json \
  --proof demos/verified-packing/unpack.lean \
  --keep "$E5R_DEMO_SCRATCH/accepted/unpack" \
  --timeout 600 --memory-mb 4096 \
  --out demos/verified-packing/results/unpack-proof.json
"$E5R_DEMO_SCRATCH/venv/bin/python" demos/verified-packing/test_gpu.py
"$E5R_DEMO_SCRATCH/venv/bin/python" demos/verified-packing/benchmark.py
python3 demos/verified-packing/report.py
```

The benchmark includes experimental pack/fusion rows explicitly labeled
above. `runtime.Packing.run` validates the selected subset, while raw
prevalidated launches are timed for equal Python overhead. The independent
604-case CPU/CuPy comparison includes every byte value, one-hot patterns,
threshold extrema, random data, zero lengths and block boundaries.
GPU tests complement the unpack theorem; they do not prove pack/fusion.

All large state lives under /mnt/scratch/e5r-ptx-demo. Dependencies are pinned
in requirements.txt. Upstream CuPy is MIT; TorchAO is BSD-3-Clause, used only
as a pinned operator reference in this unfinished follow-up. No third-party
implementation is vendored. All candidate PTX is directly authored by author.py;
CUDA baseline.cu is independently written. Initial kernels/results are
retained and have no accepted proof binding.
