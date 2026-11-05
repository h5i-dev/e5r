# Unpack headroom diagnosis after the proved milestone

**Memory-bound at large sizes; edited PTX and matching CUDA have identical
loaded machine instructions**, after removing only absolute branch addresses.
No new faster PTX replacement is claimed. Original ccfec80 proof/timings are
retained unchanged. The subsequent user scope correction selected one concrete
integer-stencil edit rather than a broad variant/optimizer project.

All seven original shapes, blocks 64/128/256/512/1024 for original/edited/tuned
CUDA, and traffic baselines were measured using graph replay, seven repeats,
the shared flock and foreign-compute-PID checks. All measurements and variance
are in [diagnosis.json](results/diagnosis.json); all configurations, including
regressions, are retained. Output buffers are preallocated and functionality
is checked before timing. SASS/resource diagnosis is separate from timing.

## Fixed 256-thread comparison

| Output bytes | Original µs | Edited PTX µs | Matching CUDA µs | Broadcast R/W µs | Copy R/W µs | Write µs | Edited logical GB/s |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.0260 | 1.0220 | 1.0220 | 1.0127 | 1.0086 | 0.8673 | 0.0 |
| 256 | 1.0353 | 1.0312 | 1.0322 | 1.0220 | 1.0199 | 0.8643 | 0.3 |
| 4,096 | 1.0783 | 1.0813 | 1.0824 | 1.0711 | 1.0639 | 0.9164 | 4.3 |
| 65,536 | 1.1428 | 1.1407 | 1.1407 | 1.1305 | 1.1387 | 0.9800 | 64.6 |
| 1,048,576 | 2.0101 | 1.9978 | 1.9968 | 1.9743 | 2.0244 | 1.6773 | 590.5 |
| 16,777,216 | 39.6790 | 39.6390 | 39.6411 | 39.4885 | 69.2204 | 34.2426 | 476.2 |
| 134,217,728 | 307.8083 | 307.5072 | 307.5113 | 308.4472 | 545.2462 | 270.0646 | 491.0 |

Broadcast R/W has the exact traffic pattern x[i/8] -> y[i] with the arithmetic
removed. Logical unpack/broadcast bytes count output plus unique input once
(1.125× output size). Copy reads and writes the full output size (2×);
write-only counts output once. At 128MiB all deliver about 490–497 GB/s on
these definitions: removing unpack arithmetic offers essentially no gain.
At 1MiB, copy logical throughput exceeds DRAM bandwidth because the working
set fits L2; it must not be interpreted as off-chip bandwidth.

## Launch and cache regimes

| Output bytes | Best original block / µs | Best edited block / µs | Best CUDA block / µs | Edited 1024-thread / µs |
| ---: | ---: | ---: | ---: | ---: |
| 32 | 512 / 1.0230 | 512 / 1.0209 | 512 / 1.0199 | 1.0271 |
| 256 | 1024 / 1.0332 | 256 / 1.0312 | 512 / 1.0312 | 1.0342 |
| 4,096 | 512 / 1.0568 | 512 / 1.0629 | 512 / 1.0609 | 1.0844 |
| 65,536 | 512 / 1.1100 | 512 / 1.1080 | 512 / 1.1080 | 1.1284 |
| 1,048,576 | 512 / 1.9517 | 512 / 1.9395 | 512 / 1.9415 | 2.3470 |
| 16,777,216 | 256 / 39.6790 | 256 / 39.6390 | 256 / 39.6411 | 43.7760 |
| 134,217,728 | 256 / 307.8083 | 256 / 307.5072 | 256 / 307.5113 | 340.7636 |

Best-per-shape entries describe the measured sweep, not a held-out optimized
policy. Fair CUDA receives the same sweep and gains the same benefits.
1024-thread launches visibly regress large cases; no result is discarded.
The 1MiB regime fits L2, while 16/128MiB outputs exceed it. Profiling separately
uses explicit cache-control all (cold replay) and none (uncontrolled/warm
replay), unmodified GPU clocks, after ten warmups. Profiler times are diagnostic,
not substitutes for the ordinary seven-repeat benchmark.

| Kernel / output / cache control | DRAM read MB | DRAM write MB | DRAM sustained % | Achieved occupancy % | L2 hit % |
| --- | ---: | ---: | ---: | ---: | ---: |
| matching-1048576-all | 0.147 | 0.166 | 14.78 | 70.95 | 89.34 |
| matching-1048576-none | 0.003 | 0.178 | 11.20 | 61.43 | 102.67 |
| matching-134217728-all | 18.447 | 149.703 | 91.14 | 84.88 | 88.89 |
| matching-134217728-none | 18.482 | 149.637 | 91.42 | 84.99 | 88.86 |
| optimized-1048576-all | 0.146 | 0.153 | 14.43 | 71.69 | 89.81 |
| optimized-1048576-none | 0.003 | 0.169 | 10.91 | 61.56 | 101.50 |
| optimized-134217728-all | 18.410 | 149.842 | 90.94 | 84.79 | 88.90 |
| optimized-134217728-none | 18.457 | 149.756 | 91.25 | 84.85 | 88.85 |
| original-1048576-all | 0.147 | 0.138 | 13.50 | 72.36 | 89.69 |
| original-1048576-none | 0.003 | 0.153 | 9.44 | 63.61 | 101.45 |
| original-134217728-all | 18.458 | 149.682 | 91.53 | 85.06 | 88.90 |
| original-134217728-none | 18.467 | 149.685 | 91.43 | 85.12 | 88.85 |

DRAM metrics include transaction/ECC effects and differ from logical payload.
NVIDIA's [profiling guide](https://docs.nvidia.com/nsight-compute/ProfilingGuide/)
defines these counters. Large-case DRAM utilization around 90% leaves little
credible room for a 1.5× improvement solely by removing arithmetic.

## Actual machine code and occupancy

[Loaded original](results/jit-original.sass), [edited](results/jit-optimized.sass),
[matching CUDA](results/jit-matching.sass) come from Nsight Compute reports for
the actual driver-JIT-loaded kernels. The edited/tuned CUDA instruction lists
are identical after absolute code addresses are normalized. The original's
spread uses four arithmetic instructions after nibble masking; the edit uses
IMAD plus LOP3, two instructions. Removing two instructions did not change the
large-case bottleneck. This is direct evidence against a PTX-specific win here.

CUDA function attributes and offline ptxas report 10 registers, no local/shared
memory or spills. Nsight launch allocation reports 16 registers/thread, with
register allocation allowing 16 blocks but warp capacity limiting a 256-thread
launch to six blocks/SM (48 warps, 1536 threads on sm_86). The difference is
consistent with register-allocation granularity, not evidence of different
loaded instructions. Achieved occupancy is reported above; it is not inferred
from register count. Raw resource/device attributes are in diagnosis.json.

Reproduce from repository root after the existing setup:

```bash
source demos/verified-packing/env.sh
"$E5R_DEMO_SCRATCH/venv/bin/python" demos/ptx-equivalence/diagnose.py
flock /mnt/scratch/e5r-gpu-benchmark.lock bash demos/ptx-equivalence/profile-diagnostics.sh
python3 demos/ptx-equivalence/optimization/report.py
```

NCU 2026.1.0 is required for counters/SASS extraction; unavailable privileges
must be reported as an unavailable check. No privileged driver setting was
changed. NVIDIA disassembly tool downloads are pinned with hashes in
../results/tool-downloads.json, used from scratch and not vendored.

The authorized stronger concrete demo is [stencil17](../../ptx-stencil/DOMAIN.md):
a frozen CUDA-generated program, directly edited using the established rolling
sum reuse technique, with explicit tails and a direct execution relation.
No optimizer, scheduling language or new optimization algorithm is introduced.
