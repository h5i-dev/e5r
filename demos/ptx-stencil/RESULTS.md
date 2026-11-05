# Stencil measurements

The direct scalar and paired-u64 edits regress over the full sweep. A local
1 MiB paired-store improvement does not establish a broad speedup. Competent
CUDA implementations of the same reuse techniques show similar behavior.
The initial 1.5x engineering target was missed.

These tables report fixed launch configurations separately, with no shape
selection. Raw performance.json retains seven CUDA-event repeats, variance,
host times and ordinary event measurements at block=256. Graph replay uses
100 captured launches, replayed ten times per repeat; buffers and compilation
are outside timing. Output bytes range from 32 to 128 MiB. The GPU is an A10G;
exact versions, hashes, grids and lock metadata are in the raw JSON. Input
traffic logically contains n+16 words; output contains n words. Logical
bandwidth counts each unique input once, not all executed overlapping loads.

Correctness tests and timing are empirical. Accepted strict proof replay
applies only to the exact scalar edited.ptx artifact, not edited64.ptx.
NVIDIA ptxas, driver JIT and hardware are outside the formal proof.

### 128 threads/block, graph replay

| Output bytes | Original us | Scalar PTX us | Paired PTX us | Scalar CUDA us | Paired CUDA us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.065 | 1.143 | 1.147 | 1.113 | 1.157 |
| 256 | 1.064 | 1.166 | 1.170 | 1.136 | 1.180 |
| 4096 | 1.120 | 1.347 | 1.346 | 1.326 | 1.352 |
| 65536 | 1.257 | 1.418 | 1.414 | 1.398 | 1.421 |
| 1048576 | 3.642 | 3.645 | 3.104 | 3.769 | 3.174 |
| 16777216 | 69.299 | 80.070 | 75.001 | 77.808 | 74.241 |
| 134217728 | 544.004 | 646.120 | 601.480 | 626.249 | 593.133 |

All seven shapes, geometric mean original/candidate speedup: edited 0.894x, edited64 0.932x, matching_cuda 0.908x, matching64_cuda 0.929x.

### 256 threads/block, graph replay

| Output bytes | Original us | Scalar PTX us | Paired PTX us | Scalar CUDA us | Paired CUDA us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.060 | 1.138 | 1.142 | 1.106 | 1.152 |
| 256 | 1.058 | 1.161 | 1.166 | 1.127 | 1.171 |
| 4096 | 1.170 | 1.615 | 1.531 | 1.566 | 1.536 |
| 65536 | 1.247 | 1.709 | 1.604 | 1.651 | 1.615 |
| 1048576 | 3.591 | 4.409 | 3.219 | 4.090 | 3.385 |
| 16777216 | 68.628 | 79.261 | 74.829 | 77.275 | 74.173 |
| 134217728 | 538.309 | 640.236 | 600.476 | 622.581 | 593.065 |

All seven shapes, geometric mean original/candidate speedup: edited 0.828x, edited64 0.895x, matching_cuda 0.858x, matching64_cuda 0.888x.

### 512 threads/block, graph replay

| Output bytes | Original us | Scalar PTX us | Paired PTX us | Scalar CUDA us | Paired CUDA us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.059 | 1.140 | 1.147 | 1.114 | 1.158 |
| 256 | 1.058 | 1.167 | 1.170 | 1.136 | 1.180 |
| 4096 | 1.239 | 1.611 | 1.535 | 1.588 | 1.542 |
| 65536 | 1.308 | 2.383 | 2.074 | 2.300 | 2.078 |
| 1048576 | 3.625 | 5.032 | 3.673 | 4.610 | 3.709 |
| 16777216 | 67.977 | 76.671 | 73.427 | 75.742 | 73.330 |
| 134217728 | 533.040 | 607.455 | 583.155 | 597.895 | 581.597 |

All seven shapes, geometric mean original/candidate speedup: edited 0.794x, edited64 0.862x, matching_cuda 0.819x, matching64_cuda 0.859x.

### Large-workload Nsight diagnosis

| Kernel | Profile us | DRAM read MB | DRAM write MB | DRAM sustained % | Occupancy % | Store sectors | Registers/thread |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| profile-edited | 641.15 | 187.13 | 163.00 | 91.09 | 86.65 | 16777216 | 26 |
| profile-edited64 | 600.70 | 166.16 | 156.36 | 89.57 | 83.33 | 8388608 | 26 |
| profile-matching17 | 624.22 | 180.05 | 161.08 | 91.17 | 85.14 | 16777216 | 30 |
| profile-matching64 | 592.38 | 163.64 | 155.51 | 89.87 | 82.25 | 8388608 | 29 |
| profile-original | 540.06 | 147.75 | 152.87 | 92.85 | 83.76 | 4194304 | 34 |

Profiling is a separate single profiled invocation at block=256 and
128 MiB output, with cache control none and clock control none. It is not
a replacement for repeated unprofiled timing. Compared with the original,
the scalar edit reduces executed instructions from 72.35 million to 15.47
million, but four adjacent outputs per thread produce strided warp stores:
store sectors rise from 4.19 million to 16.78 million. Paired-u64 stores reduce
that to 8.39 million. The rolling variants also retain roughly the original
number of load sectors despite fewer load instructions. DRAM traffic rises
from about 301 MB to 350 MB (scalar) or 323 MB (paired). Occupancy remains
above 83% and sustained DRAM throughput is around 90%; this evidence points
to transactions/bandwidth rather than instruction count or occupancy as the
large-workload bottleneck. DRAM bytes include transaction/ECC effects.
Earlier comparator profiles without __restrict__ remain explicitly named
no-restrict; the table and final sweep use the tuned comparators.
