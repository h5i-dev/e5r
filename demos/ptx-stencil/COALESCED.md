# Coalesced stencil edits: experimental results

All new variants are directly authored PTX. Each needs its own proof;
GPU correspondence and timing are empirical.
All seven predeclared shapes and fixed block sizes are retained;
these tables use graph medians. Raw JSON includes all seven repeats,
variance, host times and ordinary event measurements at block=256.
The original and each matching CUDA comparator are measured again in
each sweep. A ratio above 1 is faster than the frozen original.

## Proof acceptance

scalar2: strictly accepted, 144 declarations; axioms propext, Quot.sound, Classical.choice.

paired2: strictly accepted, 175 declarations; axioms propext, Quot.sound, Classical.choice.

## coalesced sweep

### 128 threads/block

| Output bytes | original us | striped us | staged us | striped_cuda us | staged_cuda us | matching64_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.061 | 1.063 | 1.181 | 1.062 | 1.145 | 1.153 |
| 256 | 1.060 | 1.065 | 1.199 | 1.064 | 1.168 | 1.176 |
| 4096 | 1.120 | 1.707 | 1.433 | 1.695 | 1.382 | 1.351 |
| 65536 | 1.256 | 1.798 | 1.506 | 1.789 | 1.457 | 1.422 |
| 1048576 | 3.644 | 3.718 | 3.556 | 3.706 | 3.334 | 3.174 |
| 16777216 | 69.300 | 73.913 | 77.809 | 73.914 | 69.855 | 74.255 |
| 134217728 | 544.000 | 580.119 | 625.722 | 580.064 | 552.139 | 593.186 |

All-shape geometric mean original/candidate: striped 0.875x, staged 0.881x, striped_cuda 0.877x, staged_cuda 0.936x, matching64_cuda 0.929x.

### 256 threads/block

| Output bytes | original us | striped us | staged us | striped_cuda us | staged_cuda us | matching64_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.058 | 1.060 | 1.182 | 1.060 | 1.172 | 1.149 |
| 256 | 1.056 | 1.062 | 1.196 | 1.061 | 1.193 | 1.171 |
| 4096 | 1.169 | 1.902 | 1.654 | 1.877 | 1.638 | 1.540 |
| 65536 | 1.247 | 1.945 | 1.726 | 1.957 | 1.702 | 1.617 |
| 1048576 | 3.592 | 3.934 | 3.507 | 3.917 | 3.481 | 3.382 |
| 16777216 | 68.631 | 71.166 | 69.917 | 71.176 | 69.829 | 74.201 |
| 134217728 | 538.314 | 556.622 | 556.459 | 556.588 | 551.687 | 593.050 |

All-shape geometric mean original/candidate: striped 0.855x, staged 0.875x, striped_cuda 0.856x, staged_cuda 0.881x, matching64_cuda 0.887x.

### 512 threads/block

| Output bytes | original us | striped us | staged us | striped_cuda us | staged_cuda us | matching64_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.055 | 1.063 | 1.192 | 1.062 | 1.253 | 1.155 |
| 256 | 1.054 | 1.065 | 1.197 | 1.064 | 1.272 | 1.179 |
| 4096 | 1.240 | 1.572 | 1.633 | 1.571 | 1.652 | 1.538 |
| 65536 | 1.309 | 2.331 | 2.217 | 2.330 | 2.232 | 2.082 |
| 1048576 | 3.626 | 3.810 | 3.633 | 3.812 | 3.617 | 3.707 |
| 16777216 | 67.977 | 70.020 | 69.519 | 70.020 | 69.738 | 73.316 |
| 134217728 | 533.031 | 545.859 | 549.467 | 545.807 | 549.840 | 581.742 |

All-shape geometric mean original/candidate: striped 0.875x, staged 0.854x, striped_cuda 0.875x, staged_cuda 0.838x, matching64_cuda 0.859x.

## tiled sweep

### 128 threads/block

| Output bytes | original us | tiled us | tiled4 us | tiled_cuda us | tiled4_cuda us | matching64_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.065 | 1.123 | 1.132 | 1.158 | 1.193 | 1.157 |
| 256 | 1.064 | 1.137 | 1.138 | 1.157 | 1.196 | 1.180 |
| 4096 | 1.121 | 1.342 | 1.623 | 1.362 | 1.648 | 1.352 |
| 65536 | 1.256 | 1.514 | 1.703 | 1.533 | 1.724 | 1.421 |
| 1048576 | 3.643 | 4.152 | 3.890 | 4.191 | 3.959 | 3.274 |
| 16777216 | 69.301 | 67.698 | 69.655 | 67.620 | 69.685 | 74.241 |
| 134217728 | 543.995 | 546.782 | 552.761 | 546.512 | 552.566 | 593.228 |

All-shape geometric mean original/candidate: tiled 0.918x, tiled4 0.881x, tiled_cuda 0.907x, tiled4_cuda 0.862x, matching64_cuda 0.925x.

### 256 threads/block

| Output bytes | original us | tiled us | tiled4 us | tiled_cuda us | tiled4_cuda us | matching64_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.059 | 1.125 | 1.147 | 1.162 | 1.204 | 1.153 |
| 256 | 1.058 | 1.137 | 1.152 | 1.156 | 1.212 | 1.176 |
| 4096 | 1.169 | 1.424 | 1.939 | 1.445 | 1.992 | 1.538 |
| 65536 | 1.246 | 1.495 | 2.010 | 1.513 | 2.070 | 1.622 |
| 1048576 | 3.591 | 4.259 | 4.321 | 4.311 | 4.401 | 3.385 |
| 16777216 | 68.627 | 66.879 | 70.220 | 66.985 | 70.355 | 74.191 |
| 134217728 | 538.305 | 526.185 | 553.413 | 523.705 | 553.392 | 593.032 |

All-shape geometric mean original/candidate: tiled 0.913x, tiled4 0.820x, tiled_cuda 0.902x, tiled4_cuda 0.800x, matching64_cuda 0.886x.

### 512 threads/block

| Output bytes | original us | tiled us | tiled4 us | tiled_cuda us | tiled4_cuda us | matching64_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.056 | 1.149 | 1.226 | 1.183 | 1.249 | 1.158 |
| 256 | 1.058 | 1.153 | 1.234 | 1.167 | 1.256 | 1.181 |
| 4096 | 1.242 | 1.556 | 1.863 | 1.568 | 1.893 | 1.542 |
| 65536 | 1.309 | 1.653 | 2.809 | 1.657 | 2.754 | 2.084 |
| 1048576 | 3.627 | 4.613 | 4.681 | 4.653 | 4.713 | 3.706 |
| 16777216 | 67.979 | 69.278 | 70.908 | 69.533 | 71.030 | 73.324 |
| 134217728 | 533.040 | 540.004 | 551.849 | 541.949 | 551.812 | 581.678 |

All-shape geometric mean original/candidate: tiled 0.879x, tiled4 0.773x, tiled_cuda 0.871x, tiled4_cuda 0.768x, matching64_cuda 0.858x.

## paired2 sweep

### 128 threads/block

| Output bytes | original us | paired2 us | scalar2 us | paired2_cuda us | scalar2_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.062 | 1.083 | 1.062 | 1.093 | 1.087 |
| 256 | 1.072 | 1.101 | 1.078 | 1.109 | 1.105 |
| 4096 | 1.117 | 1.185 | 1.166 | 1.189 | 1.184 |
| 65536 | 1.253 | 1.256 | 1.241 | 1.260 | 1.257 |
| 1048576 | 3.641 | 2.829 | 2.896 | 3.042 | 3.113 |
| 16777216 | 69.300 | 69.772 | 69.800 | 69.934 | 69.979 |
| 134217728 | 543.999 | 548.707 | 549.502 | 549.818 | 551.349 |

All-shape geometric mean original/candidate: paired2 1.019x, scalar2 1.025x, paired2_cuda 1.004x, scalar2_cuda 1.003x.

### 256 threads/block

| Output bytes | original us | paired2 us | scalar2 us | paired2_cuda us | scalar2_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.058 | 1.077 | 1.057 | 1.089 | 1.082 |
| 256 | 1.067 | 1.095 | 1.074 | 1.105 | 1.100 |
| 4096 | 1.166 | 1.233 | 1.221 | 1.236 | 1.232 |
| 65536 | 1.243 | 1.309 | 1.295 | 1.311 | 1.312 |
| 1048576 | 3.591 | 2.940 | 2.900 | 2.976 | 3.013 |
| 16777216 | 68.632 | 69.551 | 69.651 | 69.752 | 69.785 |
| 134217728 | 538.308 | 547.158 | 548.050 | 548.630 | 550.315 |

All-shape geometric mean original/candidate: paired2 1.003x, scalar2 1.013x, paired2_cuda 0.997x, scalar2_cuda 0.996x.

### 512 threads/block

| Output bytes | original us | paired2 us | scalar2 us | paired2_cuda us | scalar2_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.057 | 1.083 | 1.062 | 1.093 | 1.087 |
| 256 | 1.065 | 1.101 | 1.080 | 1.110 | 1.106 |
| 4096 | 1.238 | 1.401 | 1.399 | 1.420 | 1.411 |
| 65536 | 1.306 | 1.467 | 1.460 | 1.494 | 1.481 |
| 1048576 | 3.624 | 2.951 | 3.015 | 3.056 | 3.094 |
| 16777216 | 67.976 | 69.330 | 69.373 | 69.477 | 69.516 |
| 134217728 | 533.037 | 545.269 | 545.790 | 546.642 | 548.956 |

All-shape geometric mean original/candidate: paired2 0.981x, scalar2 0.984x, paired2_cuda 0.969x, scalar2_cuda 0.970x.

## paired2-pointer sweep

### 128 threads/block

| Output bytes | original us | paired2 us | scalar2 us | paired2_cuda us | scalar2_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.065 | 1.086 | 1.062 | 1.091 | 1.083 |
| 256 | 1.063 | 1.106 | 1.085 | 1.110 | 1.105 |
| 4096 | 1.120 | 1.188 | 1.165 | 1.190 | 1.187 |
| 65536 | 1.258 | 1.260 | 1.244 | 1.264 | 1.261 |
| 1048576 | 3.644 | 2.830 | 2.895 | 2.950 | 2.994 |
| 16777216 | 69.302 | 69.792 | 69.801 | 69.921 | 69.919 |
| 134217728 | 544.003 | 548.733 | 549.506 | 549.973 | 551.220 |

All-shape geometric mean original/candidate: paired2 1.017x, scalar2 1.024x, paired2_cuda 1.009x, scalar2_cuda 1.009x.

### 256 threads/block

| Output bytes | original us | paired2 us | scalar2 us | paired2_cuda us | scalar2_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.061 | 1.080 | 1.057 | 1.084 | 1.079 |
| 256 | 1.059 | 1.103 | 1.081 | 1.105 | 1.101 |
| 4096 | 1.171 | 1.236 | 1.222 | 1.243 | 1.243 |
| 65536 | 1.247 | 1.313 | 1.299 | 1.320 | 1.321 |
| 1048576 | 3.593 | 2.935 | 2.891 | 3.075 | 3.097 |
| 16777216 | 68.631 | 69.551 | 69.647 | 69.736 | 69.695 |
| 134217728 | 538.311 | 547.132 | 548.069 | 548.667 | 549.888 |

All-shape geometric mean original/candidate: paired2 1.001x, scalar2 1.012x, paired2_cuda 0.991x, scalar2_cuda 0.991x.

### 512 threads/block

| Output bytes | original us | paired2 us | scalar2 us | paired2_cuda us | scalar2_cuda us |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 1.059 | 1.087 | 1.065 | 1.086 | 1.085 |
| 256 | 1.058 | 1.108 | 1.086 | 1.107 | 1.106 |
| 4096 | 1.243 | 1.400 | 1.403 | 1.435 | 1.426 |
| 65536 | 1.309 | 1.473 | 1.461 | 1.496 | 1.490 |
| 1048576 | 3.625 | 2.954 | 3.015 | 3.069 | 3.058 |
| 16777216 | 67.977 | 69.325 | 69.379 | 69.415 | 69.441 |
| 134217728 | 533.038 | 545.233 | 545.752 | 546.161 | 548.403 |

All-shape geometric mean original/candidate: paired2 0.979x, scalar2 0.983x, paired2_cuda 0.968x, scalar2_cuda 0.970x.

## Transaction profiles

Default profiles use 128 MiB output and block=256. Additional sizes
and blocks are explicit in profile filenames (bytes-bBLOCK).
Separate Nsight invocations, cache control none, clock control none.
The profiled single invocation does not replace repeated timing.

| Profile | Time us | Global load sectors | Global store sectors | Shared store bank conflicts | Shared load bank conflicts |
| --- | ---: | ---: | ---: | ---: | ---: |
| profile-coalesced-matching64 | 594.88 | 85983232 | 8388608 | 0 | 0 |
| profile-coalesced-original | 537.66 | 85819093 | 4194304 | 0 | 0 |
| profile-coalesced-staged | 555.04 | 85983232 | 4194304 | 3145728 | 0 |
| profile-coalesced-staged17 | 550.30 | 85983232 | 4194304 | 3145728 | 0 |
| profile-coalesced-striped | 555.46 | 85983232 | 4194304 | 0 | 0 |
| profile-coalesced-striped17 | 555.36 | 85853213 | 4194304 | 0 | 0 |
| profile-tiled-original | 537.38 | 85819561 | 4194304 | 0 | 0 |
| profile-tiled-tiled | 531.04 | 4456448 | 4194304 | 32880 | 130474 |
| profile-tiled-tiled17 | 523.84 | 4456448 | 4194304 | 33441 | 97468 |
| profile-tiled-tiled4 | 552.70 | 4259840 | 4194304 | 0 | 0 |
| profile-tiled-tiled417 | 552.10 | 4259840 | 4194304 | 0 | 0 |
| profile-paired2-1048576-b128-original | 4.54 | 670105 | 32768 | n/a | n/a |
| profile-paired2-1048576-b128-paired2 | 3.78 | 638976 | 32768 | n/a | n/a |
| profile-paired2-1048576-b128-paired2_cuda | 3.94 | 638976 | 32768 | n/a | n/a |
| profile-paired2-1048576-b128-scalar2 | 3.84 | 638976 | 65536 | n/a | n/a |
| profile-paired2-1048576-b128-scalar2_cuda | 4.16 | 638976 | 65536 | n/a | n/a |
| profile-paired2-original | 539.10 | 85818684 | 4194304 | n/a | n/a |
| profile-paired2-paired2 | 547.65 | 81788892 | 4194304 | n/a | n/a |
| profile-paired2-paired2_cuda | 551.07 | 81788906 | 4194304 | n/a | n/a |
| profile-paired2-scalar2 | 549.06 | 81788928 | 8388608 | n/a | n/a |
| profile-paired2-scalar2_cuda | 550.56 | 81788904 | 8388608 | n/a | n/a |
| profile-pointer2-1048576-b128-original | 4.58 | 670081 | 32768 | n/a | n/a |
| profile-pointer2-1048576-b128-paired2 | 3.78 | 638976 | 32768 | n/a | n/a |
| profile-pointer2-1048576-b128-paired2_pointer_cuda | 3.94 | 638976 | 32768 | n/a | n/a |
| profile-pointer2-1048576-b128-scalar2 | 3.81 | 638976 | 65536 | n/a | n/a |
| profile-pointer2-1048576-b128-scalar2_pointer_cuda | 3.90 | 638976 | 65536 | n/a | n/a |

Striped independent accumulators restore coalesced stores but lose adjacent
rolling reuse. Output staging retains rolling reuse and restores the original
store-sector count, but leaves global-load sectors roughly unchanged and adds
shared bank conflicts. Input tiling instead loads each input tile cooperatively
once, including its 16-word halo, then reuses it through shared memory after a
barrier. One-output and four-output variants are measured separately.
Two-output rolling isolates scalar versus aligned-u64 global stores; its
dynamic alignment check and scalar/tail paths retain four-byte base alignment.
No unsupported shuffle or vector instruction is assumed successful.

The paired2-pointer sweep strengthens the CUDA comparator by hoisting input
and output pointers before the unrolled loads, avoiding repeated u32 index
address arithmetic. The earlier comparison is retained separately. At one MiB
and block=128 the new sweep measures 3.644 us original, 2.830 us PTX and
2.950 us stronger CUDA. Its all-seven-shape geometric means are 1.017x PTX
and 1.009x CUDA versus original. Block=256 is approximately parity; block=512
regresses. Large workloads still regress; the 1.5x target was missed.

At one MiB/block128 the loaded PTX and stronger CUDA each contain 64 SASS
instructions and use 26 registers. Nsight smsp__inst_executed.sum is 196608
versus 217088, with the same global load/store sectors. This is consistent
with a cache-resident instruction-sequence benefit. It does not establish a
general PTX-only advantage or a large-workload bandwidth improvement. The
initial CUDA comparator's 80 loaded instructions and 31 registers are also
preserved. Profiles are empirical; ptxas/JIT translation is outside Lean.

All benchmark/test commands hold the shared GPU flock and check foreign GPU
processes. coalesced-partial-contended.json retains the excluded first attempt,
aborted when a metric query created another GPU context. Handover waits poll
for the previous process's CUDA teardown before starting; foreign-process
checks remain active during every timing repeat. No result from a refused
attempt is included in the tables.
