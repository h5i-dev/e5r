# Measurements

CUDA event times per kernel in microseconds, median ± sample standard deviation over seven randomized-order repeats. Each repeat replays 256 preallocated graph nodes. All predeclared positive shapes are shown; n=0 is tested without timing. Original uses the exact unchanged normal CMake sm_86 cubin; edit and tuned use the same nvcc13.2 ptxas. Driver JIT variants are also retained in the raw dataset. Block512, ceiling-grid for tails. Actual default n=4194304 uses the original normal grid.

| n words | cache regime | original µs | direct edit µs | restrict CUDA µs | original/edit | edit vs tuned |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: |
| 1 | hot | 1.272 ± 0.067 | 1.084 ± 0.059 | 1.084 ± 0.070 | 1.173× | 1.000× |
| 31 | hot | 1.276 ± 0.041 | 1.080 ± 0.048 | 1.084 ± 0.043 | 1.181× | 1.004× |
| 32 | hot | 1.256 ± 0.061 | 1.072 ± 0.065 | 1.072 ± 0.062 | 1.172× | 1.000× |
| 255 | hot | 1.304 ± 0.044 | 1.088 ± 0.042 | 1.092 ± 0.046 | 1.199× | 1.004× |
| 256 | hot | 1.300 ± 0.044 | 1.092 ± 0.058 | 1.092 ± 0.048 | 1.190× | 1.000× |
| 511 | hot | 1.344 ± 0.042 | 1.104 ± 0.046 | 1.108 ± 0.042 | 1.217× | 1.004× |
| 512 | hot | 1.348 ± 0.044 | 1.104 ± 0.046 | 1.104 ± 0.043 | 1.221× | 1.000× |
| 513 | hot | 1.348 ± 0.045 | 1.108 ± 0.049 | 1.104 ± 0.041 | 1.217× | 0.996× |
| 4,096 | hot | 1.388 ± 0.043 | 1.140 ± 0.045 | 1.144 ± 0.042 | 1.218× | 1.004× |
| 65,536 | hot | 1.776 ± 0.096 | 1.320 ± 0.044 | 1.320 ± 0.044 | 1.345× | 1.000× |
| 65,536 | rotating | 2.240 ± 0.040 | 2.408 ± 0.048 | 2.400 ± 0.048 | 0.930× | 0.997× |
| 1,048,576 | hot | 17.572 ± 0.043 | 14.332 ± 0.080 | 14.336 ± 0.050 | 1.226× | 1.000× |
| 1,048,576 | rotating | 17.620 ± 0.047 | 17.852 ± 0.076 | 17.836 ± 0.030 | 0.987× | 0.999× |
| 4,194,304 | hot | 66.472 ± 0.038 | 68.900 ± 0.057 | 68.932 ± 0.038 | 0.965× | 1.000× |
| 4,194,304 | rotating | 66.536 ± 0.049 | 69.312 ± 0.060 | 69.316 ± 0.048 | 0.960× | 1.000× |
| 16,777,216 | hot | 266.048 ± 0.057 | 272.372 ± 0.098 | 272.368 ± 0.069 | 0.977× | 1.000× |
| 16,777,216 | rotating | 265.972 ± 0.045 | 273.360 ± 0.093 | 273.228 ± 0.152 | 0.973× | 1.000× |
| 33,554,432 | hot | 532.060 ± 0.066 | 543.884 ± 0.143 | 543.812 ± 0.204 | 0.978× | 1.000× |
| 33,554,432 | rotating | 532.124 ± 0.069 | 543.872 ± 0.082 | 543.956 ± 0.227 | 0.978× | 1.000× |

**The predeclared default-shape 1.10× success target failed.** Small cache-hot inputs improve, but the default shape and larger streaming inputs regress. The edited PTX closely matches a compiler-produced restrict CUDA implementation. No win over this tuned comparator or sample end-to-end speedup is established.

Hot means repeatedly reused buffers, not guaranteed full L2 residency. Rotating uses the actual ring size and total buffer bytes in performance.json; it exceeds L2 but is a bounded ring rather than an unbounded stream. Graph replay rotates within 64 nodes and repeats that graph. No GPU clocks or power settings were changed.

[Raw measurements](results/performance.json) include every sample, order, launch, ring size, compiler/driver/runtime and PTX hashes. The GPU compute-process list was checked before each sample while holding the common exclusive lock.
