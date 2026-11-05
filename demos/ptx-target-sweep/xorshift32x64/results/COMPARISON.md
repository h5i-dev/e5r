# xorshift32x64 measured comparison

Exploratory: no accepted proof. Graph medians in microseconds; full event timings and repeat samples in performance.json.

| Size | Original | Direct PTX | Tuned CUDA | Unrolled CUDA | Original/PTX | Tuned/PTX |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 2.076 | 1.157 | 1.139 | 2.077 | 1.794x | 0.984x |
| 4096 | 2.114 | 1.195 | 1.178 | 2.115 | 1.769x | 0.985x |
| 65536 | 3.907 | 1.758 | 1.575 | 3.908 | 2.222x | 0.896x |
| 1048576 | 34.268 | 15.860 | 14.637 | 34.276 | 2.161x | 0.923x |
| 16777216 | 529.857 | 272.952 | 273.084 | 530.167 | 1.941x | 1.000x |
