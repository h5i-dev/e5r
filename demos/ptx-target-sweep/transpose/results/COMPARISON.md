# transpose measured comparison

Exploratory: no accepted proof. Graph medians in microseconds; full event timings and repeat samples in performance.json.

| Size | Original | Direct PTX | Tuned CUDA | Unrolled CUDA | Original/PTX | Tuned/PTX |
|---:|---:|---:|---:|---:|---:|---:|
| 32 | 1.347 | 1.167 | 1.169 | nan | 1.154x | 1.002x |
| 128 | 1.693 | 1.237 | 1.240 | nan | 1.368x | 1.002x |
| 512 | 9.842 | 1.924 | 1.917 | nan | 5.115x | 0.996x |
| 1024 | 35.451 | 13.797 | 13.768 | nan | 2.569x | 0.998x |
| 2048 | 133.984 | 72.121 | 72.062 | nan | 1.858x | 0.999x |
| 4096 | 541.555 | 292.014 | 291.959 | nan | 1.855x | 1.000x |
