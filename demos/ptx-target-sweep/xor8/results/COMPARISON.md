# xor8 measured comparison

Exploratory: no accepted proof. Graph medians in microseconds; full event timings and repeat samples in performance.json.

| Size | Original | Direct PTX | Tuned CUDA | Unrolled CUDA | Original/PTX | Tuned/PTX |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 1.371 | 1.265 | 1.278 | nan | 1.084x | 1.011x |
| 4096 | 1.454 | 1.345 | 1.354 | nan | 1.081x | 1.007x |
| 65536 | 2.499 | 2.310 | 2.345 | nan | 1.082x | 1.015x |
| 1048576 | 74.869 | 74.893 | 74.910 | nan | 1.000x | 1.000x |
| 16777216 | 1181.383 | 1182.393 | 1182.390 | nan | 0.999x | 1.000x |
