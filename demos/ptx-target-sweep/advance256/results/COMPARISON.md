# advance256 measured comparison

Exploratory: no accepted proof. Graph medians in microseconds; full event timings and repeat samples in performance.json.

| Size | Original | Direct PTX | Tuned CUDA | Unrolled CUDA | Original/PTX | Tuned/PTX |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 1.027 | 1.027 | 1.027 | nan | 1.000x | 1.000x |
| 4096 | 1.065 | 1.065 | 1.066 | nan | 1.000x | 1.001x |
| 65536 | 1.291 | 1.293 | 1.292 | nan | 0.998x | 0.999x |
| 1048576 | 13.637 | 13.648 | 13.637 | nan | 0.999x | 0.999x |
| 16777216 | 273.160 | 273.175 | 273.137 | nan | 1.000x | 1.000x |
