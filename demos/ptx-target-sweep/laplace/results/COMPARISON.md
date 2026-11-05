# laplace measured comparison

Exploratory: no accepted proof. Graph medians in microseconds; full event timings and repeat samples in performance.json.

| Size | Original | Direct PTX | Tuned CUDA | Unrolled CUDA | Original/PTX | Tuned/PTX |
|---:|---:|---:|---:|---:|---:|---:|
| 32 | 1.272 | 1.394 | 1.394 | nan | 0.913x | 1.000x |
| 128 | 1.671 | 2.214 | 2.211 | nan | 0.755x | 0.999x |
| 512 | 3.374 | 5.438 | 5.406 | nan | 0.620x | 0.994x |
| 1024 | 16.171 | 17.491 | 17.457 | nan | 0.925x | 0.998x |
| 4096 | 68.516 | 67.414 | 67.428 | nan | 1.016x | 1.000x |
| 16384 | 274.083 | 270.368 | 270.361 | nan | 1.014x | 1.000x |
