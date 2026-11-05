# crc32word measured comparison

Exploratory: no accepted proof. Graph medians in microseconds; full event timings and repeat samples in performance.json.

| Size | Original | Direct PTX | Tuned CUDA | Unrolled CUDA | Original/PTX | Tuned/PTX |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 1.414 | 1.168 | 1.189 | nan | 1.210x | 1.018x |
| 4096 | 1.459 | 1.211 | 1.233 | nan | 1.205x | 1.018x |
| 65536 | 2.423 | 1.640 | 1.780 | nan | 1.477x | 1.085x |
| 1048576 | 20.276 | 15.034 | 16.289 | nan | 1.349x | 1.083x |
| 16777216 | 297.362 | 273.263 | 272.920 | nan | 1.088x | 0.999x |
