# Target screening and selection

Read-only source investigation by this worker and its delegated reviewer:

| OSS | pinned identity / source | normal implementation and use | decision |
| --- | --- | --- | --- |
| CuPy | v14.0.1, `3df3b7e4695029652fec511b71351736bae97389`, MIT, `cupy/_binary/packing.py:7,67` | Actual packbits/unpackbits ElementwiseKernel dispatch at64/105. Byte loads/stores, generated CArray/indexer structs and64-bit grid-stride loop. | Source screen only, no claimed parser/GPU result. Practical operation but a substantially larger first proof. |
| CatBoost | `5686f8c6cc9def4b0df343488d2f887ec5609d1f`, Apache-2.0, `catboost/cuda/cuda_util/kernel/fill.cu:37`, `transform.cu:15`, `segmented_scan.cu:11` | Real MakeSequence/AddVector/ZeroSegmentStarts integer specializations, usual512/512/256 thread dispatch. `WriteThrough` is CUB STORE_WT; AddVector also uses __ldg. | Source screen only. Grid-stride64-bit loops or conditional stores; no established speed advantage. Do not substitute ordinary stores for STORE_WT in a future extraction. |
| NVIDIA CUDA Samples | `0ec046d5e99d7214cc8e9fbac2cc1e66f3019878`, BSD-3-Clause, `cpp/0_Introduction/simpleMultiCopy/simpleMultiCopy.cu:58` | incKernel is the actual stream/copy overlap demonstration workload, inner_reps5, input/output separately allocated, block512. Full normal Release build is small and PTX entirely integer. | Selected and frozen. Five repeated loads/stores expose a concrete alias-dependent redundancy; exact default conditions are explicit. |

The selected kernel is genuinely upstream OSS, but is an illustrative workload
with intentional repeated work. It is not evidence of a production compression,
hashing or training application speedup. Eliminating that work changes the
intended compute load while preserving the stated observable output. An author
written restrict CUDA comparator gives the ordinary compiler the same nonalias
knowledge; it performs essentially identically to the direct PTX edit.

The actual initial parser errors, not inferred capability claims, are retained
in results/initial-parser.json, parser-metadata-before.txt and frontend-tests.txt.
The complete frozen original was never rewritten to evade unsupported syntax.
The narrow frontend additions retain metadata tokens and implement or.pred.
