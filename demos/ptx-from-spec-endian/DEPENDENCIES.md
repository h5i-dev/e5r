# Pinned tools and provenance

The candidate PTX, Lean proof, mathematical specification, Python harness and CUDA baselines were authored here. No candidate was compiled from CUDA/Triton or copied from another worker. API documentation and executable public API behavior were the design sources. A web search incidentally surfaced a main-branch CuPy core.pyx wrapper excerpt (dtype/itemsize handling); no upstream byte-transform kernel source was opened or copied, and the candidate algorithm was independently derived from the byte permutation. This repository's LICENSE applies to original demo files.

Dependencies are fetched into scratch, not vendored:

| Dependency | Version | License / role |
| --- | --- | --- |
| CuPy CUDA13 wheel | 14.2.0 | MIT; actual byteswap/XOR external oracle and performance baseline; CUDA driver binding |
| NumPy | 2.2.6 | BSD-3-Clause; CPU reference arrays and differential byteswap oracle; wheel includes additional licensed libraries listed in its metadata |
| cuda-pathfinder | 1.8.5 | Apache-2.0; CuPy dependency |
| Lean | leanprover/lean4:v4.35.0 | Apache-2.0; Lean kernel, lake, proofcheck, leanchecker |
| E5R | base b99d7a1, unchanged verifier | repository Apache-2.0; existing PTX semantics/checker |
| NVIDIA CUDA toolkit | 13.2.51 | NVIDIA licenses; nvcc -O3 -std=c++17 -arch=sm_86 -cubin baseline.cu; ptxas -arch=sm_86 for assembly check |

Actual API docs: [CuPy 14.2 ndarray.byteswap](https://docs.cupy.dev/en/v14.2.0/reference/generated/cupy.ndarray.html#cupy.ndarray.byteswap), [bitwise_xor](https://docs.cupy.dev/en/v14.2.0/reference/generated/cupy.bitwise_xor.html). The original 13.6.0 version assumption and correction are retained in API-PIN.md and PROVENANCE.txt. The failed initial CuPy12 environment packages do not belong to the final requirements or measured runtime.

CUDA __byte_perm behavior is documented in the [CUDA Math API](https://docs.nvidia.com/cuda/cuda-math-api/cuda_math_api/group__CUDA__MATH__INTRINSIC__INT.html). Baselines use the byte selector 0x0123. Their outputs are checked against the independent CPU byte-array reversal and actual OSS APIs; they are not formal proof subjects. No upstream code is distributed by this demo.
