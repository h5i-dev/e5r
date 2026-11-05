# API pin correction

2026-11-05, before timings: the initial dependency attempt used CuPy 13.6.0, which empirically raises AttributeError for ndarray.byteswap. The v13.6.0 links in the frozen SPEC.md were an incorrect version assumption. The actual API target and benchmark dependency are **cupy-cuda13x 14.2.0**, whose official documentation specifies the required operation:

- https://docs.cupy.dev/en/v14.2.0/reference/generated/cupy.ndarray.html#cupy.ndarray.byteswap
- https://docs.cupy.dev/en/v14.2.0/reference/generated/cupy.bitwise_xor.html

The independent mathematical/API behavior, candidate PTX, JSON contract and predeclared shapes are unchanged. The original frozen SPEC.md is retained verbatim with its original hash. No successful benchmark of 13.6.0 is claimed. CuPy is used as an executable external oracle, with no copying of its implementation algorithm. An initial web search incidentally returned a main-branch core.pyx API-wrapper excerpt; no underlying byte-transform kernel source was opened.
