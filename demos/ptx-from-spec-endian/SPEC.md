# Frozen independent specification, v1

Frozen 2026-11-05 UTC before candidate authorship, CUDA compilation, or timing.

API target: the composition `cupy.bitwise_xor(x.byteswap(), uint32(mask))` on a contiguous one-dimensional native uint32 array. CuPy ndarray.byteswap reverses bytes within each element; bitwise_xor performs the bitwise exclusive OR. This demo supports precisely this subset; no signed, float, structured, strided, multidimensional, inplace, or dtype-metadata conversion API is promised. This is an endian conversion with a mask, not an INT4 operator.

Independent mathematical specification: let input element i have four bytes b(i,0), b(i,1), b(i,2), b(i,3), in increasing memory address order, each in [0,255]. Its unsigned value is sum over j=0..3 of b(i,j)*256^j. The output value is `(sum over j=0..3 of b(i,3-j)*256^j) XOR mask`. Equivalently, output bit k, for 0 <= k < 32, equals input bit `8*(3-floor(k/8)) + (k mod 8)` XOR mask bit k. Bits in each byte retain their order. XOR is after reversal.

Input/output: n elements, each exactly four bytes, little endian device memory. n is an unsigned 32-bit length, 0 <= n < 2^32. mask is any uint32. Both bases are 4-byte aligned; base+4*n <= 2^64; the two half-open byte ranges are disjoint. Initial output contents are arbitrary. Input and all bytes outside output are unchanged. No scale/group indexing applies.

Launch: one-dimensional grid and blocks, positive dimensions; n <= G*B <= 2^32. A thread's mathematical global index is blockIdx.x*blockDim.x+threadIdx.x. Each valid index is written exactly once. Threads beyond n must perform no memory access. n=0 uses a one-block no-op launch in executable tests. Hardware execution additionally respects device launch limits; the theorem covers the model's entire declared range, including launch sizes too large to physically test. The host wrapper uses 256 threads/block and ceiling(n/256), at least one block.

Claims to establish using E5R's existing PTX execution semantics: no illegal access, no conflicting accesses between threads, bounded termination, output formula for every initial input/mask/output and every modeled interleaving, and frame preservation. The supplied checker must accept the exact candidate/spec SHA256 pair and replay all proof declarations in the Lean kernel with only propext, Quot.sound, Classical.choice. A bridge theorem must connect the executable contract to the independent bit-layout equation above. ptxas/driver/SASS correspondence is tested empirically and is outside the theorem.

Predeclared measured lengths (elements): 0, 1, 31, 32, 255, 256, 257, 4096, 65536, 1048576, 4194304, 16777216. Report every shape, both ordinary event timing and graph replay. Goal: >=1.5x versus actual OSS composition across meaningful bandwidth sizes (n >= 1048576); also report ratios versus a competent fused CUDA implementation and standalone byteswap. Fusion and hand assembly effects are separate. No goal is a promised outcome. Preallocate; JIT and startup excluded from all timings; repeated batches and variance, randomized method ordering; raw data retained.

API documentation (read, no upstream implementation read):
https://docs.cupy.dev/en/v13.6.0/reference/generated/cupy.ndarray.html
https://docs.cupy.dev/en/v13.6.0/reference/generated/cupy.bitwise_xor.html
