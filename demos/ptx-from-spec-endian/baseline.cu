// Authored only after candidate/spec freeze. No code from upstream implementations.
#include <stdint.h>
// CUDA's byte permutation intrinsic gives a competent one-instruction swap.
extern "C" __global__ void fused_cuda(const uint32_t* __restrict__ x,
                                     uint32_t* __restrict__ y, uint32_t n, uint32_t mask) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) y[i] = __byte_perm(x[i], 0, 0x0123) ^ mask;
}
extern "C" __global__ void swap_cuda(const uint32_t* __restrict__ x,
                                    uint32_t* __restrict__ y, uint32_t n, uint32_t unused) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) y[i] = __byte_perm(x[i], 0, 0x0123);
}
// Vectorized alternative avoids making the CUDA baseline needlessly scalar.
extern "C" __global__ void fused_cuda_vec4(const uint32_t* __restrict__ x,
                                          uint32_t* __restrict__ y, uint32_t n, uint32_t mask) {
    uint32_t j = blockIdx.x * blockDim.x + threadIdx.x;
    if (j < n / 4) {
        uint4 a = reinterpret_cast<const uint4*>(x)[j];
        uint4 b = make_uint4(__byte_perm(a.x, 0, 0x0123) ^ mask,
                            __byte_perm(a.y, 0, 0x0123) ^ mask,
                            __byte_perm(a.z, 0, 0x0123) ^ mask,
                            __byte_perm(a.w, 0, 0x0123) ^ mask);
        reinterpret_cast<uint4*>(y)[j] = b;
    }
    uint32_t i = (n / 4) * 4 + j;
    if (i < n) y[i] = __byte_perm(x[i], 0, 0x0123) ^ mask;
}
