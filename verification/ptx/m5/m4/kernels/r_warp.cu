// Block sum with the last warp unrolled without barriers (old CUDA samples, reduce4).
extern "C" __global__ void r_warp(const unsigned* x, unsigned* out, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned tid = threadIdx.x, i = blockIdx.x * blockDim.x + threadIdx.x;
  s[tid] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned k = blockDim.x / 2; k > 32; k >>= 1) {
    if (tid < k) s[tid] += s[tid + k];
    __syncthreads();
  }
  if (tid < 32) {
    volatile unsigned* v = s;
    if (blockDim.x >= 64) v[tid] += v[tid + 32];
    if (blockDim.x >= 32) v[tid] += v[tid + 16];
    if (blockDim.x >= 16) v[tid] += v[tid + 8];
    if (blockDim.x >= 8) v[tid] += v[tid + 4];
    if (blockDim.x >= 4) v[tid] += v[tid + 2];
    if (blockDim.x >= 2) v[tid] += v[tid + 1];
  }
  if (tid == 0) out[blockIdx.x] = s[0];
}
