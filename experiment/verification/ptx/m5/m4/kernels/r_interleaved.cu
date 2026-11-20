// Block sum with interleaved addressing (CUDA samples, reduce0).
extern "C" __global__ void r_interleaved(const unsigned* x, unsigned* out, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned tid = threadIdx.x, i = blockIdx.x * blockDim.x + threadIdx.x;
  s[tid] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned k = 1; k < blockDim.x; k *= 2) {
    if (tid % (2 * k) == 0) s[tid] += s[tid + k];
    __syncthreads();
  }
  if (tid == 0) out[blockIdx.x] = s[0];
}
