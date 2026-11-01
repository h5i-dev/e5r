// Block sum for blocks of at most 256 threads.
extern "C" __global__ void r_256(const unsigned* x, unsigned* y, unsigned n) {
  __shared__ unsigned s[256];
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  unsigned v = 0;
  if (i < n) v = x[i];
  s[threadIdx.x] = v;
  __syncthreads();
  for (unsigned k = blockDim.x >> 1; k > 0; k >>= 1) {
    if (threadIdx.x < k) s[threadIdx.x] += s[threadIdx.x + k];
    __syncthreads();
  }
  if (threadIdx.x == 0) y[blockIdx.x] = s[0];
}
