// Block sum where out-of-range threads leave early (a common pattern).
extern "C" __global__ void r_earlyret(const unsigned* x, unsigned* out, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned tid = threadIdx.x, i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= n) return;
  s[tid] = x[i];
  __syncthreads();
  for (unsigned k = blockDim.x / 2; k > 0; k >>= 1) {
    if (tid < k) s[tid] += s[tid + k];
    __syncthreads();
  }
  if (tid == 0) out[blockIdx.x] = s[0];
}
