// Inclusive scan of each block's segment (Hillis-Steele), read then add.
extern "C" __global__ void s_hs(const unsigned* x, unsigned* y, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned t = threadIdx.x;
  unsigned i = blockIdx.x * blockDim.x + t;
  s[t] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned d = 1; d < blockDim.x; d *= 2) {
    unsigned v = 0;
    if (t >= d) v = s[t - d];
    __syncthreads();
    s[t] += v;
    __syncthreads();
  }
  if (i < n) y[i] = s[t];
}
