// Inclusive block scan that only writes when it adds something.
extern "C" __global__ void s_cond(const unsigned* x, unsigned* y, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned t = threadIdx.x;
  unsigned i = blockIdx.x * blockDim.x + t;
  s[t] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned d = 1; d < blockDim.x; d <<= 1) {
    unsigned v = t >= d ? s[t - d] : 0;
    __syncthreads();
    if (t >= d) s[t] += v;
    __syncthreads();
  }
  if (i < n) y[i] = s[t];
}
