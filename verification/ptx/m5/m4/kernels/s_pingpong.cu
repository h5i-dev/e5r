// Inclusive block scan with two buffers and one barrier per round.
extern "C" __global__ void s_pingpong(const unsigned* x, unsigned* y, unsigned n) {
  __shared__ unsigned buf[2][1024];
  unsigned t = threadIdx.x;
  unsigned i = blockIdx.x * blockDim.x + t;
  int src = 0;
  buf[0][t] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned d = 1; d < blockDim.x; d <<= 1) {
    unsigned v = buf[src][t];
    if (t >= d) v += buf[src][t - d];
    buf[1 - src][t] = v;
    src = 1 - src;
    __syncthreads();
  }
  if (i < n) y[i] = buf[src][t];
}
