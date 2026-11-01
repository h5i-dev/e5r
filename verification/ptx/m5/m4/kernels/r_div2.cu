// Block sum, one result per block. Halving written as a division.
extern "C" __global__ void r_div2(const unsigned* in, unsigned* out, unsigned n) {
  __shared__ unsigned buf[1024];
  unsigned t = threadIdx.x;
  unsigned g = blockIdx.x * blockDim.x + t;
  buf[t] = (g < n) ? in[g] : 0u;
  __syncthreads();
  for (unsigned s = blockDim.x / 2; s != 0; s /= 2) {
    if (t < s) buf[t] = buf[t] + buf[t + s];
    __syncthreads();
  }
  if (t == 0) out[blockIdx.x] = buf[0];
}
