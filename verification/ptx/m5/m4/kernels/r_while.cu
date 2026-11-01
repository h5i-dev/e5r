// Block sum with a while loop.
extern "C" __global__ void r_while(const unsigned* x, unsigned* out, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned tid = threadIdx.x, gid = blockIdx.x * blockDim.x + threadIdx.x;
  s[tid] = gid < n ? x[gid] : 0;
  __syncthreads();
  unsigned k = blockDim.x;
  while (k > 1) {
    k >>= 1;
    if (tid < k) s[tid] += s[tid + k];
    __syncthreads();
  }
  if (tid == 0) out[blockIdx.x] = s[0];
}
