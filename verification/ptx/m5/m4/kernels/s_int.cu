// Inclusive block scan with int indices.
extern "C" __global__ void s_int(const unsigned* x, unsigned* y, int n) {
  __shared__ unsigned temp[1024];
  int tid = threadIdx.x;
  int i = blockIdx.x * blockDim.x + tid;
  temp[tid] = (i < n) ? x[i] : 0;
  __syncthreads();
  for (int off = 1; off < blockDim.x; off <<= 1) {
    unsigned add = (tid >= off) ? temp[tid - off] : 0;
    __syncthreads();
    temp[tid] = temp[tid] + add;
    __syncthreads();
  }
  if (i < n) y[i] = temp[tid];
}
