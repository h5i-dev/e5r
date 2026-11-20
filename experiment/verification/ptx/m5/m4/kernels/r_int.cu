// Block sum with signed int indices, as most CUDA tutorials write it.
extern "C" __global__ void r_int(const unsigned* in, unsigned* out, int n) {
  __shared__ unsigned sdata[1024];
  int tid = threadIdx.x;
  int i = blockIdx.x * blockDim.x + threadIdx.x;
  sdata[tid] = 0;
  if (i < n) sdata[tid] = in[i];
  __syncthreads();
  for (int s = blockDim.x / 2; s > 0; s >>= 1) {
    if (tid < s) sdata[tid] += sdata[tid + s];
    __syncthreads();
  }
  if (tid == 0) out[blockIdx.x] = sdata[0];
}
