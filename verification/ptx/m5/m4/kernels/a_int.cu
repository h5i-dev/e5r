// Total sum with int indices and a 512-word buffer.
extern "C" __global__ void a_int(const unsigned* x, unsigned* total, int n) {
  __shared__ unsigned s[512];
  int tid = threadIdx.x;
  int i = blockIdx.x * blockDim.x + tid;
  s[tid] = (i < n) ? x[i] : 0;
  __syncthreads();
  for (int k = blockDim.x / 2; k > 0; k /= 2) {
    if (tid < k) s[tid] += s[tid + k];
    __syncthreads();
  }
  if (tid == 0) atomicAdd(total, s[0]);
}
