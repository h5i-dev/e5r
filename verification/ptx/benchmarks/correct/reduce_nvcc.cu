// Block tree reduction, compiled by nvcc 13.2 -O3 -arch=sm_86 --ptx to
// reduce_nvcc.ptx. Each CTA of B threads (B a power of two, B <= 1024)
// writes the sum of its B-element segment of x (elements at or past n
// count as 0) to out[blockIdx.x].
extern "C" __global__ void reduce(const unsigned* x, unsigned* out, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned tid = threadIdx.x;
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  s[tid] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned k = blockDim.x / 2; k > 0; k >>= 1) {
    if (tid < k) s[tid] += s[tid + k];
    __syncthreads();
  }
  if (tid == 0) out[blockIdx.x] = s[0];
}
