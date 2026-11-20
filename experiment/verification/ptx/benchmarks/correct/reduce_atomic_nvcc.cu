// Block tree reduction finished with one atomicAdd per CTA, compiled by
// nvcc 13.2 -O3 -arch=sm_86 --ptx to reduce_atomic_nvcc.ptx. After the
// launch *out holds its initial value plus the sum of x[0..n) (mod 2^32).
extern "C" __global__ void reduce_atomic(const unsigned* x, unsigned* out, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned tid = threadIdx.x;
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  s[tid] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned k = blockDim.x / 2; k > 0; k >>= 1) {
    if (tid < k) s[tid] += s[tid + k];
    __syncthreads();
  }
  if (tid == 0) atomicAdd(out, s[0]);
}
