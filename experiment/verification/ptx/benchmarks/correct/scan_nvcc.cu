// Hillis-Steele inclusive scan of each CTA's segment, compiled by nvcc 13.2
// -O3 -arch=sm_86 --ptx to scan_nvcc.ptx. For every i < n, out[i] is the
// sum of x[j] for j from the start of i's CTA segment to i (B <= 1024).
extern "C" __global__ void scan(const unsigned* x, unsigned* out, unsigned n) {
  __shared__ unsigned s[1024];
  unsigned tid = threadIdx.x;
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  s[tid] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned off = 1; off < blockDim.x; off <<= 1) {
    unsigned t = tid >= off ? s[tid - off] : 0;
    __syncthreads();
    s[tid] += t;
    __syncthreads();
  }
  if (i < n) out[i] = s[tid];
}
