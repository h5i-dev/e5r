// Total sum: block tree, then one atomicAdd per block.
extern "C" __global__ void a_tree(const unsigned* x, unsigned* total, unsigned n) {
  __shared__ unsigned part[1024];
  unsigned t = threadIdx.x;
  unsigned i = blockIdx.x * blockDim.x + t;
  part[t] = i < n ? x[i] : 0;
  __syncthreads();
  for (unsigned s = blockDim.x >> 1; s; s >>= 1) {
    if (t < s) part[t] += part[t + s];
    __syncthreads();
  }
  if (t == 0) atomicAdd(total, part[0]);
}
