// Total sum: every thread adds its element atomically.
extern "C" __global__ void a_direct(const unsigned* x, unsigned* total, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) atomicAdd(total, x[i]);
}
