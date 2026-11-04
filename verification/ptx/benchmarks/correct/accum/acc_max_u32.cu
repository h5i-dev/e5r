// *out = max(*out, x[0], ..., x[min(n, G*B) - 1]) with one atomicMax per element,
// compiled by nvcc 13.2 -O3 -arch=sm_86 --ptx.
extern "C" __global__ void acc_max_u32(const unsigned* x, unsigned* out, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) atomicMax(out, x[i]);
}
