// *out = min(*out, x[0], ..., x[min(n, G*B) - 1]) with one atomicMin per element,
// compiled by nvcc 13.2 -O3 -arch=sm_86 --ptx.
extern "C" __global__ void acc_min_s32(const int* x, int* out, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) atomicMin(out, x[i]);
}
