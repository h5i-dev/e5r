// *out = or(*out, x[0], ..., x[min(n, G*B) - 1]) with one atomicOr per element,
// compiled by nvcc 13.2 -O3 -arch=sm_86 --ptx.
extern "C" __global__ void acc_or_b64(const unsigned long long* x, unsigned long long* out, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) atomicOr(out, x[i]);
}
