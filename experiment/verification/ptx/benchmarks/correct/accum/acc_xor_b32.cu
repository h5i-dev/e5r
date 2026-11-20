// *out = xor(*out, x[0], ..., x[min(n, G*B) - 1]) with one atomicXor per element,
// compiled by nvcc 13.2 -O3 -arch=sm_86 --ptx.
extern "C" __global__ void acc_xor_b32(const unsigned* x, unsigned* out, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) atomicXor(out, x[i]);
}
