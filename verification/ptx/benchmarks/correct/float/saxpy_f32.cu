// y[i] = fma(a, x[i], y[i]) in f32, one element per thread, rounded once.
extern "C" __global__ void saxpy_f32(float a, const float *x, float *y, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) y[i] = __fmaf_rn(a, x[i], y[i]);
}
