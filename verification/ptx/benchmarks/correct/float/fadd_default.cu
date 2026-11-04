// Plain CUDA C with nvcc's defaults: x + y becomes add.f32 with no rounding modifier.
extern "C" __global__ void f_add_default(const float *x, const float *y, float *z, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) z[i] = x[i] + y[i];
}
