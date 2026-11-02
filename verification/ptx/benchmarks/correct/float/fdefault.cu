// Plain CUDA C with nvcc's defaults (-fmad=true, -prec-div=true, -prec-sqrt=true).
extern "C" __global__ void f_axpy_default(float a, const float *x, float *y, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) y[i] = a * x[i] + y[i];
}
extern "C" __global__ void f_div_default(const float *x, const float *y, float *z, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) z[i] = x[i] / y[i];
}
extern "C" __global__ void f_sqrt_default(const float *x, float *y, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) y[i] = sqrtf(x[i]);
}
extern "C" __global__ void f_relu_default(const float *x, float *y, unsigned n) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) y[i] = fmaxf(x[i], 0.0f);
}
