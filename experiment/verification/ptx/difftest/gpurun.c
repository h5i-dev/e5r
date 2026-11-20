// Run the differential cases on the GPU through the CUDA driver API.
//
//   gpurun MODULE CASES > OUT
//
// MODULE is PTX text (JIT-compiled by the driver) or a cubin from ptxas;
// cuModuleLoadData takes either. For every line
//   case KERNEL gx gy gz bx by bz S INHEX OUTBYTES
// of CASES it allocates the input buffer (INHEX) and an output buffer of
// OUTBYTES bytes filled with 0xA5, launches KERNEL(in, out, S) on the given
// grid and block, and prints
//   result KERNEL OUTHEX
// A launch error is printed as `error KERNEL CODE` and the run continues.
#include <cuda.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CK(x)                                                                 \
  do {                                                                        \
    CUresult r_ = (x);                                                        \
    if (r_ != CUDA_SUCCESS) {                                                 \
      const char *s_ = 0;                                                     \
      cuGetErrorString(r_, &s_);                                              \
      fprintf(stderr, "gpurun: %s: %s\n", #x, s_ ? s_ : "?");                 \
      exit(2);                                                                \
    }                                                                         \
  } while (0)

static unsigned char *slurp(const char *p, size_t *n) {
  FILE *f = fopen(p, "rb");
  if (!f) { perror(p); exit(2); }
  fseek(f, 0, SEEK_END);
  long len = ftell(f);
  fseek(f, 0, SEEK_SET);
  unsigned char *b = malloc(len + 1);
  if (fread(b, 1, len, f) != (size_t)len) { perror(p); exit(2); }
  b[len] = 0;
  fclose(f);
  *n = len;
  return b;
}

static int hexval(int c) {
  return c <= '9' ? c - '0' : (c | 32) - 'a' + 10;
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: gpurun MODULE CASES\n"); return 2; }
  size_t mlen;
  unsigned char *mod = slurp(argv[1], &mlen);
  CK(cuInit(0));
  CUdevice dev;
  CK(cuDeviceGet(&dev, 0));
  CUcontext ctx;
  CK(cuDevicePrimaryCtxRetain(&ctx, dev));
  CK(cuCtxSetCurrent(ctx));
  char name[256];
  CK(cuDeviceGetName(name, sizeof name, dev));
  int drv;
  CK(cuDriverGetVersion(&drv));
  fprintf(stderr, "gpurun: %s, driver API %d\n", name, drv);
  CUmodule m;
  char log[8192] = {0};
  CUjit_option opts[] = {CU_JIT_ERROR_LOG_BUFFER, CU_JIT_ERROR_LOG_BUFFER_SIZE_BYTES};
  void *vals[] = {log, (void *)(size_t)sizeof log};
  CUresult lr = cuModuleLoadDataEx(&m, mod, 2, opts, vals);
  if (lr != CUDA_SUCCESS) { fprintf(stderr, "gpurun: module load failed: %d\n%s\n", lr, log); return 2; }

  FILE *cf = fopen(argv[2], "r");
  if (!cf) { perror(argv[2]); return 2; }
  size_t cap = 1 << 20;
  char *line = malloc(cap);
  ssize_t got;
  while ((got = getline(&line, &cap, cf)) > 0) {
    char kname[128], *inhex = malloc(got);
    unsigned gx, gy, gz, bx, by, bz, s;
    size_t outn;
    if (sscanf(line, "case %127s %u %u %u %u %u %u %u %s %zu", kname, &gx, &gy, &gz, &bx, &by, &bz,
               &s, inhex, &outn) != 10) {
      fprintf(stderr, "gpurun: bad case line\n");
      return 2;
    }
    size_t inn = strlen(inhex) / 2;
    unsigned char *in = malloc(inn + 1), *out = malloc(outn);
    for (size_t i = 0; i < inn; i++) in[i] = hexval(inhex[2 * i]) << 4 | hexval(inhex[2 * i + 1]);
    memset(out, 0xA5, outn);
    CUfunction f;
    CK(cuModuleGetFunction(&f, m, kname));
    CUdeviceptr din, dout;
    CK(cuMemAlloc(&din, inn ? inn : 1));
    CK(cuMemAlloc(&dout, outn));
    if (inn) CK(cuMemcpyHtoD(din, in, inn));
    CK(cuMemcpyHtoD(dout, out, outn));
    void *args[] = {&din, &dout, &s};
    CUresult r = cuLaunchKernel(f, gx, gy, gz, bx, by, bz, 0, 0, args, 0);
    if (r == CUDA_SUCCESS) r = cuCtxSynchronize();
    if (r != CUDA_SUCCESS) {
      printf("error %s %d\n", kname, r);
      return 1;  // a sticky error poisons the context; stop here
    }
    CK(cuMemcpyDtoH(out, dout, outn));
    printf("result %s ", kname);
    for (size_t i = 0; i < outn; i++) printf("%02x", out[i]);
    printf("\n");
    CK(cuMemFree(din));
    CK(cuMemFree(dout));
    free(in);
    free(out);
    free(inhex);
  }
  return 0;
}
