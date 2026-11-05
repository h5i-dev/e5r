extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) { unsigned i=blockIdx.x*blockDim.x+threadIdx.x; if(i>=n)return; unsigned x=input[i];
#pragma unroll
for(unsigned j=0;j<256;j++)x=1664525u*x+1013904223u;
output[i]=x; }
