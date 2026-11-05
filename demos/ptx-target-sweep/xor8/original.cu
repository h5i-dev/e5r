extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) { unsigned i=blockIdx.x*blockDim.x+threadIdx.x; if(i>=n)return; const unsigned* p=input+8*i; unsigned x=0;
#pragma unroll
for(unsigned j=0;j<8;j++)x^=p[j]; output[i]=x; }
