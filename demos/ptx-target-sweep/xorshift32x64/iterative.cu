extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) { unsigned i=blockIdx.x*blockDim.x+threadIdx.x; if(i>=n)return; unsigned x=input[i]; 
#pragma unroll
for(unsigned j=0;j<64;j++){x^=x<<13; x^=x>>17; x^=x<<5;} output[i]=x;}
