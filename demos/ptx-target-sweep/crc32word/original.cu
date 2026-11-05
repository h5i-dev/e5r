extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) { unsigned i=blockIdx.x*blockDim.x+threadIdx.x; if(i>=n)return; unsigned x=input[i];
#pragma unroll
for(unsigned j=0;j<32;j++) { if(x&1u)x=(x>>1)^0xedb88320u;else x>>=1; }
output[i]=x; }
