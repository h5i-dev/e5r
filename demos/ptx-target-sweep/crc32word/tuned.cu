extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) { unsigned i=blockIdx.x*blockDim.x+threadIdx.x; if(i>=n)return; unsigned x=input[i];
#pragma unroll
for(unsigned k=0;k<8;k++){ unsigned y=x>>4;
if(x&1u)y^=498536548u;
if(x&2u)y^=997073096u;
if(x&4u)y^=1994146192u;
if(x&8u)y^=3988292384u;
x=y;} output[i]=x;}
