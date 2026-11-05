extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) { unsigned i=blockIdx.x*blockDim.x+threadIdx.x; if(i>=n)return; const unsigned* p=input+8*i; unsigned x=0;
if(((unsigned long long)p&7)==0) {const unsigned long long* q=(const unsigned long long*)p;
unsigned long long v=q[0]^q[1]^q[2]^q[3];x=(unsigned)v^(unsigned)(v>>32);}
else {
#pragma unroll
for(unsigned j=0;j<8;j++)x^=p[j];}
output[i]=x;}
