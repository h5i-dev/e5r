
extern "C" __global__ void unpack(const unsigned char* __restrict__ x, unsigned long long* __restrict__ y, unsigned n){
 for(unsigned i=blockIdx.x*blockDim.x+threadIdx.x;i<n;i+=gridDim.x*blockDim.x){
 unsigned v=x[i];unsigned long long z=0;
 #pragma unroll
 for(int j=0;j<8;j++)z|=(unsigned long long)((v>>(7-j))&1)<<(8*j);
 y[i]=z;
 }}
extern "C" __global__ void pack(const unsigned char* __restrict__ x, unsigned char* __restrict__ y, unsigned n){
 for(unsigned i=blockIdx.x*blockDim.x+threadIdx.x;i<n/8;i+=gridDim.x*blockDim.x){
 unsigned v=0;
 #pragma unroll
 for(int j=0;j<8;j++)v|=(unsigned)(x[8*i+j]!=0)<<(7-j);
 y[i]|=v;
 }}
