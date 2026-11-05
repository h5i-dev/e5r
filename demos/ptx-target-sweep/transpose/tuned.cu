extern "C" __global__ void kernel(const unsigned* __restrict__ input,unsigned* __restrict__ output,unsigned n) {
__shared__ unsigned tile[32][33];unsigned tx=threadIdx.x,ty=threadIdx.y;
unsigned x=32*blockIdx.x+tx,y=32*blockIdx.y+ty;
#pragma unroll
for(unsigned j=0;j<4;j++)tile[ty+8*j][tx]=input[(y+8*j)*n+x];
__syncthreads();x=32*blockIdx.y+tx;y=32*blockIdx.x+ty;
#pragma unroll
for(unsigned j=0;j<4;j++)output[(y+8*j)*n+x]=tile[tx][ty+8*j]; }
