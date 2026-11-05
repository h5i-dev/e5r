extern "C" __global__ void kernel(const unsigned* __restrict__ input,unsigned* __restrict__ output,unsigned rows) {
__shared__ unsigned tile[10][34];unsigned tx=threadIdx.x,ty=threadIdx.y;
unsigned x=32*blockIdx.x+tx,y=8*blockIdx.y+ty;const unsigned* p=input+(y+1)*1026+x+1;
unsigned c=p[0];tile[ty+1][tx+1]=c;
if(tx==0){tile[ty+1][0]=p[-1];tile[ty+1][33]=p[32];}
if(ty==0){tile[0][tx+1]=p[-1026];tile[9][tx+1]=p[8*1026];}
__syncthreads();output[y*1024+x]=(c<<2)-tile[ty+1][tx]-tile[ty+1][tx+2]-tile[ty][tx+1]-tile[ty+2][tx+1];}
