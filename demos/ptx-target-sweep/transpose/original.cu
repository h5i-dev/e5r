extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) {
unsigned x=blockIdx.x*blockDim.x+threadIdx.x,y=blockIdx.y*blockDim.y+threadIdx.y;
if(x<n && y<n)output[x*n+y]=input[y*n+x]; }
