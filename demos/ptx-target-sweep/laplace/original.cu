extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned rows) {
unsigned x=blockIdx.x*blockDim.x+threadIdx.x,y=blockIdx.y*blockDim.y+threadIdx.y;
if(x<1024 && y<rows){const unsigned* p=input+(y+1)*1026+x+1;
output[y*1024+x]=(p[0]<<2)-p[-1]-p[1]-p[-1026]-p[1026];}}
