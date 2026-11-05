// CUDA comparators only for directly authored input-tiled PTX.
template<unsigned Outputs> __device__ void tiled_body(const unsigned* __restrict__ x,
                                                      unsigned* __restrict__ y, unsigned n,
                                                      unsigned* stage) {
    unsigned long long start=(unsigned long long)Outputs*blockIdx.x*blockDim.x;
    #pragma unroll
    for(unsigned k=0;k<Outputs;k++) {
        unsigned j=threadIdx.x+k*blockDim.x;
        stage[j]=start+j<(unsigned long long)n+16 ? x[start+j] : 0;
    }
    if(threadIdx.x<16) {
        unsigned j=Outputs*blockDim.x+threadIdx.x;
        stage[j]=start+j<(unsigned long long)n+16 ? x[start+j] : 0;
    }
    __syncthreads();
    #pragma unroll
    for(unsigned k=0;k<Outputs;k++) {
        unsigned j=threadIdx.x+k*blockDim.x;
        if(start+j<n) {
            unsigned s=0;
            #pragma unroll
            for(unsigned a=0;a<17;a++)s+=stage[j+a];
            y[start+j]=s;
        }
    }
}
extern "C" __global__ void tiled17(const unsigned* __restrict__ x,
                                  unsigned* __restrict__ y, unsigned n) {
    __shared__ unsigned stage[528];
    tiled_body<1>(x,y,n,stage);
}
extern "C" __global__ void tiled417(const unsigned* __restrict__ x,
                                   unsigned* __restrict__ y, unsigned n) {
    __shared__ unsigned stage[2064];
    tiled_body<4>(x,y,n,stage);
}
