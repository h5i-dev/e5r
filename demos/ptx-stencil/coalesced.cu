// Comparators only. Neither candidate PTX is compiled from this source.
extern "C" __global__ void striped17(const unsigned* __restrict__ x,
                                    unsigned* __restrict__ y, unsigned n) {
    unsigned long long i=4ull*blockIdx.x*blockDim.x+threadIdx.x;
    #pragma unroll
    for(unsigned k=0;k<4;k++,i+=blockDim.x) {
        if(i>=n)return;
        unsigned s=0;
        #pragma unroll
        for(unsigned j=0;j<17;j++)s+=x[i+j];
        y[i]=s;
    }
}
extern "C" __global__ void staged17(const unsigned* __restrict__ x,
                                   unsigned* __restrict__ y, unsigned n) {
    __shared__ unsigned stage[2048]; // blockDim.x <= 512
    unsigned g=blockIdx.x*blockDim.x+threadIdx.x;
    if(g<(n+3)/4) {
        unsigned i=4*g,s=0;
        #pragma unroll
        for(unsigned j=0;j<17;j++)s+=x[i+j];
        stage[4*threadIdx.x]=s;
        #pragma unroll
        for(unsigned j=1;j<4;j++) {
            if(i+j<n){s=s-x[i+j-1]+x[i+j+16];stage[4*threadIdx.x+j]=s;}
        }
    }
    __syncthreads();
    unsigned long long i=4ull*blockIdx.x*blockDim.x+threadIdx.x;
    #pragma unroll
    for(unsigned k=0;k<4;k++,i+=blockDim.x) {
        if(i<n)y[i]=stage[threadIdx.x+k*blockDim.x];
    }
}
