// Matching two-output rolling comparators; never used to generate candidate PTX.
template<bool Wide> __device__ void body(const unsigned* __restrict__ x,
                                        unsigned* __restrict__ y, unsigned n) {
    unsigned g=blockIdx.x*blockDim.x+threadIdx.x;
    if(g>=(n+1)/2)return;
    unsigned i=2*g,s=0;
    #pragma unroll
    for(unsigned j=0;j<17;j++)s+=x[i+j];
    unsigned a=s;
    if(i+1>=n){y[i]=a;return;}
    s=s-x[i]+x[i+17];
    if(Wide && (((unsigned long long)(y+i)&7)==0))
        *(unsigned long long*)(y+i)=(unsigned long long)a|((unsigned long long)s<<32);
    else {y[i]=a;y[i+1]=s;}
}
extern "C" __global__ void paired2_cuda(const unsigned* __restrict__ x,
                                       unsigned* __restrict__ y, unsigned n) {body<true>(x,y,n);}
extern "C" __global__ void scalar2_cuda(const unsigned* __restrict__ x,
                                       unsigned* __restrict__ y, unsigned n) {body<false>(x,y,n);}
