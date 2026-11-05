// Matching two-output rolling comparators; never used to generate candidate PTX.
template<bool Wide> __device__ void body(const unsigned* __restrict__ x,
                                        unsigned* __restrict__ y, unsigned n) {
    unsigned g=blockIdx.x*blockDim.x+threadIdx.x;
    if(g>=(n+1)/2)return;
    unsigned i=2*g,s=0;
    const unsigned* p=x+i;
    unsigned* q=y+i;
    #pragma unroll
    for(unsigned j=0;j<17;j++)s+=p[j];
    unsigned a=s;
    if(i+1>=n){q[0]=a;return;}
    s=s-p[0]+p[17];
    if(Wide && (((unsigned long long)q&7)==0))
        *(unsigned long long*)q=(unsigned long long)a|((unsigned long long)s<<32);
    else {q[0]=a;q[1]=s;}
}
extern "C" __global__ void paired2_cuda(const unsigned* __restrict__ x,
                                       unsigned* __restrict__ y, unsigned n) {body<true>(x,y,n);}
extern "C" __global__ void scalar2_cuda(const unsigned* __restrict__ x,
                                       unsigned* __restrict__ y, unsigned n) {body<false>(x,y,n);}
