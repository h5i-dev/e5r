// Comparator only; candidate PTX is directly edited, never compiled from CUDA.
extern "C" __global__ void wide_input_cuda(const unsigned* __restrict__ x,
                                          unsigned* __restrict__ y, unsigned n) {
    unsigned g=blockIdx.x*blockDim.x+threadIdx.x;
    if(g>=(n+1)/2)return;
    unsigned i=2*g,s=0,a,arriving=0;
    const unsigned* p=x+i;
    unsigned* q=y+i;
    if((((unsigned long long)p&7)==0) && i+1<n) {
        const unsigned long long* v=(const unsigned long long*)p;
        unsigned long long first=v[0];
        s=(unsigned)first+(unsigned)(first>>32);
        #pragma unroll
        for(unsigned j=1;j<8;j++) {
            unsigned long long z=v[j];
            s+=(unsigned)z+(unsigned)(z>>32);
        }
        unsigned long long last=v[8];
        s+=(unsigned)last;
        a=s;
        s=s-(unsigned)first+(unsigned)(last>>32);
    } else {
        #pragma unroll
        for(unsigned j=0;j<17;j++)s+=p[j];
        a=s;
        if(i+1>=n){q[0]=a;return;}
        arriving=p[17];
        s=s-p[0]+arriving;
    }
    if(((unsigned long long)q&7)==0)
        *(unsigned long long*)q=(unsigned long long)a|((unsigned long long)s<<32);
    else {q[0]=a;q[1]=s;}
}
