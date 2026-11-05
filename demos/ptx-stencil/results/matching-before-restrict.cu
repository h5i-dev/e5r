// Known rolling-window CUDA baseline, independently compiled only as comparator.
extern "C" __global__ void matching17(const unsigned* x,unsigned* y,unsigned n) {
    unsigned g=blockIdx.x*blockDim.x+threadIdx.x;
    if(g>=(n+3)/4)return;
    unsigned i=4*g,s=0;
    #pragma unroll
    for(unsigned j=0;j<17;j++)s+=x[i+j];
    y[i]=s;
    #pragma unroll
    for(unsigned j=1;j<4;j++) {
        if(i+j<n) {s=s-x[i+j-1]+x[i+j+16];y[i+j]=s;}
    }
}
extern "C" __global__ void matching64(const unsigned* x,unsigned* y,unsigned n) {
    unsigned g=blockIdx.x*blockDim.x+threadIdx.x;
    if(g>=(n+3)/4)return;
    unsigned i=4*g,s=0;
    #pragma unroll
    for(unsigned j=0;j<17;j++)s+=x[i+j];
    unsigned a=s;
    if(i+1>=n){y[i]=a;return;}
    s=s-x[i]+x[i+17];
    if(((unsigned long long)(y+i)&7)==0)
        *(unsigned long long*)(y+i)=(unsigned long long)a|((unsigned long long)s<<32);
    else {y[i]=a;y[i+1]=s;}
    if(i+2>=n)return;
    s=s-x[i+1]+x[i+18];a=s;
    if(i+3>=n){y[i+2]=a;return;}
    s=s-x[i+2]+x[i+19];
    if(((unsigned long long)(y+i+2)&7)==0)
        *(unsigned long long*)(y+i+2)=(unsigned long long)a|((unsigned long long)s<<32);
    else {y[i+2]=a;y[i+3]=s;}
}
