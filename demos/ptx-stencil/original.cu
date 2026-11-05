// Ordinary exact uint32 17-tap 1D box stencil. Input holds n+16 words.
// Unsigned addition is modulo 2^32; no floating-point/reassociation issue.
extern "C" __global__ void stencil17(const unsigned* input, unsigned* output, unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if(i>=n)return;
    unsigned s=0;
    #pragma unroll
    for(unsigned j=0;j<17;j++)s+=input[i+j];
    output[i]=s;
}
