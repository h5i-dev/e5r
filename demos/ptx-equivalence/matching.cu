// Competent CUDA expression for the candidate's arithmetic, compiled only
// as an independent performance comparator, never as candidate provenance.
extern "C" __global__ void matching(const unsigned* input, unsigned* output, unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if (i<n) {
        unsigned x=(input[i/8]>>(4*(i%8)))&15;
        output[i]=(x*0x00204081u)&0x01010101u;
    }
}
