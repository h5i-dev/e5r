// Independently authored baselines, compiled with nvcc -O3 -arch=sm_86.
// Grid-stride warp ballots avoid launching one thread per byte globally.
template<bool Threshold> __device__ void ballot(const unsigned char* x, unsigned char* y, unsigned n) {
    for (unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
         __any_sync(0xffffffff, i < n); i += gridDim.x * blockDim.x) {
        bool b = i < n && (Threshold ? x[i] > 127 : x[i] != 0);
        unsigned word = __ballot_sync(0xffffffff, b);
        if ((threadIdx.x & 31) == 0 && i < n)
            reinterpret_cast<unsigned*>(y)[i / 32] = word;
    }
}
extern "C" __global__ void ballot_pack(const unsigned char* x, unsigned char* y, unsigned n) { ballot<false>(x,y,n); }
extern "C" __global__ void ballot_threshold(const unsigned char* x, unsigned char* y, unsigned n) { ballot<true>(x,y,n); }
extern "C" __global__ void coalesced_unpack(const unsigned char* x, unsigned char* y, unsigned n) {
    for (unsigned i = blockIdx.x * blockDim.x + threadIdx.x; i < n; i += gridDim.x * blockDim.x)
        y[i] = (x[i / 8] >> (i % 8)) & 1;
}
// A competent CUDA implementation using the same 32-byte group ownership.
// Full nonzero predicate, no assumption that inputs are already booleans.
extern "C" __global__ void grouped_pack(const unsigned* x, unsigned* y, unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if (i>=n) return;
    unsigned result=0;
    #pragma unroll
    for (unsigned j=0;j<8;j++) {
        unsigned v=x[8*i+j];
        #pragma unroll
        for (unsigned k=0;k<4;k++) result |= (((v>>(8*k))&255)!=0) << (4*j+k);
    }
    y[i]=result;
}
extern "C" __global__ void grouped_threshold(const unsigned* x, unsigned* y, unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if (i>=n) return;
    unsigned result=0;
    #pragma unroll
    for (unsigned j=0;j<8;j++) {
        unsigned v=x[8*i+j];
        #pragma unroll
        for (unsigned k=0;k<4;k++) result |= (((v>>(8*k))&128)!=0) << (4*j+k);
    }
    y[i]=result;
}
extern "C" __global__ void grouped_unpack(const unsigned* x, unsigned* y, unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if (i>=n) return;
    unsigned v=x[i];
    #pragma unroll
    for (unsigned j=0;j<8;j++) {
        unsigned z=(v>>(4*j))&15;
        z=(z|(z<<14))&0x00030003;
        z=(z|(z<<7))&0x01010101;
        y[8*i+j]=z;
    }
}
// Match the optimized candidate's four output bytes per thread as well.
extern "C" __global__ void word_unpack(const unsigned* x, unsigned* y, unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if (i>=n) return;
    unsigned z=(x[i/8]>>(4*(i%8)))&15;
    z=(z|(z<<14))&0x00030003;
    y[i]=(z|(z<<7))&0x01010101;
}
