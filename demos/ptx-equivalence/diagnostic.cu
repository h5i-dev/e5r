// Fair traffic baselines: all outputs are defined, guarded, same alignment.
extern "C" __global__ void broadcast_rw(const unsigned* x,unsigned* y,unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if(i<n)y[i]=x[i/8];
}
extern "C" __global__ void copy_rw(const unsigned* x,unsigned* y,unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if(i<n)y[i]=x[i];
}
extern "C" __global__ void write_only(unsigned* y,unsigned n) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if(i<n)y[i]=1;
}
