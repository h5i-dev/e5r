// Four little-endian unpacked bits per output word. A byte implementation
// would issue four stores; this ordinary CUDA uses one aligned word store.
extern "C" __global__ void unpack4(const unsigned* input, unsigned* output, unsigned n) {
    unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    unsigned x = input[i / 8] >> (4 * (i % 8));
    x &= 15;
    x = (x | (x << 14)) & 0x00030003;
    output[i] = (x | (x << 7)) & 0x01010101;
}
