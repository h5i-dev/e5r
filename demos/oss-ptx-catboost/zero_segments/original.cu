#include <cuda_runtime.h>
#include <stdint.h>
using ui8=uint8_t; using ui32=uint32_t; using ui64=uint64_t;
struct TDataPartition {
    ui32 Offset;
    ui32 Size;

    TDataPartition(ui32 offset = 0,
                   ui32 size = 0)
        : Offset(offset)
        , Size(size)
    {
    }
};

namespace NKernel {
    template <class T>
    __global__ void ZeroSegmentStartsImpl(const ui32* flags, ui32 flagMask, ui32 size, T* output) {
        const ui32 tid = blockIdx.x * blockDim.x + threadIdx.x;
        if (tid < size) {
            bool segmentStart = flags[tid] & flagMask;
            if (segmentStart) {
                output[tid] = 0;
            }
        }
    }

template __global__ void ZeroSegmentStartsImpl<ui32>(const ui32*,ui32,ui32,ui32*);
}
