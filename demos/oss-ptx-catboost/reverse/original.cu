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
    template <typename T>
    __global__ void ReverseImpl(T *data, ui64 size) {
        ui64 i = (ui64)blockIdx.x * blockDim.x + threadIdx.x;
        ui64 half = size / 2;
        while (i < half) {
            T a = data[i];
            T b = data[size - i - 1];
            data[i] = b;
            data[size - i - 1] = a;
            i += (ui64)gridDim.x * blockDim.x;
        }
    }

template __global__ void ReverseImpl<ui32>(ui32*,ui64);
}
