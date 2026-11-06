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
    __global__ void ZeroPartitions(TDataPartition* __restrict parts, ui32 partCount)
    {
        ui32 i = blockIdx.x * blockDim.x + threadIdx.x;
        while (i < partCount) {
            parts[i].Size = 0;
            parts[i].Offset = 0;
            i += blockDim.x * gridDim.x;
        }
    }


}
