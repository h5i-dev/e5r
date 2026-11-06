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
    template <ui32 BLOCK_SIZE>
    __global__ void ComputeGroupIdsImpl(const ui32* qSizes, const ui32* qOffsets, ui32 offsetsBias, int qCount, ui32* dst) {
        const int queriesPerBlock = BLOCK_SIZE / 32;
        const int localQid = threadIdx.x / 32;
        const int qid = blockIdx.x * queriesPerBlock + localQid;
        ui32 writeOffset = qid < qCount ? (qOffsets[qid] - offsetsBias) : 0;
        dst += writeOffset;

        const int x = threadIdx.x & 31;
        const int querySize = qid < qCount ? qSizes[qid] : 0;

        for (int i = x; i < querySize; i += 32) {
            dst[i] = qid;
        }
    }

template __global__ void ComputeGroupIdsImpl<128>(const ui32*,const ui32*,ui32,int,ui32*);
}
