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
    __global__ void FillQueryEndMaskImpl(const ui32* __restrict qids, const ui32* __restrict docs, ui32 docCount, ui32* __restrict masks) {
        const ui32 i = blockIdx.x * blockDim.x + threadIdx.x;
        if (i < docCount) {
            ui32 idx = docs[i];
            const ui32 qid = qids[idx];
            const ui32 nextDoc = i + 1 < docCount ? docs[i + 1] : static_cast<ui32>(-1);
            const ui32 isEnd = i + 1 < docCount ? qid != qids[nextDoc] : 1;
            masks[i] = isEnd;
        }
    }


}
