#include <cupy/complex.cuh>
#include <cupy/carray.cuh>
#include <cupy/atomics.cuh>
#include <cupy/math_constants.h>

    typedef int T;

    
    extern "C" __global__ void cupy_tri(const int m, const int k, CArray<int, 1, 1, 1> _raw_out, CIndexer<1, 1> _ind) {
      ;
      #pragma unroll 1
      CUPY_FOR(i, _ind.size()) {
        _ind.set(i);
        T &out = _raw_out[_ind.get()];

    int row = i / m;
    int col = i % m;
    out = (col <= row + k);
    ;
      }
      ;
    }
    