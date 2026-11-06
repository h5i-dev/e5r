#include <cupy/complex.cuh>
#include <cupy/carray.cuh>
#include <cupy/atomics.cuh>
#include <cupy/math_constants.h>

    typedef int T;

    
    extern "C" __global__ void cupy_resize(const CArray<int, 1, 1, 1> x, const long long size, CArray<int, 1, 1, 1> _raw_y, CIndexer<1, 1> _ind) {
      ;
      #pragma unroll 1
      CUPY_FOR(i, _ind.size()) {
        _ind.set(i);
        T &y = _raw_y[_ind.get()];
y = x[i % size];
      }
      ;
    }
    