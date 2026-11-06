#include <cupy/complex.cuh>
#include <cupy/carray.cuh>
#include <cupy/atomics.cuh>
#include <cupy/math_constants.h>

    typedef int T;

    
    extern "C" __global__ void cupy_flatiter_getitem_slice(const CArray<int, 1, 1, 1> a, const long long start, const long long step, CArray<int, 1, 1, 1> _raw_o, CIndexer<1, 1> _ind) {
      ;
      #pragma unroll 1
      CUPY_FOR(i, _ind.size()) {
        _ind.set(i);
        T &o = _raw_o[_ind.get()];
o = a[start + i * step];
      }
      ;
    }
    