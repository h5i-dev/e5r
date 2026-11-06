#include <cupy/complex.cuh>
#include <cupy/carray.cuh>
#include <cupy/atomics.cuh>
#include <cupy/math_constants.h>

    typedef bool Q;
typedef int S;
typedef int T;

    
    extern "C" __global__ void cupy_putmask_kernel(const CArray<bool, 1, 1, 1> _raw_mask, const CArray<int, 1, 1, 1> values, const unsigned long long len_vals, CArray<int, 1, 1, 1> _raw_out, CIndexer<1, 1> _ind) {
      ;
      #pragma unroll 1
      CUPY_FOR(i, _ind.size()) {
        _ind.set(i);
        const Q &mask = _raw_mask[_ind.get()];
T &out = _raw_out[_ind.get()];

    if (mask) out = (T) values[i % len_vals];
    ;
      }
      ;
    }
    