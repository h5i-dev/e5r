#include <cupy/complex.cuh>
#include <cupy/carray.cuh>
#include <cupy/atomics.cuh>
#include <cupy/math_constants.h>

    typedef unsigned char T;

    
    extern "C" __global__ void cupy_unpackbits_big(const CArray<unsigned char, 1, 1, 1> a, CArray<unsigned char, 1, 1, 1> _raw_unpacked, CIndexer<1, 1> _ind) {
      ;
      #pragma unroll 1
      CUPY_FOR(i, _ind.size()) {
        _ind.set(i);
        T &unpacked = _raw_unpacked[_ind.get()];
unpacked = (a[i / 8] >> (7 - i % 8)) & 1;;
      }
      ;
    }
    