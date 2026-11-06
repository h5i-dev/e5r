#include <cupy/complex.cuh>
#include <cupy/carray.cuh>
#include <cupy/atomics.cuh>
#include <cupy/math_constants.h>

    typedef unsigned char T;

    
    extern "C" __global__ void cupy_packbits_big(const CArray<unsigned char, 1, 1, 1> a, const int a_size, CArray<unsigned char, 1, 1, 1> _raw_packed, CIndexer<1, 1> _ind) {
      ;
      #pragma unroll 1
      CUPY_FOR(i, _ind.size()) {
        _ind.set(i);
        unsigned char &packed = _raw_packed[_ind.get()];
for (int j = 0; j < 8; ++j) {
                    int k = i * 8 + j;
                    int bit = k < a_size && a[k] != 0;
                    packed |= bit << (7 - j);
                };
      }
      ;
    }
    