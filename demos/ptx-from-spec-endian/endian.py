"""Restricted uint32 CuPy API wrapper for the proved PTX. No timing on import."""
from functools import lru_cache
from pathlib import Path
from operator import index


@lru_cache(maxsize=None)
def _kernel(device_id):
    import cupy as cp
    path = Path(__file__).with_name('endian_xor.ptx')
    with cp.cuda.Device(device_id):
        return cp.RawModule(path=str(path)).get_function('endian_xor')


def endian_xor(x, mask, out=None):
    """Return byte-reversed native uint32 elements XOR mask, on current stream.

    x and out must be disjoint contiguous 1-D uint32 arrays on the same device.
    Launching requires externally ensuring no concurrent writer to these arrays.
    """
    import cupy as cp
    import numpy as np
    if not isinstance(x, cp.ndarray) or x.dtype != np.dtype('uint32') or x.ndim != 1 or not x.flags.c_contiguous:
        raise ValueError('x must be a contiguous 1-D native uint32 CuPy array')
    try:
        mask = index(mask)
    except TypeError as error:
        raise ValueError('mask must be an integer uint32') from error
    if not 0 <= mask < 2**32:
        raise ValueError('mask must be uint32')
    n = x.size
    if n >= 2**32:
        raise ValueError('length must fit uint32')
    if out is None:
        with x.device:
            out = cp.empty_like(x)
    if (not isinstance(out, cp.ndarray) or out.dtype != x.dtype or out.shape != x.shape
            or not out.flags.c_contiguous or out.device.id != x.device.id):
        raise ValueError('out must match x dtype, shape, contiguous layout, device')
    if (x.data.ptr % 4 or out.data.ptr % 4 or
            (n and x.data.ptr < out.data.ptr + out.nbytes and out.data.ptr < x.data.ptr + x.nbytes)):
        raise ValueError('arrays must be aligned and disjoint')
    with x.device:
        _kernel(x.device.id)((max(1, (n+255)//256),), (256,), (x, out, np.uint32(n), np.uint32(mask)))
    return out
