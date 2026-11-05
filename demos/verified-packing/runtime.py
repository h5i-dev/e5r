"""Restricted, allocation-free packing launches.
Only unpack has an accepted proof; pack/threshold remain experimental.
"""
from pathlib import Path
import cupy as cp
import numpy as np
D=Path(__file__).resolve().parent

class Packing:
    def __init__(self):
        self.modules={op: cp.RawModule(path=str(D/f'{op}.ptx')) for op in ('pack','unpack','threshold')}
        self.kernels={op: mod.get_function(op) for op,mod in self.modules.items()}
    def run(self,op,x,y):
        if op not in self.kernels: raise ValueError('unsupported operation')
        if x.dtype != cp.uint8 or y.dtype != cp.uint8: raise TypeError('uint8 required')
        if not x.flags.c_contiguous or not y.flags.c_contiguous: raise ValueError('contiguous buffers required')
        unit=4 if op=='unpack' else 32
        if x.size % unit: raise ValueError('partial groups are outside the proved subset')
        if y.size != (x.size*8 if op=='unpack' else x.size//8): raise ValueError('wrong output size')
        if x.data.ptr%4 or y.data.ptr%4: raise ValueError('4-byte alignment required')
        if x.size and max(x.data.ptr,y.data.ptr) < min(x.data.ptr+x.nbytes,y.data.ptr+y.nbytes):
            raise ValueError('overlapping input/output')
        n=x.size*2 if op=='unpack' else x.size//unit
        if n>2**31: raise ValueError('launch outside proved index range')
        if n:
            blocks=(n+255)//256
            if blocks*256>2**31: raise ValueError('launch outside proved index range')
            self.kernels[op]((blocks,),(256,),(x,y,np.uint32(n)))
