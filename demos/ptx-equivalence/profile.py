"""A single selected kernel, for lock-wrapped ncu diagnostic runs."""
from pathlib import Path
import os,sys
import cupy as cp
import numpy as np
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent/'verified-packing'))
from benchmark import uncontended
uncontended()
name=sys.argv[1];size=int(sys.argv[2]);n=size//4
if name in ['original','optimized']:
    module=cp.RawModule(path=str(D/(name+'.ptx')));fn=module.get_function('unpack4')
elif name=='matching':
    module=cp.RawModule(code=(D/'matching.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));fn=module.get_function('matching')
else:
    module=cp.RawModule(code=(D/'diagnostic.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));fn=module.get_function(name)
x=cp.ones(n if name=='copy_rw' else n//8,dtype=cp.uint32);y=cp.empty(n,dtype=cp.uint32)
args=(y,np.uint32(n)) if name=='write_only' else (x,y,np.uint32(n))
for _ in range(11):fn(((n+255)//256,),(256,),args)
cp.cuda.get_current_stream().synchronize();uncontended()
