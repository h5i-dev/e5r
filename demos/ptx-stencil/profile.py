from pathlib import Path
import sys
import cupy as cp
import numpy as np
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent/'verified-packing'))
from benchmark import uncontended
uncontended();name=sys.argv[1];n=(int(sys.argv[2]) if len(sys.argv)>2 else 134217728)//4
block=int(sys.argv[3]) if len(sys.argv)>3 else 256
if name in ['original','edited','edited64','striped','staged','tiled','tiled4','paired2','scalar2','wide-input','wide-branch']:
 m=cp.RawModule(path=str(D/(name+'.ptx')));f=m.get_function('stencil17')
elif name in ['striped17','staged17']:
 m=cp.RawModule(code=(D/'coalesced.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));f=m.get_function(name)
elif name in ['tiled17','tiled417']:
 m=cp.RawModule(code=(D/'tiled.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));f=m.get_function(name)
elif name in ['paired2_cuda','scalar2_cuda']:
 m=cp.RawModule(code=(D/'paired2.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));f=m.get_function(name)
elif name in ['paired2_pointer_cuda','scalar2_pointer_cuda']:
 m=cp.RawModule(code=(D/'paired2-pointer.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));f=m.get_function(name.replace('_pointer',''))
elif name=='wide_input_cuda':
 m=cp.RawModule(code=(D/'wide-input.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));f=m.get_function(name)
else:
 m=cp.RawModule(code=(D/'matching.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'));f=m.get_function(name)
x=cp.ones(n+16,dtype=cp.uint32);y=cp.empty(n,dtype=cp.uint32)
count=n if name in ['original','tiled','tiled17'] else (n+1)//2 if name in ['paired2','scalar2','paired2_cuda','scalar2_cuda','paired2_pointer_cuda','scalar2_pointer_cuda','wide-input','wide-branch','wide_input_cuda'] else (n+3)//4
for _ in range(11):f(((count+block-1)//block,),(block,),(x,y,np.uint32(n)))
cp.cuda.get_current_stream().synchronize();uncontended()
