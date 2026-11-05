"""Traffic, launch geometry and resource diagnostics under the shared lock."""
from pathlib import Path
import fcntl,importlib.util,json,math,os,subprocess,sys
import cupy as cp
import numpy as np
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('timing',D.parent/'verified-packing/benchmark.py')
timing=importlib.util.module_from_spec(spec);sys.path.insert(0,str(D.parent/'verified-packing'));spec.loader.exec_module(timing)

def main():
 timing.uncontended()
 prop=cp.cuda.runtime.getDeviceProperties(0)
 resources={}
 original=cp.RawModule(path=str(D/'original.ptx')).get_function('unpack4')
 optimized=cp.RawModule(path=str(D/'optimized.ptx')).get_function('unpack4')
 matching=cp.RawModule(code=(D/'matching.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86')).get_function('matching')
 mod=cp.RawModule(code=(D/'diagnostic.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'))
 funcs={'original':original,'optimized':optimized,'matching':matching,
  **{name:mod.get_function(name) for name in ['broadcast_rw','copy_rw','write_only']}}
 for name,f in funcs.items():resources[name]=f.attributes
 rows=[]
 for size in [32,256,4096,65536,1048576,16777216,134217728]:
  n=size//4;x=cp.ones(n,dtype=cp.uint32);y=cp.empty(n,dtype=cp.uint32)
  for name,f in funcs.items():
   blocks=[64,128,256,512,1024] if name in ['original','optimized','matching'] else [256]
   for block in blocks:
    args=(y,np.uint32(n)) if name=='write_only' else (x,y,np.uint32(n))
    def run():f(((n+block-1)//block,),(block,),args)
    run()
    if name=='copy_rw' or name=='broadcast_rw' or name=='write_only':cp.testing.assert_array_equal(y,1)
    else:cp.testing.assert_array_equal(y.view(cp.uint8),cp.unpackbits(x[:n//8].view(cp.uint8),bitorder='little'))
    # Graph replay is the primary device measurement at every shape.
    result=timing.measure(run,True)
    logical=size*(2 if name=='copy_rw' else 1 if name=='write_only' else 1.125)
    rows.append(dict(output_bytes=size,name=name,block=block,graph=True,
     logical_bytes=logical,logical_GBps=logical/result['median_us']/1000,**result))
    print(size,name,block,round(result['median_us'],4),flush=True)
  (D/'optimization/results/diagnosis.json').write_text(json.dumps(dict(
   device={str(k):v for k,v in prop.items() if isinstance(v,(int,float,str))},resources=resources,
   lock='/mnt/scratch/e5r-gpu-benchmark.lock',foreign_processes_observed=False,rows=rows),indent=2)+'\n')

if __name__=='__main__':
 with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX);main()
