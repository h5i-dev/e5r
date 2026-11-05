"""Concrete direct-edit experiment; no formal acceptance claimed by GPU tests."""
from pathlib import Path
import fcntl,hashlib,importlib.util,json,os,subprocess,sys,time
import numpy as np
import cupy as cp
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('timing',D.parent/'verified-packing/benchmark.py')
timing=importlib.util.module_from_spec(spec);sys.path.insert(0,str(D.parent/'verified-packing'));spec.loader.exec_module(timing)

def functions():
 mods={name:cp.RawModule(path=str(D/(name+'.ptx'))) for name in ['original','edited','edited64']}
 f={name:m.get_function('stencil17') for name,m in mods.items()}
 mod=cp.RawModule(code=(D/'matching.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'))
 f['matching_cuda']=mod.get_function('matching17')
 f['matching64_cuda']=mod.get_function('matching64')
 return f

def launch_items(name,n):
 if name in ['original','tiled','tiled_cuda']:return n
 if name in ['paired2','scalar2','paired2_cuda','scalar2_cuda']:return (n+1)//2
 return (n+3)//4

def await_gpu_idle():
 # A previous lock holder can close its file before CUDA context teardown.
 # Wait before launching anything; never bypass the foreign-process check.
 for attempt in range(40):
  try:return timing.uncontended()
  except RuntimeError:
   if attempt==39:raise
   time.sleep(.25)

def test():
 timing.uncontended();f=functions();rng=np.random.default_rng(1717);count=0
 for n in list(range(21))+[31,32,33,127,128,129,255,256,257,511,512,513,1023,1024,1025,8193]:
  timing.uncontended()
  patterns=[np.zeros(n+16,dtype=np.uint32),np.full(n+16,0xffffffff,dtype=np.uint32),
   np.arange(n+16,dtype=np.uint32),rng.integers(0,2**32,size=n+16,dtype=np.uint32)]
  for a in patterns:
   expected=np.convolve(a.astype(np.uint64),np.ones(17,dtype=np.uint64),'valid').astype(np.uint32) if n else np.empty(0,dtype=np.uint32)
   for offset in range(4):
    storage=cp.empty(n+20,dtype=cp.uint32);x=storage[offset:offset+n+16];x.set(a)
    for name,kernel in f.items():
     for block in [32,128,256]:
      backing=cp.full(n+12,0xa5a5a5a5,dtype=cp.uint32);y=backing[4+offset:4+offset+n]
      size=launch_items(name,n)
      kernel((max(1,(size+block-1)//block+1),),(block,),(x,y,np.uint32(n)))
      np.testing.assert_array_equal(y.get(),expected)
      np.testing.assert_array_equal(backing[:4+offset].get(),0xa5a5a5a5)
      np.testing.assert_array_equal(backing[4+offset+n:].get(),0xa5a5a5a5)
      np.testing.assert_array_equal(x.get(),a);count+=1
 return dict(cases=count,seed=1717,alignment='input and output offsets 0/4/8/12 bytes; all only 4-byte alignment',
  ptx_sha256={name:hashlib.sha256((D/(name+'.ptx')).read_bytes()).hexdigest() for name in ['original','edited','edited64']},
  foreign_processes_observed=False,lock='/mnt/scratch/e5r-gpu-benchmark.lock')

def bench():
 timing.uncontended();f=functions();rng=np.random.default_rng(1717);rows=[]
 for out in [32,256,4096,65536,1048576,16777216,134217728]:
  n=out//4;x=cp.asarray(rng.integers(0,2**32,size=n+16,dtype=np.uint32));y=cp.empty(n,dtype=cp.uint32)
  wide=cp.concatenate([cp.zeros(1,dtype=cp.uint64),cp.cumsum(x,dtype=cp.uint64)])
  expected=(wide[17:]-wide[:-17]).astype(cp.uint32)
  for name,kernel in f.items():
   size=n if name=='original' else (n+3)//4
   for block in [128,256,512]:
    def run():kernel(((size+block-1)//block,),(block,),(x,y,np.uint32(n)))
    run();cp.testing.assert_array_equal(y,expected)
    for graph in ([True,False] if block==256 else [True]):
     result=timing.measure(run,graph)
     rows.append(dict(output_bytes=out,name=name,block=block,grid=(size+block-1)//block,graph=graph,
      logical_GBps=(x.nbytes+y.nbytes)/result['median_us']/1000,**result))
     print(out,name,block,'graph' if graph else 'events',round(result['median_us'],4),flush=True)
  (D/'results/performance.json').write_text(json.dumps(dict(metadata=dict(
   matching_cuda_sha256=hashlib.sha256((D/'matching.cu').read_bytes()).hexdigest(),
   gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip(),
   cupy=cp.__version__,numpy=np.__version__,nvcc=subprocess.check_output(['nvcc','--version'],text=True),
   ptx_sha256={name:hashlib.sha256((D/(name+'.ptx')).read_bytes()).hexdigest() for name in ['original','edited','edited64']},
   lock='/mnt/scratch/e5r-gpu-benchmark.lock',foreign_processes_observed=False,seed=1717),rows=rows),indent=2)+'\n')

if __name__=='__main__':
 with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  await_gpu_idle()
  if len(sys.argv)>1 and sys.argv[1]=='benchmark':bench()
  else:
   result=test();(D/'results/correctness.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
