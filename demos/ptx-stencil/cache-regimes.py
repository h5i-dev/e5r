"""Predeclared follow-up: one-MiB hot buffer versus 16 rotating buffer pairs.

This diagnoses the observed local gain, separately from the original sweep.
The rotating 32MiB working set exceeds the A10G's L2; it is not a cache flush.
"""
from pathlib import Path
import fcntl
import hashlib
import importlib.util
import json
import subprocess
import sys
import cupy as cp
import numpy as np
import experiment

D=Path(__file__).resolve().parent


def main():
    module_spec=importlib.util.spec_from_file_location('wide_branch_experiment',D/'wide-branch-experiment.py')
    module=importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(module)
    module.run.PTX=['original','paired2','wide-input','wide-branch']
    funcs=module.functions()
    n=1048576//4
    block=128
    rng=np.random.default_rng(1718)
    rows=[]
    for buffers in [1,16]:
        xs=[];ys=[];refs=[]
        for _ in range(buffers):
            a=rng.integers(0,2**32,size=n+16,dtype=np.uint32)
            prefix=np.concatenate([np.zeros(1,dtype=np.uint64),np.cumsum(a,dtype=np.uint64)])
            refs.append((prefix[17:]-prefix[:-17]).astype(np.uint32))
            xs.append(cp.asarray(a));ys.append(cp.empty(n,dtype=cp.uint32))
        for name,kernel in funcs.items():
            experiment.timing.uncontended()
            count=experiment.launch_items(name,n)
            grid=(count+block-1)//block
            for x,y,reference in zip(xs,ys,refs):
                kernel((grid,),(block,),(x,y,np.uint32(n)))
                np.testing.assert_array_equal(y.get(),reference)
            cursor=0
            def launch():
                nonlocal cursor
                index=cursor%buffers
                cursor+=1
                kernel((grid,),(block,),(xs[index],ys[index],np.uint32(n)))
            result=experiment.timing.measure(launch,graph=True)
            rows.append(dict(output_bytes=1048576,block=block,name=name,buffer_pairs=buffers,
                             working_set_bytes=sum(x.nbytes+y.nbytes for x,y in zip(xs,ys)),**result))
            print(buffers,name,round(result['median_us'],4),flush=True)
    result=dict(metadata=dict(seed=1718,lock='/mnt/scratch/e5r-gpu-benchmark.lock',
                              foreign_processes_observed=False,
                              environment=dict(gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip(),
                                               cupy=cp.__version__,numpy=np.__version__,
                                               nvcc=subprocess.check_output(['nvcc','--version'],text=True)),
                              note='Diagnostic predeclared after the original sweep: one hot buffer and 16 rotating pairs, not a forced cold-cache guarantee',
                              ptx_sha256={p:hashlib.sha256((D/(p+'.ptx')).read_bytes()).hexdigest() for p in module.run.PTX},
                              cuda_sha256={p:hashlib.sha256((D/p).read_bytes()).hexdigest() for p in ['paired2-pointer.cu','wide-input.cu']}),rows=rows)
    (D/'results/cache-regimes.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        experiment.await_gpu_idle()
        main()
