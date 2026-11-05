"""All predeclared shapes; use existing independently authored timing harness."""
from pathlib import Path
import fcntl, hashlib, importlib.util, json, math, os, platform, statistics, subprocess, sys
import numpy as np
import cupy as cp
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('packing_benchmark',D.parent/'verified-packing/benchmark.py')
harness=importlib.util.module_from_spec(spec)
sys.path.insert(0,str(D.parent/'verified-packing'));spec.loader.exec_module(harness)


def main():
    harness.uncontended()
    modules={name:cp.RawModule(path=str(D/(name+'.ptx'))) for name in ('original','optimized')}
    funcs={name:m.get_function('unpack4') for name,m in modules.items()}
    matching=cp.RawModule(code=(D/'matching.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'))
    funcs['matching_cuda']=matching.get_function('matching')
    meta=dict(gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version,memory.total,clocks.sm,clocks.mem','--format=csv,noheader'],text=True).strip(),
        cupy=cp.__version__,numpy=np.__version__,python=platform.python_version(),
        nvcc=subprocess.check_output(['nvcc','--version'],text=True),
        runtime=cp.cuda.runtime.runtimeGetVersion(),driver=cp.cuda.runtime.driverGetVersion(),
        ptx_sha256={name:hashlib.sha256((D/(name+'.ptx')).read_bytes()).hexdigest() for name in modules},
        matching_cuda_sha256=hashlib.sha256((D/'matching.cu').read_bytes()).hexdigest(),
        protocol_sha256=hashlib.sha256((D/'PROTOCOL.md').read_bytes()).hexdigest(),
        lock='/mnt/scratch/e5r-gpu-benchmark.lock',seed=6041,block=256,repeats=7,
        foreign_processes_observed=False)
    rng=np.random.default_rng(6041);rows=[]
    for out_bytes in [32,256,4096,65536,1048576,16777216,134217728]:
        n=out_bytes//4;grid=(n+255)//256
        x=cp.asarray(rng.integers(0,2**32,size=n//8,dtype=np.uint32));y=cp.empty(n,dtype=np.uint32)
        expected=cp.unpackbits(x.view(cp.uint8),bitorder='little')
        for name,kernel in funcs.items():
            def launch():kernel((grid,),(256,),(x,y,np.uint32(n)))
            launch();cp.testing.assert_array_equal(y.view(cp.uint8),expected)
            for graph in (False,True):
                row=dict(output_bytes=out_bytes,input_bytes=x.nbytes,n=n,grid=grid,block=256,
                    implementation=name,graph=graph,**harness.measure(launch,graph))
                row['logical_GBps']=(x.nbytes+y.nbytes)/row['median_us']/1000
                rows.append(row)
                print(out_bytes,name,'graph' if graph else 'events',round(row['median_us'],4),flush=True)
        (D/'results/performance.json').write_text(json.dumps(dict(metadata=meta,rows=rows),indent=2)+'\n')
    harness.uncontended()

if __name__=='__main__':
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);main()
