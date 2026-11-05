"""All predeclared shapes, allocation-free device and graph measurements.
Run under the common lock; refuse foreign GPU compute processes throughout.
"""
import fcntl, hashlib, json, os, platform, statistics, subprocess, time
import numpy as np
import cupy as cp
from cupy._binary.packing import _packbits_kernel, _unpackbits_kernel
from runtime import Packing,D

SIZES=[32,256,4096,65536,1048576,16777216,134217728]

def gpu_snapshot():
    return subprocess.check_output(['nvidia-smi','--query-compute-apps=pid,process_name,used_memory','--format=csv,noheader'],text=True).strip()
def uncontended():
    snap=gpu_snapshot()
    for row in snap.splitlines():
        if row and int(row.split(',')[0])!=os.getpid():
            raise RuntimeError('foreign GPU process; timing refused: '+snap)
    return snap

def measure(fn,graph=False):
    stream=cp.cuda.get_current_stream()
    for _ in range(20):fn()
    stream.synchronize()
    if graph:
        # Non-default stream capture; buffers and compiled kernels already exist.
        with cp.cuda.Stream(non_blocking=True) as capture:
            capture.begin_capture()
            for _ in range(100):fn()
            g=capture.end_capture()
        fn=lambda:g.launch(stream)
        divisor=100
        iterations=10
    else:
        divisor=1;iterations=100
    result=[];host=[]
    for _ in range(7):
        uncontended();a=cp.cuda.Event();b=cp.cuda.Event()
        t=time.perf_counter_ns();a.record(stream)
        for _ in range(iterations):fn()
        b.record(stream);b.synchronize()
        host.append((time.perf_counter_ns()-t)/1000/iterations/divisor)
        result.append(cp.cuda.get_elapsed_time(a,b)*1000/iterations/divisor)
    return dict(device_us=result,host_us=host,median_us=statistics.median(result),
        min_us=min(result),max_us=max(result),stdev_us=statistics.stdev(result),
        host_median_us=statistics.median(host),launches_per_repeat=iterations*divisor)

def main():
    uncontended();rt=Packing()
    baseline=cp.RawModule(code=(D/'baseline.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'))
    funcs={op:baseline.get_function('coalesced_unpack' if op=='unpack' else 'ballot_'+op) for op in rt.kernels}
    meta=dict(gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version,memory.total,clocks.sm,clocks.mem','--format=csv,noheader'],text=True).strip(),
        cupy=cp.__version__,numpy=np.__version__,python=platform.python_version(),
        nvcc=subprocess.check_output(['nvcc','--version'],text=True),
        runtime=cp.cuda.runtime.runtimeGetVersion(),driver=cp.cuda.runtime.driverGetVersion(),
        ptx_sha256={op:hashlib.sha256((D/f'{op}.ptx').read_bytes()).hexdigest() for op in rt.kernels},
        lock='/mnt/scratch/e5r-gpu-benchmark.lock',seed=6041,block=256,cuda_grid_cap=4096,scope='SPEC.md',
        repeats=7,foreign_processes_observed=False)
    grouped={op:baseline.get_function('grouped_'+op) for op in rt.kernels}
    word_unpack=baseline.get_function('word_unpack')
    rows=[];rng=np.random.default_rng(6041)
    for n in SIZES:
        for op in rt.kernels:
            length=n//8 if op=='unpack' else n
            x=cp.asarray(rng.integers(0,256,size=length,dtype=np.uint8));y=cp.empty(n if op=='unpack' else n//8,dtype=cp.uint8)
            pred=cp.empty(length,dtype=cp.bool_)
            def oss():
                if op=='unpack':_unpackbits_kernel['little'](x,y)
                else:
                    y.fill(0)
                    if op=='threshold':cp.greater(x,127,out=pred);a=pred
                    else:a=x
                    _packbits_kernel['little'](a,np.int32(length),y)
            def cuda(): funcs[op]((min(4096,(n+255)//256),),(256,),(x,y,np.uint32(n)))
            count=n//4 if op=='unpack' else n//32
            def cuda_grouped():grouped[op](((n//32+255)//256,),(256,),(x,y,np.uint32(n//32)))
            def ptx():rt.kernels[op](((count+255)//256,),(256,),(x,y,np.uint32(count)))
            rt.run(op,x,y)
            calls={'ptx':ptx,'cupy_preallocated':oss,'cuda_grid_stride':cuda,'cuda_grouped':cuda_grouped}
            if op=='unpack':
                calls['cuda_word']=lambda:word_unpack(((count+255)//256,),(256,),(x,y,np.uint32(count)))
            expected=cp.unpackbits(x,bitorder='little') if op=='unpack' else cp.packbits(x>127 if op=='threshold' else x,bitorder='little')
            for name,fn in calls.items():
                fn();cp.testing.assert_array_equal(y,expected)
                for graph in (False,True):
                    row=dict(unpacked_bytes=n,operation=op,implementation=name,graph=graph,
                        input_bytes=x.nbytes,output_bytes=y.nbytes,
                        **measure(fn,graph))
                    row['logical_GBps']=(x.nbytes+y.nbytes)/row['median_us']/1000
                    rows.append(row)
                    print(op,n,name,'graph' if graph else 'events',round(row['median_us'],3),flush=True)
            # Public API timing includes documented allocation/initialization.
            api=(lambda:cp.unpackbits(x,bitorder='little')) if op=='unpack' else (lambda:cp.packbits(x>127 if op=='threshold' else x,bitorder='little'))
            rows.append(dict(unpacked_bytes=n,operation=op,implementation='cupy_public_api',graph=False,**measure(api)))
            (D/'results/performance.json').write_text(json.dumps(dict(metadata=meta,rows=rows),indent=2)+'\n')
    uncontended()

if __name__=='__main__':
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);main()
