"""Real OSS PTX differential tests and allocation-free, locked measurements."""
from pathlib import Path
import fcntl, hashlib, json, os, platform, statistics, subprocess, sys
import numpy as np
import cupy as cp
D=Path(__file__).resolve().parent
SIZES=[0,1,31,32,255,256,511,512,513,4096,65536,1048576,4194304,16777216,33554432]
SYMBOL='_Z9incKernelPiS_ii'

def uncontended():
    snap=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid,process_name,used_memory','--format=csv,noheader'],text=True).strip()
    for line in snap.splitlines():
        if line and int(line.split(',')[0])!=os.getpid():
            raise RuntimeError('Foreign GPU process, refusing run: '+snap)
    return snap

def save(name,value):
    (D/'results'/name).write_text(json.dumps(value,indent=2)+'\n')

def metadata():
    return dict(gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version,memory.total,clocks.sm,clocks.mem','--format=csv,noheader'],text=True).strip(),
        python=platform.python_version(),cupy=cp.__version__,numpy=np.__version__,
        runtime=cp.cuda.runtime.runtimeGetVersion(),driver=cp.cuda.runtime.driverGetVersion(),
        nvcc=subprocess.check_output(['nvcc','--version'],text=True),
        aot_sha256={k:hashlib.sha256((Path(os.environ.get('E5R_OSS_SCRATCH','/mnt/scratch/e5r-oss-ptx'))/p).read_bytes()).hexdigest() for k,p in {'original_aot':'upstream-build/simpleMultiCopy.sm_86.cubin','edited_aot':'edited.cubin','tuned_aot':'tuned.cubin'}.items()},
        ptx_sha256={k:hashlib.sha256((D/f'{k}.ptx').read_bytes()).hexdigest() for k in ('original','edited','tuned')},
        lock='/mnt/scratch/e5r-gpu-benchmark.lock',foreign_processes_observed=False,seed=936,inner_reps=5,
        proof_status='consult results/proof.json; GPU runs are tests, not proofs')

def kernels():
    mods={k:cp.RawModule(path=str(D/f'{k}.ptx')) for k in ('original','edited','tuned')}
    for k,path in {'original_aot':'upstream-build/simpleMultiCopy.sm_86.cubin','edited_aot':'edited.cubin','tuned_aot':'tuned.cubin'}.items():
        mods[k]=cp.RawModule(path=str(Path(os.environ.get('E5R_OSS_SCRATCH','/mnt/scratch/e5r-oss-ptx'))/path))
    return mods,{k:m.get_function(SYMBOL) for k,m in mods.items()}

def test():
    uncontended()
    binary=Path('/mnt/scratch/e5r-oss-ptx/upstream-build/simpleMultiCopy')
    if not binary.exists():
        raise FileNotFoundError('Run build-upstream.sh before GPU validation: '+str(binary))
    if binary.exists():
        r=subprocess.run([str(binary)],text=True,capture_output=True,timeout=120)
        (D/'results/upstream-run.txt').write_text(r.stdout+r.stderr)
        assert r.returncode==0,(r.returncode,r.stdout,r.stderr)
    uncontended()
    mods,funcs=kernels();rng=np.random.default_rng(936);count=0
    for n in SIZES[:-2]+[8193]:
        patterns=[np.zeros(n,dtype=np.uint32),np.full(n,0xffffffff,dtype=np.uint32),
            np.resize(np.array([0x7fffffff,0x80000000,0,1,0xffffffff,0xaaaaaaaa,0x55555555],np.uint32),n),
            rng.integers(0,2**32,n,dtype=np.uint32)]
        for a in patterns:
            expected=np.add(a,np.uint32(1),dtype=np.uint32)
            for block in (32,256,512):
                for offset in (1,4):
                    xs=cp.full(n+offset+8,np.uint32(0xa5a5a5a5));x=xs[offset:offset+n]
                    if n:x.set(a)
                    for name,fn in funcs.items():
                        ys=cp.full(n+offset+8,np.uint32(0xdeadbeef));y=ys[offset:offset+n]
                        fn((max(1,(n+block-1)//block+1),),(block,),(y,x,np.int32(n),np.int32(5)))
                        np.testing.assert_array_equal(y.get(),expected)
                        np.testing.assert_array_equal(x.get(),a)
                        np.testing.assert_array_equal(ys[:offset].get(),0xdeadbeef)
                        np.testing.assert_array_equal(ys[offset+n:].get(),0xdeadbeef)
                        np.testing.assert_array_equal(xs[:offset].get(),0xa5a5a5a5)
                        np.testing.assert_array_equal(xs[offset+n:].get(),0xa5a5a5a5)
                        count+=1
            uncontended()
    # Concrete counterexample to extending theorem to aliased allocations.
    alias=[]
    for name in ('original','edited'):
        x=cp.zeros(32,np.uint32);funcs[name]((1,),(32,),(x,x,np.int32(32),np.int32(5)))
        alias.append(int(x[0].get()))
    assert alias==[5,1],alias
    save('correctness.json',dict(metadata=metadata(),cases=count,all_passed=True,canaries=True,
        input_preserved=True,word_offset_buffers=[1,4],blocks=[32,256,512],
        alias_outside_domain_witness=dict(original=alias[0],edited=alias[1]),upstream_exit=0))
    print('correctness cases',count,flush=True)

def bench():
    uncontended();mods,funcs=kernels();rng=np.random.default_rng(936)
    rows=[];meta=metadata();meta.update(block=512,repeats=7,warmups=20,graph_nodes=64,graph_replays=4,
        l2_bytes=cp.cuda.runtime.getDeviceProperties(0).get('l2CacheSize'),scope='kernel only, no sample/API/end-to-end claim')
    for n in SIZES[1:]:
        for regime in ('hot','rotating') if n>=65536 else ('hot',):
            ring=1 if regime=='hot' else max(2,min(64,(128*1024**2+8*n-1)//(8*n)))
            xs=[cp.arange(n,dtype=cp.uint32) for _ in range(ring)]
            ys=[cp.empty(n,cp.uint32) for _ in range(ring)]
            graphs={};stream=cp.cuda.Stream(non_blocking=True)
            grid=(n+511)//512
            for name,fn in funcs.items():
                def launch(j):fn((grid,),(512,),(ys[j%ring],xs[j%ring],np.int32(n),np.int32(5)),stream=stream)
                for j in range(20):launch(j)
                stream.synchronize()
                with stream:
                    stream.begin_capture()
                    for j in range(64):launch(j)
                    graphs[name]=stream.end_capture()
            samples={name:[] for name in funcs};orders=[]
            for repeat in range(7):
                order=list(funcs);rng.shuffle(order);orders.append(order)
                for name in order:
                    uncontended()
                    a=cp.cuda.Event();b=cp.cuda.Event();a.record(stream)
                    for _ in range(4):graphs[name].launch(stream)
                    b.record(stream);b.synchronize()
                    samples[name].append(cp.cuda.get_elapsed_time(a,b)*1000/256)
            for name,values in samples.items():
                rows.append(dict(n=n,regime=regime,implementation=name,grid=grid,block=512,
                    ring_buffers=ring,total_buffer_bytes=ring*n*8,device_us=values,
                    median_us=statistics.median(values),stdev_us=statistics.stdev(values),
                    min_us=min(values),max_us=max(values),variant_orders=orders))
            save('performance.json',dict(metadata=meta,rows=rows))
            print(n,regime,{k:round(statistics.median(v),3) for k,v in samples.items()},flush=True)
            del graphs,xs,ys
            cp.get_default_memory_pool().free_all_blocks()
    uncontended()

if __name__=='__main__':
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        {'test':test,'benchmark':bench}[sys.argv[1]]()
