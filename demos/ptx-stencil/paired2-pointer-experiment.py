"""Two adjacent outputs: useful rolling reuse and contiguous aligned u64 stores."""
import fcntl
import sys
import cupy as cp
import coalesced as run


def functions():
    mods={name:cp.RawModule(path=str(run.D/(name+'.ptx'))) for name in run.PTX}
    result={name:mod.get_function('stencil17') for name,mod in mods.items()}
    mod=cp.RawModule(code=(run.D/'paired2-pointer.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'))
    for name in ['paired2_cuda','scalar2_cuda']:result[name]=mod.get_function(name)
    return result


if __name__=='__main__':
    run.PTX=['original','paired2','scalar2']
    run.STEM='paired2-pointer'
    run.CUDA_SOURCES=['paired2-pointer.cu']
    run.SCOPE='same direct PTX; matching CUDA hoists input/output pointers to avoid repeated u32 index overflow address work'
    run.functions=functions
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        run.experiment.await_gpu_idle()
        if len(sys.argv)>1 and sys.argv[1]=='benchmark':run.bench()
        else:run.test()
