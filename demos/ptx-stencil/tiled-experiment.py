"""Input staging gives actual cross-thread reuse with coalesced global I/O."""
import fcntl
import sys
import cupy as cp
import coalesced as run


def functions():
    mods = {name: cp.RawModule(path=str(run.D/(name+'.ptx'))) for name in run.PTX}
    result = {name: mod.get_function('stencil17') for name, mod in mods.items()}
    mod = cp.RawModule(code=(run.D/'tiled.cu').read_text(), backend='nvcc', options=('-O3','-arch=sm_86'))
    result['tiled_cuda'] = mod.get_function('tiled17')
    result['tiled4_cuda'] = mod.get_function('tiled417')
    old = cp.RawModule(code=(run.D/'matching.cu').read_text(), backend='nvcc', options=('-O3','-arch=sm_86'))
    result['matching64_cuda'] = old.get_function('matching64')
    return result


if __name__ == '__main__':
    run.PTX = ['original','tiled','tiled4']
    run.STEM = 'tiled'
    run.CUDA_SOURCES = ['tiled.cu','matching.cu']
    run.SCOPE = 'cooperative contiguous input+halo staging, one barrier, coalesced output; 16<=block<=512; one/four outputs per thread'
    run.functions = functions
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        run.experiment.await_gpu_idle()
        if len(sys.argv)>1 and sys.argv[1]=='benchmark':
            run.bench()
        else:
            run.test()
