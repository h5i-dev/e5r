"""Coalesced u64 input loads, with independent input/output alignment tests."""
import fcntl
import sys
import cupy as cp
import coalesced as run


def functions():
    mods={name:cp.RawModule(path=str(run.D/(name+'.ptx'))) for name in run.PTX}
    result={name:mod.get_function('stencil17') for name,mod in mods.items()}
    old=cp.RawModule(code=(run.D/'paired2-pointer.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'))
    result['paired2_cuda']=old.get_function('paired2_cuda')
    mod=cp.RawModule(code=(run.D/'wide-input.cu').read_text(),backend='nvcc',options=('-O3','-arch=sm_86'))
    result['wide_input_cuda']=mod.get_function('wide_input_cuda')
    return result


if __name__=='__main__':
    run.PTX=['original','paired2','wide-input']
    run.STEM='wide-input'
    run.CUDA_SOURCES=['paired2-pointer.cu','wide-input.cu']
    run.SCOPE='aligned full pairs use nine u64 input loads and paired output stores; independent 4-byte input/output alignments and odd tails retain scalar fallbacks'
    run.functions=functions
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        run.experiment.await_gpu_idle()
        if len(sys.argv)>1 and sys.argv[1]=='benchmark':run.bench()
        else:run.test(independent_offsets=True)
