"""Capture ordinary CuPy API compilation; separately retain optimized PTX."""
from pathlib import Path
import fcntl,hashlib,inspect,json,os,subprocess
import cupy as cp
from cupy.cuda import compiler
from cupy._binary import packing
D=Path(__file__).resolve().parent

def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    lock=open('/mnt/scratch/e5r-gpu-benchmark.lock','w');fcntl.flock(lock,fcntl.LOCK_EX)
    snap=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],text=True).strip()
    if snap:raise RuntimeError('Foreign GPU process '+snap)
    original=compiler.compile_using_nvrtc
    captures=[]
    def capture(source,options=(),arch=None,filename='kern.cu',name_expressions=None,log_stream=None,cache_in_memory=False,jitify=False):
        binary,mapping=original(source,options,arch,filename,name_expressions,log_stream,cache_in_memory,jitify)
        if 'cupy_packbits_big' in source or 'cupy_unpackbits_big' in source:
            name='unpackbits' if 'cupy_unpackbits_big' in source else 'packbits'
            dest=D/name;dest.mkdir(exist_ok=True)
            (dest/'original.cu').write_text(source)
            (dest/'normal.cubin').write_bytes(binary)
            # Same generated source and compiler options; retention changes target
            # from sm_86 cubin to compute_86 PTX, with default optimization intact.
            archopt,method=compiler._get_arch_for_options_for_nvrtc(arch)
            opts=options+(archopt.replace('sm_','compute_'),'--device-as-default-execution-space')
            prog=compiler._NVRTCProgram(source,'frozen.cu',method='ptx')
            ptx,_=prog.compile(opts,None)
            (dest/'original.ptx').write_bytes(ptx)
            captures.append(dict(id='cupy/'+name,options=list(options),normal_arch=archopt,ptx_options=list(opts),
                hashes={p.name:h(p) for p in dest.iterdir() if p.is_file()}))
        return binary,mapping
    compiler.compile_using_nvrtc=capture
    x=cp.arange(8192,dtype=cp.uint8)
    cp.packbits(x);cp.unpackbits(x);cp.cuda.get_current_stream().synchronize()
    src=Path(inspect.getsourcefile(packing));(D/'packing.py').write_bytes(src.read_bytes())
    checkout=Path('/mnt/scratch/e5r-oss-ptx/screen/cupy')
    upstream=subprocess.check_output(['git','-C',str(checkout),'show','v13.6.0:cupy/_binary/packing.py'])
    assert upstream==src.read_bytes()
    (D/'LICENSE').write_bytes(subprocess.check_output(['git','-C',str(checkout),'show','v13.6.0:LICENSE']))
    data=dict(repository='https://github.com/cupy/cupy',commit='25e552d5d679dcdc6f7cc3d81310a9b265463137',license='MIT',source='cupy/_binary/packing.py',cupy=cp.__version__,
        nvrtc=compiler._get_nvrtc_version(),source_sha256=h(D/'packing.py'),kernels=captures,
        adaptation='No upstream body changes. Capture normal API NVRTC cubin and separately emit optimized PTX from identical generated source/options. API ordinary cubin remains strongest baseline.',
        dispatch='packbits/unpackbits default big order, uint8 contiguous; ElementwiseKernel block128 grid-stride normal launch',
        domain='Contiguous uint8 arrays, default big bitorder; 1D nonaliasing arrays, normal launch; packbits output initialized to zero by normal API.',
        predeclared_sizes=[1,7,8,31,128,1024,65536,1048576,4194304,16777216],
        success='>=1.10x geometric mean kernel latency over 65536..16777216 vs normal cubin, plus strongest matching tuned baseline; report every shape/regression',
        proof_status='not attempted; freeze only')
    assert len(captures)==2,captures
    (D/'freeze.json').write_text(json.dumps(data,indent=2)+'\n')
    print('Frozen',[(r['id'],r['hashes']['original.ptx']) for r in captures])
if __name__=='__main__':main()
