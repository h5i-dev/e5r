"""Capture actual CuPy API NVRTC programs without changing upstream bodies."""
from pathlib import Path
import fcntl,hashlib,json,os,subprocess
os.environ['CUPY_CACHE_DIR']='/mnt/scratch/e5r-oss-ptx/cupy-index/cache'
import cupy as cp
from cupy.cuda import compiler
D=Path(__file__).resolve().parent
ROOT=Path('/mnt/scratch/e5r-oss-ptx/screen/cupy')
TAG='25e552d5d679dcdc6f7cc3d81310a9b265463137'
TARGETS={'tri':'cupy/_creation/matrix.py','resize':'cupy/_manipulation/add_remove.py','putmask':'cupy/_indexing/insert.py','flatiter_setitem_slice':'cupy/_indexing/iterate.py','flatiter_getitem_slice':'cupy/_indexing/iterate.py'}
old=compiler._NVRTCProgram.compile
current=None
captures={}
def hook(self,options=(),log_stream=None):
 result=old(self,options,log_stream)
 if current and 'extern "C"' in self.src and 'cupy_'+current in self.src:
  dest=D/current;dest.mkdir(exist_ok=True)
  (dest/'generated.cu').write_text(self.src)
  (dest/'normal.cubin').write_bytes(result[0])
  ptxopts=tuple(o.replace('sm_86','compute_86') for o in options)
  prog=compiler._NVRTCProgram(self.src,'frozen.cu',name_expressions=self.name_expressions,method='ptx')
  ptx,mapping=old(prog,ptxopts)
  (dest/'original.ptx').write_bytes(ptx)
  src=TARGETS[current]
  original=subprocess.check_output(['git','-C',str(ROOT),'show',TAG+':'+src])
  installed=Path(cp.__file__).parent.parent/src
  assert installed.read_bytes()==original,src
  (dest/'upstream.py').write_bytes(original)
  hashes={n:hashlib.sha256((dest/n).read_bytes()).hexdigest() for n in ['generated.cu','normal.cubin','original.ptx','upstream.py']}
  meta=dict(project='CuPy',commit=TAG,tag='v13.6.0',license='MIT',source=src,normal_options=options,ptx_options=ptxopts,cupy=cp.__version__,native_method=self.method,hashes=hashes,phase='source_build_frozen',proof_accepted=False)
  (dest/'freeze.json').write_text(json.dumps(meta,indent=2)+'\n')
  captures[current]=meta
 return result
compiler._NVRTCProgram.compile=hook
with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 snap=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],text=True).strip()
 assert not snap,snap
 a=cp.arange(256,dtype=cp.int32);mask=cp.ones(65536,dtype=cp.bool_);out=cp.empty(65536,dtype=cp.int32)
 current='tri';cp.tri(256,256,dtype=cp.int32)
 current='resize';cp.resize(a,65536)
 current='putmask';cp.putmask(out,mask,a)
 current='flatiter_setitem_slice';out.flat[:]=a
 current='flatiter_getitem_slice';z=out.flat[0:65536:1]
 cp.cuda.Device().synchronize()
assert len(captures)==5,captures.keys()
(D/'LICENSE').write_bytes(subprocess.check_output(['git','-C',str(ROOT),'show',TAG+':LICENSE']))
print('frozen',list(captures))
