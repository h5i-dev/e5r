"""Locked exact CuPy ABI tests and kernel-only native/JIT/tuned timing."""
from pathlib import Path
import fcntl,json,os,statistics,subprocess,struct,hashlib
import numpy as np
import cupy as cp
D=Path(__file__).resolve().parent
SIZES=[0,1,7,8,31,128,1024,65536,1048576,4194304,16777216]
REGIME=os.environ.get("OSS_PACKING_REGIME","hot")
TUNED=r'''
extern "C" __global__ void unpack(const unsigned char* __restrict__ x, unsigned long long* __restrict__ y, unsigned n){
 for(unsigned i=blockIdx.x*blockDim.x+threadIdx.x;i<n;i+=gridDim.x*blockDim.x){
 unsigned v=x[i];unsigned long long z=0;
 #pragma unroll
 for(int j=0;j<8;j++)z|=(unsigned long long)((v>>(7-j))&1)<<(8*j);
 y[i]=z;
 }}
extern "C" __global__ void pack(const unsigned char* __restrict__ x, unsigned char* __restrict__ y, unsigned n){
 for(unsigned i=blockIdx.x*blockDim.x+threadIdx.x;i<n/8;i+=gridDim.x*blockDim.x){
 unsigned v=0;
 #pragma unroll
 for(int j=0;j<8;j++)v|=(unsigned)(x[8*i+j]!=0)<<(7-j);
 y[i]|=v;
 }}
'''
def blob(*words):return np.array(np.void(struct.pack('<'+'Q'*len(words),*words)))
def carray(x):return blob(x.data.ptr,x.size,x.size,1)
def index(n):return blob(n,0,0)
def args(k,x,y):return (carray(x),np.int32(x.size),carray(y),index(y.size)) if k=='packbits' else (carray(x),carray(y),index(y.size))
def check_foreign():
 snap=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],text=True).strip()
 assert all(int(p)==os.getpid() for p in snap.splitlines()),snap

def main():
 lock=open('/mnt/scratch/e5r-gpu-benchmark.lock','w');fcntl.flock(lock,fcntl.LOCK_EX);check_foreign()
 rng=np.random.default_rng(927)
 tuned=cp.RawModule(code=TUNED,options=('-std=c++17',));(D/'tuned.cu').write_text(TUNED)
 report=dict(gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version,clocks.sm,clocks.mem','--format=csv,noheader'],text=True).strip(),cupy=cp.__version__,repeats=7,graph_nodes=32,warmups=20,regime=REGIME,scope='kernel-only',proof='not accepted',rows=[],cases=0)
 report['hashes']={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.glob('*/*') if p.suffix in ('.ptx','.cubin')}
 for k in ('packbits','unpackbits'):
  mods={v:cp.RawModule(path=str(D/k/f)) for v,f in [('normal','normal.cubin'),('original','original.ptx'),('edited','edited.ptx')]}
  funcs={v:m.get_function('cupy_'+k+'_big') for v,m in mods.items()};funcs['tuned']=tuned.get_function('pack' if k=='packbits' else 'unpack')
  for n in SIZES:
   if k=='packbits' and n%8:continue
   out=n//8 if k=='packbits' else n*8
   host=rng.integers(0,256,n,dtype=np.uint8)
   for pattern in (host,np.zeros(n,np.uint8),np.resize(np.arange(256,dtype=np.uint8),n)):
    expected=np.packbits(pattern) if k=='packbits' else np.unpackbits(pattern)
    for offset in (0,8):
     xs=cp.full(n+offset+16,193,np.uint8);x=xs[offset:offset+n];x.set(pattern)
     ys=cp.full(out+offset+16,173,np.uint8);y=ys[offset:offset+out]
     for v,fn in funcs.items():
      y.fill(0);work=n if k=='unpackbits' and v in ('edited','tuned') else out
      a=(x,y,np.uint32(n)) if v=='tuned' else args(k,x,y)
      fn((max(1,(work+127)//128),),(128,),a)
      np.testing.assert_array_equal(y.get(),expected);np.testing.assert_array_equal(x.get(),pattern)
      np.testing.assert_array_equal(ys[:offset].get(),173);np.testing.assert_array_equal(ys[offset+out:].get(),173)
      report['cases']+=1
   ring=max(2,min(16,(128*1024**2+n+out-1)//max(1,n+out))) if REGIME=='rotating' and n>=65536 else 1
   xr=[cp.asarray(host) for _ in range(ring)];yr=[cp.zeros(out,np.uint8) for _ in range(ring)];graphs={};stream=cp.cuda.Stream(non_blocking=True)
   for v,fn in funcs.items():
    work=n if k=='unpackbits' and v in ('edited','tuned') else out
    def launch(j):
     x,y=xr[j%ring],yr[j%ring]
     a=(x,y,np.uint32(n)) if v=='tuned' else args(k,x,y)
     fn((max(1,(work+127)//128),),(128,),a,stream=stream)
    for j in range(20):launch(j)
    stream.synchronize()
    with stream:
     stream.begin_capture()
     for j in range(32):launch(j)
     graphs[v]=stream.end_capture()
   samples={v:[] for v in funcs};orders=[]
   for _ in range(7):
    order=list(funcs);rng.shuffle(order);orders.append(order)
    for v in order:
     begin=cp.cuda.Event();end=cp.cuda.Event();begin.record(stream);graphs[v].launch(stream);end.record(stream);end.synchronize()
     samples[v].append(cp.cuda.get_elapsed_time(begin,end)*1000/32)
   med={v:statistics.median(s) for v,s in samples.items()}
   row=dict(kernel=k,n=n,ring=ring,ring_bytes=ring*(n+out),us=med,samples_us=samples,orders=orders,speedup_normal=med['normal']/med['edited'],speedup_tuned=med['tuned']/med['edited'])
   report['rows'].append(row);print(k,n,med,'normal/edit',round(row['speedup_normal'],3),flush=True);check_foreign()
  (D/('results-'+REGIME+'.json')).write_text(json.dumps(report,indent=2)+'\n')
 print('passed cases',report['cases'])
if __name__=='__main__':main()
