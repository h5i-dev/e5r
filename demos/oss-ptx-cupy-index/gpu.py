"""Locked native OSS/PTX/edit/tuned validation and graph timing."""
from pathlib import Path
import fcntl,hashlib,json,os,random,statistics,subprocess
import numpy as np,cupy as cp
D=Path(__file__).resolve().parent
NAMES=['tri','resize','putmask','flatiter_setitem_slice','flatiter_getitem_slice']
SIZES=[1,31,255,256,257,4096,65536,1048576,4194304]
def st(vals):return np.asarray(vals,dtype=np.uint64).view('V'+str(8*len(vals)))
def arr(a):return st([a.data.ptr,a.size,a.size,a.strides[0]])
def args(name,a,y,mask,k=0):
 idx=st([y.size,y.size,0])
 if name=='tri':return (np.int32(256),np.int32(k),arr(y),idx)
 if name=='resize':return (arr(a),np.int64(256),arr(y),idx)
 if name=='putmask':return (arr(mask),arr(a),np.uint64(256),arr(y),idx)
 return (arr(a),np.int64(0),np.int64(1),arr(y),idx)
def upstream(name,a,y,mask,k=0):
 if name=='tri':return cp.tri(y.size//256,256,k,dtype=cp.int32)
 if name=='resize':return cp.resize(a,y.size)
 if name=='putmask':cp.putmask(y,mask,a);return y
 if name=='flatiter_setitem_slice':y.flat[:]=a;return y
 return a.flat[:y.size:1]
def expected(name,a,n,mask,k=0):
 if name=='tri':return np.tri(n//256,256,k,dtype=np.int32).ravel()
 if name=='flatiter_getitem_slice':return a[:n]
 vals=np.resize(a,n)
 return np.where(mask,vals,np.int32(-118)) if name=='putmask' else vals
def main():
 with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  snap=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],text=True).strip();assert not snap,snap
  rng=np.random.default_rng(1703);random.seed(1703)
  rows=[];checks=0
  for name in NAMES:
   symbol='cupy_'+name+('_kernel' if name=='putmask' else '')
   paths={'native':D/name/'normal.cubin','original':D/name/'original.ptx','edited':D/name/'edited.ptx','tuned':Path('/mnt/scratch/e5r-oss-ptx/cupy-index/tuned.cubin')}
   modules={v:cp.RawModule(path=str(p)) for v,p in paths.items()};fns={v:m.get_function(symbol) for v,m in modules.items()}
   sizes=[256*r for r in [1,31,256,4096,16384]] if name=='tri' else SIZES
   for n in sizes:
    ninput=n if name=='flatiter_getitem_slice' else 256
    ah=rng.integers(-2**31,2**31,ninput,dtype=np.int32);abase=cp.full(ninput+16,-555,dtype=cp.int32);a=abase[4:4+ninput];a.set(ah)
    mh=rng.integers(0,2,n,dtype=np.int8).astype(bool);mask=cp.asarray(mh)
    ybase=cp.full(n+16,-999,dtype=cp.int32);y=ybase[4:4+n]
    for k in [-257,-1,0,1,257] if name=='tri' else [0]:
     y.fill(-118);want=expected(name,ah,n,mh,k)
     np.testing.assert_array_equal(upstream(name,a,y,mask,k).get().ravel(),want);checks+=1
     for v,fn in fns.items():
      y.fill(-118);fn(((n+127)//128,),(min(128,n),),args(name,a,y,mask,k));cp.cuda.Device().synchronize()
      np.testing.assert_array_equal(y.get(),want);np.testing.assert_array_equal(a.get(),ah)
      np.testing.assert_array_equal(ybase[:4].get(),-999);np.testing.assert_array_equal(ybase[4+n:].get(),-999);checks+=1
    graphs={};stream=cp.cuda.Stream(non_blocking=True)
    arguments=args(name,a,y,mask)
    for v,fn in fns.items():
     for _ in range(20):fn(((n+127)//128,),(min(128,n),),arguments,stream=stream)
     stream.synchronize()
     with stream:
      stream.begin_capture()
      for _ in range(64):fn(((n+127)//128,),(min(128,n),),arguments,stream=stream)
      graphs[v]=stream.end_capture()
    samples={v:[] for v in fns};orders=[]
    for r in range(7):
     order=list(fns);random.shuffle(order);orders.append(order)
     for v in order:
      begin=cp.cuda.Event();end=cp.cuda.Event();begin.record(stream)
      for _ in range(4):graphs[v].launch(stream)
      end.record(stream);end.synchronize();samples[v].append(cp.cuda.get_elapsed_time(begin,end)*1000/256)
    med={v:statistics.median(xs) for v,xs in samples.items()}
    rows.append(dict(kernel=name,n=n,samples_us=samples,median_us=med,order=orders,speedup_native=med['native']/med['edited'],speedup_original=med['original']/med['edited'],speedup_tuned=med['tuned']/med['edited']))
    print(name,n,round(med['native']/med['edited'],3),round(med['tuned']/med['edited'],3),flush=True)
   # Zero-sized upstream APIs are handled by host dispatch and skipped, not launched.
   upstream(name,cp.empty(0 if name=='flatiter_getitem_slice' else 256,cp.int32),cp.empty(0,cp.int32),cp.empty(0,cp.bool_));checks+=1
  result=dict(checks=checks,all_passed=True,proof_accepted=False,rows=rows,metadata=dict(cupy=cp.__version__,numpy=np.__version__,gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version,clocks.sm,clocks.mem','--format=csv,noheader'],text=True).strip(),scope='hot graph kernel only',block=128,graphs=64,repeats=7,graph_replays=4))
  result['metadata']['hashes']={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for name in NAMES for p in [D/name/'normal.cubin',D/name/'original.ptx',D/name/'edited.ptx']}
  (D/'results.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__ == "__main__": main()
