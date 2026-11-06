"""Additional adversarial values, masks, tails, launches and frame tests."""
from gpu import *
import hashlib
count=0
with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 snap=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],text=True).strip();assert not snap,snap
 for name in NAMES:
  symbol='cupy_'+name+('_kernel' if name=='putmask' else '')
  modules={v:cp.RawModule(path=str(D/name/p)) for v,p in {'native':'normal.cubin','original':'original.ptx','edited':'edited.ptx'}.items()};fns={v:m.get_function(symbol) for v,m in modules.items()}
  sizes=[256,7936,65536] if name=='tri' else [1,31,255,256,257,4096,65536]
  for n in sizes:
   size=n if name=='flatiter_getitem_slice' else 256
   for pattern in [np.array([0],np.int32),np.array([-1],np.int32),np.array([-2**31,2**31-1,0,1,-1,0x55555555],np.int32)]:
    host=np.resize(pattern,size);abase=cp.full(size+16,-999,cp.int32);a=abase[4:4+size];a.set(host)
    for maskval in [0,1,2] if name=='putmask' else [2]:
     mh=np.zeros(n,bool) if maskval==0 else np.ones(n,bool) if maskval==1 else np.arange(n)%2==0;mask=cp.asarray(mh)
     for block in [32,128,256]:
      for grid in [1,(n+block-1)//block+1]:
       ybase=cp.full(n+16,-777,cp.int32);y=ybase[4:4+n];want=expected(name,host,n,mh)
       for v,fn in fns.items():
        y.fill(-118);fn((grid,),(block,),args(name,a,y,mask))
        np.testing.assert_array_equal(y.get(),want);np.testing.assert_array_equal(a.get(),host)
        np.testing.assert_array_equal(ybase[:4].get(),-777);np.testing.assert_array_equal(ybase[4+n:].get(),-777)
        np.testing.assert_array_equal(abase[:4].get(),-999);np.testing.assert_array_equal(abase[4+size:].get(),-999);count+=1
r=dict(cases=count,all_passed=True,proof_accepted=False,patterns=['zeros','all_one_bits','signed_extremes_and_alternating'],masks=['all_false','all_true','alternating'],blocks=[32,128,256],grid=['one_grid_stride','covering_plus_tail'],hashes={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for name in NAMES for p in [D/name/'normal.cubin',D/name/'original.ptx',D/name/'edited.ptx']})
(D/'edges.json').write_text(json.dumps(r,indent=2)+'\n');print(count,'edge cases passed')
