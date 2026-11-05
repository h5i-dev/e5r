"""Frozen concrete targets: independent CPU tests, exact PTX timing and scoreboard."""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess,sys,time,math
import numpy as np
import cupy as cp
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent/'verified-packing'))
import benchmark as timing
NAMES=['advance256','transpose','laplace','xor8','crc32word','xorshift32x64']
SWEEPS={name:[256,4096,65536,1048576,16777216] for name in NAMES}
SWEEPS['transpose']=[32,128,512,1024,2048,4096]
SWEEPS['laplace']=[32,128,512,1024,4096,16384]
TESTS={name:[0,1,2,3,7,31,32,33,127,128,129,255,256,257,1025,4099] for name in NAMES}
TESTS['transpose']=[32,64,96,128]
TESTS['laplace']=[8,16,24,40]


def idle():
 for attempt in range(40):
  try:return timing.uncontended()
  except RuntimeError:
   if attempt==39:raise
   time.sleep(.25)


def layout(name,n,which):
 if name=='transpose':
  if n<32 or n%32:raise ValueError('transpose requires positive full32 tiles')
  return n*n,n*n,(32,8),((n//32,n//8) if which=='original' else (n//32,n//32))
 if name=='laplace':
  if n<8 or n%8:raise ValueError('laplace requires positive full8 rows')
  return (n+2)*1026,n*1024,(32,8),(32,n//8)
 return n*(8 if name=='xor8' else 1),n,(256,),(max(1,(n+255)//256),)


def implementations(name):
 return [p for p in ['original','candidate','tuned','iterative'] if (D/name/(p+'.ptx')).exists()]


def functions(name):
 return {p:cp.RawModule(path=str(D/name/(p+'.ptx'))).get_function('kernel') for p in implementations(name)}


def reference(name,a,n):
 if name=='advance256':
  x=a.copy()
  for _ in range(256):x=(x.astype(np.uint64)*1664525+1013904223).astype(np.uint32)
  return x
 if name=='xorshift32x64':
  x=a.copy()
  for _ in range(64):x=x^(x<<13);x=x^(x>>17);x=x^(x<<5)
  return x
 if name=='crc32word':
  x=a.copy()
  for _ in range(32):x=(x>>1)^np.where(x&1,np.uint32(0xedb88320),np.uint32(0))
  return x
 if name=='xor8':return np.bitwise_xor.reduce(a.reshape(n,8),axis=1)
 if name=='transpose':return a.reshape(n,n).T.copy().ravel()
 x=a.reshape(n+2,1026)
 return ((x[1:-1,1:-1]<<2)-x[1:-1,:-2]-x[1:-1,2:]-x[:-2,1:-1]-x[2:,1:-1]).ravel()


def sample_reference(name,a,n,ix):
 if name in ['advance256','crc32word','xorshift32x64']:return reference(name,a[ix],len(ix))
 if name=='xor8':return reference(name,a.reshape(n,8)[ix].copy().ravel(),len(ix))
 if name=='transpose':return a[(ix%n)*n+ix//n]
 q=(ix//1024+1)*1026+ix%1024+1
 return (a[q]<<2)-a[q-1]-a[q+1]-a[q-1026]-a[q+1026]


def hashes(name):
 folder=D/name;original=json.loads((folder/'freeze.json').read_text());art=json.loads((folder/'artifacts.json').read_text())
 for p,h in {**original['sha256'],**art['sha256']}.items():
  assert hashlib.sha256((folder/p).read_bytes()).hexdigest()==h,p
 return {p:hashlib.sha256((folder/(p+'.ptx')).read_bytes()).hexdigest() for p in implementations(name)}


def test(name):
 idle();f=functions(name);rng=np.random.default_rng(29177);cases=0
 for n in TESTS[name]:
  timing.uncontended();ni,no,_,_=layout(name,n,'candidate')
  patterns=[np.zeros(ni,dtype=np.uint32),np.full(ni,0xffffffff,dtype=np.uint32),np.arange(ni,dtype=np.uint32),rng.integers(0,2**32,size=ni,dtype=np.uint32)]
  if name=='xorshift32x64':patterns.append(np.uint32(1)<<(np.arange(ni,dtype=np.uint32)%32))
  for a in patterns:
   expected=reference(name,a,n)
   for offset in range(4):
    backing_x=cp.empty(ni+8,dtype=cp.uint32);x=backing_x[offset:offset+ni];x.set(a)
    for out_offset in range(4):
     for which,kernel in f.items():
      backing=cp.full(no+16,0xa5a5a5a5,dtype=cp.uint32);y=backing[4+out_offset:4+out_offset+no]
      _,_,block,grid=layout(name,n,which);kernel(grid,block,(x,y,np.uint32(n)))
      np.testing.assert_array_equal(y.get(),expected);np.testing.assert_array_equal(x.get(),a)
      np.testing.assert_array_equal(backing[:4+out_offset].get(),0xa5a5a5a5)
      np.testing.assert_array_equal(backing[4+out_offset+no:].get(),0xa5a5a5a5);cases+=1
 result=dict(cases=cases,reference='independent NumPy operator; iterative LCG/CRC, axis XOR, transpose, direct padded Laplacian',
             input_output_offsets='all16 independent combinations0/4/8/12 bytes',ptx_sha256=hashes(name),seed=29177,
             lock='/mnt/scratch/e5r-gpu-benchmark.lock',foreign_processes_observed=False)
 (D/name/'results/correctness.json').write_text(json.dumps(result,indent=2)+'\n');print(name,'correct',cases,flush=True)


def bench(name):
 idle();f=functions(name);rng=np.random.default_rng(29178);rows=[];identity=hashes(name)
 correctness=json.loads((D/name/'results/correctness.json').read_text());assert correctness['ptx_sha256']==identity
 for n in SWEEPS[name]:
  ni,no,_,_=layout(name,n,'candidate');a=rng.integers(0,2**32,size=ni,dtype=np.uint32);x=cp.asarray(a);y=cp.empty(no,dtype=cp.uint32);base=cp.empty_like(y)
  block=layout(name,n,'original')[2];grid=layout(name,n,'original')[3];f['original'](grid,block,(x,base,np.uint32(n)))
  ix=np.unique(np.concatenate([np.array([0,no-1,no//2],dtype=np.int64),rng.integers(0,no,size=min(4096,no))]));expected=sample_reference(name,a,n,ix)
  np.testing.assert_array_equal(base[cp.asarray(ix)].get(),expected)
  for which,kernel in f.items():
   _,_,block,grid=layout(name,n,which)
   def launch():kernel(grid,block,(x,y,np.uint32(n)))
   launch();cp.testing.assert_array_equal(y,base)
   for graph in [True,False]:
    result=timing.measure(launch,graph)
    rows.append(dict(size=n,input_bytes=ni*4,output_bytes=no*4,name=which,grid=grid,block=block,graph=graph,
                     logical_GBps=(ni+no)*4/result['median_us']/1000,**result))
    print(name,n,which,'graph' if graph else 'events',round(result['median_us'],4),flush=True)
  meta=dict(ptx_sha256=identity,cupy=cp.__version__,numpy=np.__version__,
            gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip(),
            nvcc=json.loads((D/name/'freeze.json').read_text())['nvcc'],flags=json.loads((D/name/'freeze.json').read_text())['flags'],
            resources={k:v.attributes for k,v in f.items()},seed=29178,lock='/mnt/scratch/e5r-gpu-benchmark.lock',
            foreign_processes_observed=False,correctness='all output words differential against frozen original at every timed shape; independent CPU samples up to4096 plus exhaustive small-domain tests',
            proof_status_at_measurement='exploratory; no accepted equivalence claimed')
  (D/name/'results/performance.json').write_text(json.dumps(dict(metadata=meta,rows=rows),indent=2)+'\n')


def scoreboard():
 result=[];text=['# Concrete PTX target scoreboard','','2f386ea stencil milestone preserved. All new rows are exploratory until their exact proof is accepted.','',
 '| Target | Correctness | Original parse | Graph GM original/candidate | Largest original/candidate | GM tuned/candidate | Status |','|---|---:|---|---:|---:|---:|---|']
 for name in NAMES:
  p=D/name/'results';parse=json.loads((p/'parse.json').read_text()) if (p/'parse.json').exists() else {};c=json.loads((p/'correctness.json').read_text()) if (p/'correctness.json').exists() else None
  perf=json.loads((p/'performance.json').read_text()) if (p/'performance.json').exists() else None;gm=None;large=None;tuned_gm=None;state='authored; unproved'
  if perf:
   rows=perf['rows'];assert sorted({r['size'] for r in rows})==SWEEPS[name] and len(rows)==len(SWEEPS[name])*len(implementations(name))*2,'partial sweep: '+name
   ratios=[];tuned_ratios=[];table=['# '+name+' measured comparison','','Exploratory: no accepted proof. Graph medians in microseconds; full event timings and repeat samples in performance.json.','', '| Size | Original | Direct PTX | Tuned CUDA | Unrolled CUDA | Original/PTX | Tuned/PTX |','|---:|---:|---:|---:|---:|---:|---:|']
   for n in SWEEPS[name]:
    a={r['name']:r['median_us'] for r in rows if r['size']==n and r['graph']};ratios.append(a['original']/a['candidate']);tuned_ratios.append(a['tuned']/a['candidate'])
    table.append(f"| {n} | {a['original']:.3f} | {a['candidate']:.3f} | {a['tuned']:.3f} | {a.get('iterative',float('nan')):.3f} | {ratios[-1]:.3f}x | {tuned_ratios[-1]:.3f}x |")
   (p/'COMPARISON.md').write_text('\n'.join(table)+'\n')
   tuned_gm=math.exp(sum(map(math.log,tuned_ratios))/len(tuned_ratios))
   gm=math.exp(sum(map(math.log,ratios))/len(ratios));large=ratios[-1];state='promising, UNPROVED' if gm>=1.2 and large>=1.2 else 'measured miss / timeboxed; UNPROVED'
  if parse and not parse['original']['supported']:state+='; original outside current parser'
  proof=json.loads((p/'proof.json').read_text()) if (p/'proof.json').exists() else None
  if proof and proof['verdict']=='proved':
   assert proof['input']['ptx']['sha256']==hashes(name)['candidate'];state='PROVED direct equivalence'
  row=dict(target=name,cases=c['cases'] if c else None,parse=parse,gm=gm,large=large,tuned_gm=tuned_gm,status=state);result.append(row)
  text.append(f"| {name} | {row['cases'] or 'pending'} | {parse.get('original',{}).get('supported','pending')} | {f'{gm:.3f}x' if gm else 'pending'} | {f'{large:.3f}x' if large else 'pending'} | {f'{tuned_gm:.3f}x' if tuned_gm else 'pending'} | {state} |")
 text+=['','All declared shapes, both graph/device-event regimes, variance, versions, resources and source hashes are in each results/performance.json. CUDA tuned comparators use the same known techniques; gains over original are not labeled PTX-only. Shared-tile shape restrictions and raw CRC semantics are explicit in PLAN.md.','', 'Proof status is separate from GPU tests and timing. Standard allowed axioms only; parser/exporter, nvcc, ptxas/JIT and hardware remain outside Lean.']
 (D/'SCOREBOARD.md').write_text('\n'.join(text)+'\n');(D/'scoreboard.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
 if len(sys.argv)>1 and sys.argv[1]=='report':scoreboard();raise SystemExit
 mode=sys.argv[1] if len(sys.argv)>1 else 'test';targets=sys.argv[2:] or NAMES
 with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX);idle()
  for name in targets:
   (test if mode=='test' else bench)(name)
