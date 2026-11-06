"""Locked independent CPU differential and fair AOT graph timing. GPU tests are not proofs."""
from pathlib import Path
import fcntl,hashlib,json,os,subprocess,statistics
import numpy as np
import cupy as cp
D=Path(__file__).resolve().parent
S=Path('/mnt/scratch/e5r-oss-ptx/catboost-batch')
S.mkdir(parents=True,exist_ok=True)
RNG=np.random.default_rng(174)
IDS=['zero_partitions','reverse','zero_segments','fill_query_end_mask','compute_group_ids']
def check_gpu():
 s=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],text=True).strip()
 if any(int(x)!=os.getpid() for x in s.splitlines() if x.strip()):raise RuntimeError('foreign GPU process '+s)
def array(host,off):
 h=np.asarray(host,dtype=np.uint32);base=cp.full(h.size+off+8,np.uint32(0xfeedbeef));view=base[off:off+h.size];view.set(h);return base,view
def case(name,n,offset,pattern=0,qlen=33):
 # Return GPU argument arrays, output, CPU expected, buffers, launch shape.
 bufs=[];inputs=[]
 def a(h):
  b,v=array(h,offset);bufs.append((b,v));inputs.append(np.asarray(h,dtype=np.uint32).copy());return v
 words=RNG.integers(0,2**32,n,dtype=np.uint32)
 if pattern==1:words[:]=0
 if pattern==2:words[:]=0xffffffff
 if name=='zero_partitions':
  out=a(np.resize(words,2*n));args=(out,np.uint32(n));expected=np.zeros(2*n,np.uint32);block=256;work=n
 elif name=='reverse':
  out=a(words);args=(out,np.uint64(n));expected=words[::-1];block=256;work=(n+1)//2
 elif name=='zero_segments':
  flags=a(words);initial=RNG.integers(0,2**32,n,dtype=np.uint32);out=a(initial);mask=np.uint32(0x80000001);args=(flags,mask,np.uint32(n),out);expected=initial.copy();expected[(words&mask)!=0]=0;block=256;work=n
 elif name=='fill_query_end_mask':
  qids=words;docs=RNG.permutation(n).astype(np.uint32);q=a(qids);docsdev=a(docs);out=a(np.full(n,0xdeadcafe,np.uint32));args=(q,docsdev,np.uint32(n),out);expected=np.ones(n,np.uint32)
  if n>1:expected[:-1]=(qids[docs[:-1]]!=qids[docs[1:]]).astype(np.uint32)
  block=256;work=n
 else:
  sizes=RNG.integers(0,qlen+1,n,dtype=np.uint32);offsets=np.concatenate(([0],np.cumsum(sizes,dtype=np.uint64)))[:-1].astype(np.uint32);bias=17
  sz=a(sizes);offs=a(offsets+np.uint32(bias));out=a(np.full(int(sizes.sum()),0xdeadcafe,np.uint32));args=(sz,offs,np.uint32(bias),np.int32(n),out);expected=np.repeat(np.arange(n,dtype=np.uint32),sizes.astype(np.int64));block=128;work=n*32
 return args,out,expected,bufs,inputs,(max(1,(work+block-1)//block),),(block,)
def run():
 check_gpu()
 meta={'gpu':subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version,clocks.sm,clocks.mem','--format=csv,noheader'],text=True).strip(),'cupy':cp.__version__,'numpy':np.__version__,'runtime':cp.cuda.runtime.runtimeGetVersion(),'driver':cp.cuda.runtime.driverGetVersion(),'seed':174,'lock':'/mnt/scratch/e5r-gpu-benchmark.lock','compiler':subprocess.check_output(['nvcc','--version'],text=True),'ptxas':subprocess.check_output(['ptxas','--version'],text=True),'strict_proof_accepted':False,'full_upstream_runtime_verified':False}
 allrows=[]
 for name in IDS:
  d=D/name;mods={};funcs={}
  for variant in ['original','edited','tuned']:
   p=d/(variant+'.ptx');c=S/(name+'-'+variant+'.cubin')
   res=subprocess.run(['ptxas','-O3','-arch=sm_86',str(p),'-o',str(c)],capture_output=True,text=True);(d/(variant+'.ptxas.log')).write_text(res.stdout+res.stderr);res.check_returncode()
   import re
   symbol=re.search(r'\.entry\s+(\w+)',p.read_text()).group(1)
   mods[variant]=cp.RawModule(path=str(c));funcs[variant]=mods[variant].get_function(symbol)
  count=0
  for n in [0,1,2,31,32,33,127,128,255,256,257,4096,65537]:
   for offset in [1,4]:
    for pattern in [0,1,2]:
     args,out,expected,bufs,inputs,grid,block=case(name,n,offset,pattern)
     for variant,fn in funcs.items():
      for (base,view),initial in zip(bufs,inputs):view.set(initial)
      fn(grid,block,args);cp.cuda.get_current_stream().synchronize()
      np.testing.assert_array_equal(out.get(),expected)
      for (base,view),initial in zip(bufs,inputs):
       np.testing.assert_array_equal(base[:offset].get(),0xfeedbeef);np.testing.assert_array_equal(base[offset+view.size:].get(),0xfeedbeef)
       if view is not out:np.testing.assert_array_equal(view.get(),initial)
      count+=1
  print(name,'correctness',count,flush=True)
  rows=[]
  shapes=[(n,33) for n in [1,31,256,257,4096,65536,1048576,4194304]] if name!='compute_group_ids' else [(n,q) for n in [1,5,4096,65536] for q in [1,8,32,33,128]]
  for n,qlen in shapes:
   for regime in (['hot','rotating'] if n>=1048576 else ['hot']):
    ring=8 if regime=='rotating' else 1
    cases=[case(name,n,4,qlen=qlen) for _ in range(ring)]
    graphs={};stream=cp.cuda.Stream(non_blocking=True)
    for variant,fn in funcs.items():
     def launch(j):
      args,out,expected,bufs,inputs,grid,block=cases[j%ring];fn(grid,block,args,stream=stream)
     for j in range(20):launch(j)
     stream.synchronize()
     with stream:
      stream.begin_capture()
      for j in range(32):launch(j)
      graphs[variant]=stream.end_capture()
    samples={v:[] for v in funcs};orders=[]
    for rep in range(7):
     order=list(funcs);RNG.shuffle(order);orders.append(order)
     for variant in order:
      start=cp.cuda.Event();end=cp.cuda.Event()
      start.record(stream)
      for _ in range(4):graphs[variant].launch(stream)
      end.record(stream);end.synchronize();samples[variant].append(cp.cuda.get_elapsed_time(start,end)*1000/128)
    med={v:statistics.median(x) for v,x in samples.items()}
    rows.append({'n':n,'max_query_size':qlen if name=='compute_group_ids' else None,'regime':regime,'ring':ring,'samples_us':samples,'median_us':med,'speedup_original_over_edited':med['original']/med['edited'],'speedup_tuned_over_edited':med['tuned']/med['edited'],'orders':orders})
    check_gpu()
   print(name,n,qlen,med,flush=True)
  result={'metadata':meta,'correctness_cases':count,'canaries':True,'input_preservation':True,'offset_words':[1,4],'scope':'extracted exact upstream body AOT kernel only; no API claim; tuned CUDA is separate comparator','proof':'pending direct universal equivalence, no accepted theorem yet','hashes':{v:hashlib.sha256((d/(v+'.ptx')).read_bytes()).hexdigest() for v in funcs},'rows':rows}
  (d/'gpu.json').write_text(json.dumps(result,indent=2)+'\n');allrows.append((name,count,len(rows)))
 print(allrows)
if __name__=='__main__':
 with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX);run()
