"""GPU witnesses for bad parameter substitutions; not a Lean proof negative."""
from gpu import *
import hashlib,re
out=[]
with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 snap=subprocess.check_output(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],text=True).strip();assert not snap,snap
 for name in NAMES:
  p=D/name;ptx=(p/'edited.ptx').read_text();edit=json.loads((p/'edit.json').read_text());old=edit['value'];bad=0 if old==1 else 254
  if name=='flatiter_getitem_slice':
   ptx,count=ptx.replace('mov.u64 %rd32, %rd42;', 'mov.u64 %rd32, 0;'),1
  else:
   ptx,count=re.subn(r'(and.b64 %rd\d+, %rd\d+, )255;',r'\g<1>254;',ptx,count=1)
  assert count==1
  path=Path('/mnt/scratch/e5r-oss-ptx/cupy-index')/(name+'-negative.ptx');path.write_text(ptx)
  a=cp.arange(65536 if name=='flatiter_getitem_slice' else 256,dtype=cp.int32);y=cp.full(65536,-118,dtype=cp.int32);mask=cp.ones(65536,dtype=cp.bool_)
  module=cp.RawModule(path=str(path));fn=module.get_function('cupy_'+name+('_kernel' if name=='putmask' else ''))
  fn((512,),(128,),args(name,a,y,mask));actual=y.get();want=expected(name,a.get(),y.size,mask.get());diff=np.flatnonzero(actual!=want);assert diff.size,name
  i=int(diff[0]);out.append(dict(kernel=name,mutated_constant=bad,sha256=hashlib.sha256(ptx.encode()).hexdigest(),first_difference=i,actual=int(actual[i]),expected=int(want[i]),gpu_witness=True,strict_semantic_proof_negative='not reached: original parser unsupported'))
(D/'negatives.json').write_text(json.dumps(out,indent=2)+'\n');print('negative witnesses',len(out))
