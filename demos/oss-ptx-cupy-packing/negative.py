"""Realistic semantic mutations tested on hardware; not formal proof negatives."""
import fcntl,hashlib,json,os,subprocess,tempfile
from pathlib import Path
import numpy as np
import cupy as cp
from gpu import D,args,check_foreign
lock=open('/mnt/scratch/e5r-gpu-benchmark.lock','w');fcntl.flock(lock,fcntl.LOCK_EX);check_foreign()
rows=[]
for k in ('packbits','unpackbits'):
 original=(D/k/'edited.ptx').read_text()
 if k=='packbits':
  old='st.global.u8 \t[%rd11], %rs32;';new='// semantic negative: final store removed'
  if old not in original:old='st.global.u8 \t[%rd11], %rs32;'
 else:old='shr.u32 %r6, %r5, 7;';new='shr.u32 %r6, %r5, 6;'
 assert original.count(old)==1,(k,old)
 bad=original.replace(old,new)
 with tempfile.TemporaryDirectory(dir='/mnt/scratch/e5r-oss-ptx/tmp') as tmp:
  p=Path(tmp)/'bad.ptx';p.write_text(bad)
  fn=cp.RawModule(path=str(p)).get_function('cupy_'+k+'_big')
  host=np.full(8,128,np.uint8);x=cp.asarray(host);y=cp.zeros(1 if k=='packbits' else 64,np.uint8)
  fn((1,),(128,),args(k,x,y));got=y.get();expected=np.packbits(host) if k=='packbits' else np.unpackbits(host)
  assert not np.array_equal(got,expected)
  rows.append(dict(kernel=k,mutation=new,mutant_sha256=hashlib.sha256(bad.encode()).hexdigest(),detected=True,got=got.tolist(),expected=expected.tolist()))
(D/'gpu-negatives.json').write_text(json.dumps(dict(cases=rows,formal_proof_negative=False),indent=2)+'\n')
print('Both semantic GPU mutants detected; formal rebound proof negatives pending.')
