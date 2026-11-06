#!/usr/bin/env python3
"""Wrong-sign execution negative; explicitly not a whole-kernel proof negative."""
import ctypes as c, gzip, hashlib, json, os, re, subprocess
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
scratch=Path(os.environ.get('FP4_SCRATCH','/mnt/scratch/e5r-oss-ptx/int4/fp4-sign'))
text=gzip.decompress((HERE/'evidence/edited.ptx.gz').read_bytes()).decode()
wrong,count=re.subn(r'(and.b32 %sign\d+, %sign\d+, )0x80000000;',r'\g<1>0x40000000;',text)
assert count==48
ptx=scratch/'wrong-sign.ptx'; cubin=scratch/'wrong-sign.cubin';ptx.write_text(wrong)
(HERE/'evidence/wrong-sign.ptx.gz').write_bytes(gzip.compress(wrong.encode(),mtime=0))
subprocess.run(['/usr/local/cuda/bin/ptxas','-O3','-arch=sm_86',str(ptx),'-o',str(cubin)],check=True)
(HERE/'evidence/wrong-sign.cubin.gz').write_bytes(gzip.compress(cubin.read_bytes(),mtime=0))
# No context is created until the shared lock and foreign-PID check pass.
import driver as d
p=d.ptr;u=d.u64
module,fn=p(),p();d.load(c.byref(module),os.fsencode(cubin))
d.function(c.byref(fn),module,b'_Z20kDequantizeBlockwiseIfLi512ELi64ELi8ELi1EEvPfPhS0_PT_ii')
packed=np.tile(np.arange(256,dtype=np.uint8),2);scales=np.ones(32,dtype=np.float32)
alloc=[]
for size in [512,128,4096+128]:
 v=u();d.allocate(c.byref(v),size);alloc.append(v)
inp,scale,out=alloc;d.upload(inp,packed.ctypes.data,512);d.upload(scale,scales.ctypes.data,128);d.memset(out,0xa5,4096+128)
zero=u(0);target=u(out.value+64);bs=c.c_int(32);n=c.c_int(1024)
params=(p*6)(*[c.cast(c.byref(x),p) for x in [zero,inp,scale,target,bs,n]])
d.launch(fn,1,1,1,64,1,1,0,d.stream,params,None);d.sync(d.stream)
host=c.create_string_buffer(4096+128);d.download(host,out,len(host));raw=host.raw
assert raw[:64]==b'\xa5'*64 and raw[-64:]==b'\xa5'*64
codes=np.empty(1024,dtype=np.uint32);codes[::2]=packed>>4;codes[1::2]=packed&15
mag=np.array([0,0x3baaaaab,0x3f2aaaab,0x3f800000,0x3eaaaaab,0x3f000000,0x3e2aaaab,0x3e800000],dtype=np.uint32)
expected=mag[codes&7]|((codes&8)<<28);actual=np.frombuffer(raw[64:-64],dtype=np.uint32)
mismatches=int(np.count_nonzero(expected!=actual));assert mismatches>0
for v in alloc:d.free(v)
report={'kind':'GPU execution semantic negative only','candidate_sha256':hashlib.sha256(wrong.encode()).hexdigest(),'changed_sign_masks':count,'mismatching_outputs':mismatches,'outputs':1024,'canaries':'pass','proof_negative':False,'note':'Candidate hash rebound for execution. Whole-kernel exporter/proof admission is still blocked; do not count this as a strict proof negative.'}
(HERE/'gpu-negative.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
