#!/usr/bin/env python3
"""Instruction regression, not an optimization benchmark or FP4 proof.
Independent Python bytes = Rust interpreter = Lean exec/tstep = GPU JIT/cubin.
All GPU execution holds the shared flock and refuses foreign compute PIDs.
"""
import fcntl,hashlib,json,os,random,signal,struct,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(os.environ.get('FP4_PROOF_SCRATCH','/mnt/scratch/e5r-oss-ptx/int4/whole-proof'))/'forms-diff';OUT.mkdir(parents=True,exist_ok=True)
E5R=Path(os.environ.get('E5R_VERIFY','/mnt/scratch/e5r-oss-ptx/cargo/release/e5r'))
CUDA=Path(os.environ.get('CUDA_HOME','/usr/local/cuda'))
sys.path.insert(0,str(ROOT/'verification/ptx/difftest'))
from gen import kernel_text
rng=random.Random(20261106)
base=[0,1,2,15,16,31,32,0x7fff,0x8000,0xffff,0x80000000,0xffffffff,0xffffffffffff8001]
integers=base+[rng.getrandbits(64) for _ in range(128-len(base))]
floats=[0,0x80000000,0x3f800000,0xbf800000,0x40000000,0xc0000000,0x3f000000,0x00800000,1,0x807fffff,0x7f7fffff,0xff7fffff]
def number(bits):return struct.unpack('<f',struct.pack('<I',bits&0xffffffff))[0]
def bits(value):
 try:return struct.unpack('<I',struct.pack('<f',value))[0]
 except OverflowError:return 0xff800000 if value<0 else 0x7f800000
def flush(x):return x&0x80000000 if x&0x7f800000==0 else x
def signed(x):return (x&0xffffffff)-(1<<32) if x&0x80000000 else x&0xffffffff
def float_op(a,b,op):
 x,y=number(flush(a)),number(flush(b))
 return flush(bits(x*y if op=='mul' else x-y))
forms=[
 ('clz',['clz.b32 %r8, %r5;'],lambda a,b,i:32-(a&0xffffffff).bit_length(),False),
 ('min',['min.s32 %r8, %r5, %r6;'],lambda a,b,i:min(signed(a),signed(b))&0xffffffff,False),
 ('lane',['mov.u32 %r8, %laneid;'],lambda a,b,i:i%32,False),
 ('u16tof',['cvt.u16.u32 %h1, %r5;','cvt.rn.f32.u16 %f0, %h1;','mov.b32 %r8, %f0;'],lambda a,b,i:bits(a&65535),False),
 ('s16tof',['cvt.u16.u32 %h1, %r5;','cvt.rn.f32.s16 %f0, %h1;','mov.b32 %r8, %f0;'],lambda a,b,i:bits((a&65535)-(65536 if a&32768 else 0)),False),
 ('ftou16',['mov.b32 %f1, %r5;','cvt.rzi.u16.f32 %h0, %f1;','cvt.u32.u16 %r8, %h0;'],lambda a,b,i:max(0,min(65535,int(number(a)))),True),
 ('ftos16',['mov.b32 %f1, %r5;','cvt.rzi.s16.f32 %h0, %f1;','cvt.u32.u16 %r8, %h0;'],lambda a,b,i:max(-32768,min(32767,int(number(a))))&65535,True),
 ('sub',['mov.b32 %f1, %r5;','mov.b32 %f2, %r6;','sub.ftz.f32 %f0, %f1, %f2;','mov.b32 %r8, %f0;'],lambda a,b,i:float_op(a,b,'sub'),True),
 ('mul',['mov.b32 %f1, %r5;','mov.b32 %f2, %r6;','mul.ftz.f32 %f0, %f1, %f2;','mov.b32 %r8, %f0;'],lambda a,b,i:float_op(a,b,'mul'),True)]
ptx='.version 9.2\n.target sm_86\n.address_size 64\n';cases=[];expected=[]
for name,body,ref,isfloat in forms:
 k='forms_'+name
 text=kernel_text(k,body+['st.global.u32 [%rd4], %r8;']).replace('\t.reg .pred','\t.reg .b16 %h<3>;\n\t.reg .pred',1)
 # Every case has one physical CTA; linearize 3D thread coordinates for IO.
 old='\tmad.lo.u32 \t%r4, %r1, %r2, %r3;'
 new='\tmov.u32 %r10, %tid.y;\n\tmov.u32 %r11, %tid.z;\n\tmov.u32 %r12, %ntid.y;\n\tmad.lo.u32 %r10, %r11, %r12, %r10;\n\tmad.lo.u32 %r4, %r10, %r2, %r3;'
 assert old in text;text=text.replace(old,new)
 # Exercise comma-separated register groups in each generated entry.
 text=text.replace('%r<16>;','%r<16>, %extra;')
 ptx+=text
 for bx,by,bz in [(64,1,1),(8,8,2)]:
  count=bx*by*bz
  pairs=[(floats[i%len(floats)],floats[(i*5+3)%len(floats)]) if isfloat else (integers[i],integers[-i-1]) for i in range(count)]
  raw=b''.join(struct.pack('<QQQ',a,b,0) for a,b in pairs)
  cases.append(f'case {k} 1 1 1 {bx} {by} {bz} 0 {raw.hex()} {count*48}\n')
  out=bytearray([0xa5]*(count*48))
  for i,(a,b) in enumerate(pairs):out[i*48:i*48+4]=struct.pack('<I',ref(a,b,i))
  expected.append(f'result {k} {out.hex()}\n')
(OUT/'diff.ptx').write_text(ptx);(OUT/'cases.txt').write_text(''.join(cases));(OUT/'expected.txt').write_text(''.join(expected))
env=dict(os.environ,LEAN_NUM_THREADS='1')
def run(cmd,output=None,cwd=ROOT):
 p=subprocess.Popen(list(map(str,cmd)),cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:stdout,stderr=p.communicate(timeout=300)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL);p.communicate();raise
 if p.returncode:raise RuntimeError((cmd,p.returncode,stderr.decode()))
 if output:Path(output).write_bytes(stdout)
 return stdout
run([CUDA/'bin/ptxas','-O3','-arch=sm_86',OUT/'diff.ptx','-o',OUT/'diff.cubin'])
run(['gcc','-O2','-Wall',ROOT/'verification/ptx/difftest/gpurun.c','-I'+str(CUDA/'include'),'-lcuda','-o',OUT/'gpurun'])
run([E5R,'ptx','run','--cases',OUT/'cases.txt',OUT/'diff.ptx'],OUT/'rust.txt')
run([E5R,'ptx','export','--namespace','FP4Kernels',OUT/'diff.ptx'],OUT/'FP4Kernels.lean')
lean=run(['elan','which','lean'],cwd=ROOT/'verification/ptx').decode().strip()
env['LEAN_PATH']=str(ROOT/'verification/ptx/.lake/build/lib/lean')+':'+str(OUT)
run([lean,'-j1','-M2048','-R',OUT,OUT/'FP4Kernels.lean','-o',OUT/'FP4Kernels.olean'],OUT/'lean-export.log')
main=(ROOT/'verification/ptx/Diff/Main.lean').read_text().replace('Diff.Kernels','FP4Kernels')
(OUT/'Main.lean').write_text(main)
run([lean,'-j1','-M2048','--run',OUT/'Main.lean',OUT/'cases.txt'],OUT/'lean.txt')
with open('/mnt/scratch/e5r-gpu-benchmark.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 foreign=run(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader']).decode().strip()
 if foreign:raise SystemExit('refusing GPU work: foreign compute PIDs '+foreign)
 for name,module in [('gpu-jit','diff.ptx'),('gpu-cubin','diff.cubin')]:run([OUT/'gpurun',OUT/module,OUT/'cases.txt'],OUT/(name+'.txt'))
golden=(OUT/'expected.txt').read_bytes()
for name in ['rust','lean','gpu-jit','gpu-cubin']:
 assert (OUT/(name+'.txt')).read_bytes()==golden,name+' differs from independent Python reference'
report={'kind':'semantic regression only; no benchmark or FP4 whole-kernel proof','launches':len(cases),'forms':len(forms),'threads_per_form':[64,128], 'comparisons':['independent Python','Rust','actual Lean exec/tstep','GPU JIT','ptxas cubin'],'canaries':'all 44 bytes outside each 4-byte output in each 48-byte record retained', 'ptx_sha256':hashlib.sha256(ptx.encode()).hexdigest(),'expected_sha256':hashlib.sha256(golden).hexdigest(),'GPU_lock':'exclusive shared flock and empty foreign-PID check before GPU child launches','status':'pass'}
(OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
