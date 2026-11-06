#!/usr/bin/env python3
"""Two-warp NC/volatile regression: Python = actual Lean Warp model = GPU.
Not a universal proof, optimization measurement or FP4 acceptance. All GPU work
uses the shared exclusive lock and a foreign-compute-PID check.
"""
import fcntl,hashlib,json,os,random,signal,struct,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(os.environ.get('FP4_PROOF_SCRATCH','/mnt/scratch/e5r-oss-ptx/int4/whole-proof'))/'warp-diff';OUT.mkdir(parents=True,exist_ok=True)
E5R=Path(os.environ.get('E5R_VERIFY','/mnt/scratch/e5r-oss-ptx/cargo/release/e5r'))
CUDA=Path(os.environ.get('CUDA_HOME','/usr/local/cuda'))
sys.path.insert(0,str(ROOT/'verification/ptx/difftest'))
from gen import kernel_text
body=[
 'shl.b32 %r10, %r3, 2;', 'mov.u32 %r11, sm;', 'add.u32 %r10, %r11, %r10;',
 'st.volatile.shared.u32 [%r10], %r5;', 'bar.warp.sync -1;',
 'xor.b32 %r12, %r3, 31;', 'shl.b32 %r12, %r12, 2;', 'add.u32 %r12, %r11, %r12;',
 'ld.volatile.shared.u32 %r8, [%r12];', 'bar.sync 0;',
 'setp.eq.u32 %p1, %r3, 0;', '@%p1 st.volatile.shared.u32 [sm+512], 0x12345678;',
 'bar.sync 0;', 'ld.volatile.shared.u32 %r9, [sm+512];',
 'ld.global.nc.f32 %f0, [%rd3];', 'bar.warp.sync 0xffffffff;',
 'st.global.u32 [%rd4], %r8;', 'st.global.u32 [%rd4+4], %r9;', 'st.global.f32 [%rd4+8], %f0;']
ptx='.version 9.2\n.target sm_86\n.address_size 64\n'+kernel_text('warp_nc',body)
(OUT/'diff.ptx').write_text(ptx)
rng=random.Random(20261107);cases=[];expected=[]
for grid,block in [(1,64),(2,64),(1,128),(2,128)]:
 n=grid*block;values=[0,0x80000000,0x7fc12345,0xffa00001,1,0x807fffff,0x7f800000,0xff800000]+[rng.getrandbits(32) for _ in range(n-8)]
 raw=b''.join(struct.pack('<QQQ',x,rng.getrandbits(64),rng.getrandbits(64)) for x in values)
 cases.append(f'case warp_nc {grid} 1 1 {block} 1 1 0 {raw.hex()} {n*48}\n')
 out=bytearray([0xa5]*(n*48))
 for i,x in enumerate(values):out[i*48:i*48+12]=struct.pack('<III',values[i^31],0x12345678,x)
 expected.append('result warp_nc '+out.hex()+'\n')
(OUT/'cases.txt').write_text(''.join(cases));(OUT/'expected.txt').write_text(''.join(expected))
env=dict(os.environ,LEAN_NUM_THREADS='1')
def run(cmd,output=None,cwd=ROOT):
 p=subprocess.Popen(list(map(str,cmd)),cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:stdout,stderr=p.communicate(timeout=300)
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.communicate();raise
 if p.returncode:raise RuntimeError((cmd,p.returncode,stderr.decode(),stdout.decode()[:2000]))
 if output:Path(output).write_bytes(stdout);Path(str(output)+'.stderr').write_bytes(stderr)
 return stdout
run([CUDA/'bin/ptxas','-O3','-arch=sm_86',OUT/'diff.ptx','-o',OUT/'diff.cubin'])
run(['gcc','-O2','-Wall',ROOT/'verification/ptx/difftest/gpurun.c','-I'+str(CUDA/'include'),'-lcuda','-o',OUT/'gpurun'])
run([E5R,'ptx','export','--namespace','WarpKernels',OUT/'diff.ptx'],OUT/'WarpKernels.lean')
lean=run(['elan','which','lean'],cwd=ROOT/'verification/ptx').decode().strip()
env['LEAN_PATH']=str(ROOT/'verification/ptx/.lake/build/lib/lean')+':'+str(OUT)
run([lean,'-j1','-M2048','-R',OUT,OUT/'WarpKernels.lean','-o',OUT/'WarpKernels.olean'],OUT/'lean-export.log')
run([lean,'-j1','-M2048','--run',ROOT/'demos/oss-ptx-int4/whole-proof/WarpDiff.lean',OUT/'cases.txt'],OUT/'lean.txt')
with open('/mnt/scratch/e5r-gpu-benchmark.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 foreign=run(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader']).decode().strip()
 if foreign:raise SystemExit('refusing GPU work: foreign compute PIDs '+foreign)
 for name,module in [('gpu-jit','diff.ptx'),('gpu-cubin','diff.cubin')]:run([OUT/'gpurun',OUT/module,OUT/'cases.txt'],OUT/(name+'.txt'))
golden=(OUT/'expected.txt').read_bytes()
for name in ['lean','gpu-jit','gpu-cubin']:assert (OUT/(name+'.txt')).read_bytes()==golden,name+' differs from independent Python'
report={'kind':'semantic regression, not whole-kernel proof or performance measurement','launches':4,'geometries':[[1,64],[2,64],[1,128],[2,128]],'threads':576,'barriers':['2 full-mask warp barriers','2 CTA barriers'],'operations':['volatile shared warp permutation','volatile CTA scalar publication','NC f32 bit-preserving readonly input load incl NaNs'],'comparisons':['independent Python','actual Lean Warp.res/action','GPU JIT','GPU cubin'],'canaries':'36 retained bytes per48-byte output record','ptx_sha256':hashlib.sha256(ptx.encode()).hexdigest(),'expected_sha256':hashlib.sha256(golden).hexdigest(),'status':'pass'}
(OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
