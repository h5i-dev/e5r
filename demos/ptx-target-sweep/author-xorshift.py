"""Direct PTX for one fixed xorshift32 state-advance edit."""
from pathlib import Path
import subprocess,json,hashlib,datetime
from author import HEAD,MAP,END,CUDA_MAP,FLAGS,D
P=D/'xorshift32x64';P.mkdir(exist_ok=True);(P/'results').mkdir(exist_ok=True)
if (P/'freeze.json').exists():raise RuntimeError('already frozen')
step='x^=x<<13; x^=x>>17; x^=x<<5;'
original=CUDA_MAP+'unsigned x=input[i]; for(unsigned j=0;j<64;j++){'+step+'} output[i]=x;}\n'
(P/'original.cu').write_text(original)
subprocess.run(['nvcc',*FLAGS,str(P/'original.cu'),'-o',str(P/'original.ptx')],check=True)
freeze=dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),flags=FLAGS,nvcc=subprocess.check_output(['nvcc','--version'],text=True),operator=dict(state_bits=32,rounds=64,shifts=[13,17,5]),sha256={p:hashlib.sha256((P/p).read_bytes()).hexdigest() for p in ['original.cu','original.ptx']})
(P/'freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
def f(x):
 for _ in range(64):x^=(x<<13)&0xffffffff;x^=x>>17;x^=(x<<5)&0xffffffff
 return x
cols=[f(1<<j) for j in range(32)]
candidate=HEAD+MAP+'ld.global.u32 %r10, [%rd4];\nmov.u32 %r11, 0;\n'
tuned=CUDA_MAP+'unsigned x=input[i],s=0;\n'
for j,c in enumerate(cols):
 candidate+=f'and.b32 %r12, %r10, {1<<j};\nsetp.ne.u32 %p1, %r12, 0;\nselp.b32 %r13, {c}, 0, %p1;\nxor.b32 %r11, %r11, %r13;\n'
 tuned+=f'if(x&{1<<j}u)s^={c}u;\n'
candidate+='st.global.u32 [%rd5], %r11;\n'+END;tuned+='output[i]=s;}\n'
(P/'candidate.ptx').write_text('// Directly authored fixed GF(2) jump for xorshift32,64 rounds; unproved exploration.\n'+candidate)
(P/'tuned.cu').write_text(tuned);(P/'iterative.cu').write_text(original.replace('for(unsigned j=0;j<64;j++)','\n#pragma unroll\nfor(unsigned j=0;j<64;j++)'))
for p in ['tuned','iterative']:subprocess.run(['nvcc',*FLAGS,str(P/(p+'.cu')),'-o',str(P/(p+'.ptx'))],check=True)
art=dict(authored_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='fixed concrete32-column jump PTX; no candidate CUDA compilation',columns=cols,sha256={p:hashlib.sha256((P/p).read_bytes()).hexdigest() for p in ['candidate.ptx','tuned.cu','tuned.ptx','iterative.cu','iterative.ptx']})
(P/'artifacts.json').write_text(json.dumps(art,indent=2)+'\n')
print('xorshift32x64',freeze['sha256']['original.ptx'][:12],art['sha256']['candidate.ptx'][:12])
