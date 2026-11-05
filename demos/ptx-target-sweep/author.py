"""Five concrete instruction templates, not a transformation framework.
Original CUDA is frozen before writing any candidate; tuned CUDA is comparator only.
"""
from pathlib import Path
import datetime,hashlib,json,subprocess
D=Path(__file__).resolve().parent
FLAGS=['-O3','-arch=sm_86','-std=c++17','--ptx']
MASK=2**32-1
A,C=1664525,1013904223
JUMP_A=pow(A,256,2**32)
JUMP_C=0
for _ in range(256):JUMP_C=(A*JUMP_C+C)&MASK
POLY=0xEDB88320

def step(x):return (x>>1)^(POLY if x&1 else 0)
def four(x):
 for _ in range(4):x=step(x)
 return x

HEAD='''.version 9.2
.target sm_86
.address_size 64
.visible .entry kernel(.param .u64 kernel_param_0,.param .u64 kernel_param_1,.param .u32 kernel_param_2) {
.reg .pred %p<8>;
.reg .b32 %r<80>;
.reg .b64 %rd<32>;
'''
PARAM='''ld.param.u64 %rd1, [kernel_param_0];
ld.param.u64 %rd2, [kernel_param_1];
ld.param.u32 %r2, [kernel_param_2];
'''
MAP=PARAM+'''mov.u32 %r3, %ntid.x;
mov.u32 %r4, %ctaid.x;
mov.u32 %r5, %tid.x;
mad.lo.u32 %r1, %r4, %r3, %r5;
setp.ge.u32 %p0, %r1, %r2;
@%p0 bra DONE;
mul.wide.u32 %rd3, %r1, 4;
add.u64 %rd4, %rd1, %rd3;
add.u64 %rd5, %rd2, %rd3;
'''
END='DONE:\nret;\n}\n'
CUDA_MAP='extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) { unsigned i=blockIdx.x*blockDim.x+threadIdx.x; if(i>=n)return; '

def maps():
 original=CUDA_MAP+'''unsigned x=input[i];
#pragma unroll
for(unsigned j=0;j<256;j++)x=1664525u*x+1013904223u;
output[i]=x; }\n'''
 candidate=HEAD+MAP+f'ld.global.u32 %r10, [%rd4];\nmad.lo.u32 %r11, %r10, {JUMP_A}, {JUMP_C};\nst.global.u32 [%rd5], %r11;\n'+END
 tuned=CUDA_MAP+f'output[i]={JUMP_A}u*input[i]+{JUMP_C}u; }}\n'
 yield 'advance256',original,candidate,tuned,dict(rounds=256,a=A,c=C,jump_a=JUMP_A,jump_c=JUMP_C)
 original=CUDA_MAP+'''unsigned x=input[i];
#pragma unroll
for(unsigned j=0;j<32;j++) { if(x&1u)x=(x>>1)^0xedb88320u;else x>>=1; }
output[i]=x; }\n'''
 candidate=HEAD+MAP+'ld.global.u32 %r10, [%rd4];\n'
 tuned=CUDA_MAP+'unsigned x=input[i];\n#pragma unroll\nfor(unsigned k=0;k<8;k++){ unsigned y=x>>4;\n'
 for _ in range(8):
  candidate+='shr.u32 %r11, %r10, 4;\n'
  for j in range(4):candidate+=f'and.b32 %r12, %r10, {1<<j};\nsetp.ne.u32 %p1, %r12, 0;\n@%p1 xor.b32 %r11, %r11, {four(1<<j)};\n'
  candidate+='mov.u32 %r10, %r11;\n'
 for j in range(4):tuned+=f'if(x&{1<<j}u)y^={four(1<<j)}u;\n'
 tuned+='x=y;} output[i]=x;}\n';candidate+='st.global.u32 [%rd5], %r10;\n'+END
 yield 'crc32word',original,candidate,tuned,dict(polynomial=POLY,rounds=32,chunk_constants=[four(1<<j) for j in range(4)],initial_final_complement=False)
 original=CUDA_MAP+'''const unsigned* p=input+8*i; unsigned x=0;
#pragma unroll
for(unsigned j=0;j<8;j++)x^=p[j]; output[i]=x; }\n'''
 candidate=HEAD+MAP+'''mul.wide.u32 %rd6, %r1, 32;
add.u64 %rd4, %rd1, %rd6;
and.b64 %rd7, %rd4, 7;
setp.ne.u64 %p1, %rd7, 0;
@%p1 bra SCALAR;
ld.global.u64 %rd8, [%rd4];
ld.global.u64 %rd9, [%rd4+8];
ld.global.u64 %rd10, [%rd4+16];
ld.global.u64 %rd11, [%rd4+24];
xor.b64 %rd8, %rd8, %rd9;
xor.b64 %rd10, %rd10, %rd11;
xor.b64 %rd8, %rd8, %rd10;
cvt.u32.u64 %r10, %rd8;
shr.u64 %rd8, %rd8, 32;
cvt.u32.u64 %r11, %rd8;
xor.b32 %r10, %r10, %r11;
bra STORE;
SCALAR:
'''
 for j in range(8):candidate+=f'ld.global.u32 %r{10+j}, [%rd4+{4*j}];\n'
 for j in range(1,8):candidate+=f'xor.b32 %r10, %r10, %r{10+j};\n'
 candidate+='STORE:\nst.global.u32 [%rd5], %r10;\n'+END
 tuned=CUDA_MAP+'''const unsigned* p=input+8*i; unsigned x=0;
if(((unsigned long long)p&7)==0) {const unsigned long long* q=(const unsigned long long*)p;
unsigned long long v=q[0]^q[1]^q[2]^q[3];x=(unsigned)v^(unsigned)(v>>32);}
else {
#pragma unroll
for(unsigned j=0;j<8;j++)x^=p[j];}
output[i]=x;}\n'''
 yield 'xor8',original,candidate,tuned,dict(record_words=8)

def transpose():
 original='''extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned n) {
unsigned x=blockIdx.x*blockDim.x+threadIdx.x,y=blockIdx.y*blockDim.y+threadIdx.y;
if(x<n && y<n)output[x*n+y]=input[y*n+x]; }\n'''
 candidate=HEAD+'.shared .align 4 .b8 tile[4224];\n'+PARAM+'''mov.u32 %r3, %tid.x;
mov.u32 %r4, %tid.y;
mov.u32 %r5, %ctaid.x;
mov.u32 %r6, %ctaid.y;
shl.b32 %r10, %r5, 5;
add.u32 %r10, %r10, %r3;
shl.b32 %r11, %r6, 5;
add.u32 %r11, %r11, %r4;
mad.lo.u32 %r12, %r4, 33, %r3;
mov.u32 %r20, tile;
shl.b32 %r21, %r12, 2;
add.u32 %r21, %r20, %r21;
mad.lo.u32 %r13, %r11, %r2, %r10;
mul.wide.u32 %rd3, %r13, 4;
add.u64 %rd4, %rd1, %rd3;
mul.wide.u32 %rd6, %r2, 32;
'''
 for k in range(4):
  candidate+=f'ld.global.u32 %r30, [%rd4];\nst.shared.u32 [%r21+{k*1056}], %r30;\n'
  if k<3:candidate+='add.u64 %rd4, %rd4, %rd6;\n'
 candidate+='''bar.sync 0;
shl.b32 %r10, %r6, 5;
add.u32 %r10, %r10, %r3;
shl.b32 %r11, %r5, 5;
add.u32 %r11, %r11, %r4;
mad.lo.u32 %r12, %r3, 33, %r4;
shl.b32 %r21, %r12, 2;
add.u32 %r21, %r20, %r21;
mad.lo.u32 %r13, %r11, %r2, %r10;
mul.wide.u32 %rd3, %r13, 4;
add.u64 %rd4, %rd2, %rd3;
'''
 for k in range(4):
  candidate+=f'ld.shared.u32 %r30, [%r21+{k*32}];\nst.global.u32 [%rd4], %r30;\n'
  if k<3:candidate+='add.u64 %rd4, %rd4, %rd6;\n'
 candidate+=END
 tuned='''extern "C" __global__ void kernel(const unsigned* __restrict__ input,unsigned* __restrict__ output,unsigned n) {
__shared__ unsigned tile[32][33];unsigned tx=threadIdx.x,ty=threadIdx.y;
unsigned x=32*blockIdx.x+tx,y=32*blockIdx.y+ty;
#pragma unroll
for(unsigned j=0;j<4;j++)tile[ty+8*j][tx]=input[(y+8*j)*n+x];
__syncthreads();x=32*blockIdx.y+tx;y=32*blockIdx.x+ty;
#pragma unroll
for(unsigned j=0;j<4;j++)output[(y+8*j)*n+x]=tile[tx][ty+8*j]; }\n'''
 return 'transpose',original,candidate,tuned,dict(tile=32,block=[32,8],shared_stride=33)

def laplace():
 original='''extern "C" __global__ void kernel(const unsigned* input,unsigned* output,unsigned rows) {
unsigned x=blockIdx.x*blockDim.x+threadIdx.x,y=blockIdx.y*blockDim.y+threadIdx.y;
if(x<1024 && y<rows){const unsigned* p=input+(y+1)*1026+x+1;
output[y*1024+x]=(p[0]<<2)-p[-1]-p[1]-p[-1026]-p[1026];}}\n'''
 candidate=HEAD+'.shared .align 4 .b8 tile[1360];\n'+PARAM+'''mov.u32 %r3, %tid.x;
mov.u32 %r4, %tid.y;
mov.u32 %r5, %ctaid.x;
mov.u32 %r6, %ctaid.y;
shl.b32 %r10, %r5, 5;
add.u32 %r10, %r10, %r3;
shl.b32 %r11, %r6, 3;
add.u32 %r11, %r11, %r4;
add.u32 %r12, %r11, 1;
add.u32 %r13, %r10, 1;
mad.lo.u32 %r14, %r12, 1026, %r13;
mul.wide.u32 %rd3, %r14, 4;
add.u64 %rd4, %rd1, %rd3;
shl.b32 %r15, %r11, 10;
add.u32 %r15, %r15, %r10;
mul.wide.u32 %rd6, %r15, 4;
add.u64 %rd7, %rd2, %rd6;
add.u32 %r16, %r4, 1;
add.u32 %r17, %r3, 1;
mad.lo.u32 %r18, %r16, 34, %r17;
shl.b32 %r19, %r18, 2;
mov.u32 %r20, tile;
add.u32 %r21, %r20, %r19;
ld.global.u32 %r30, [%rd4];
st.shared.u32 [%r21], %r30;
setp.ne.u32 %p1, %r3, 0;
@%p1 bra NOT_LR;
sub.u64 %rd8, %rd4, 4;
ld.global.u32 %r31, [%rd8];
sub.u32 %r22, %r21, 4;
st.shared.u32 [%r22], %r31;
add.u64 %rd8, %rd4, 128;
ld.global.u32 %r31, [%rd8];
add.u32 %r22, %r21, 128;
st.shared.u32 [%r22], %r31;
NOT_LR:
setp.ne.u32 %p1, %r4, 0;
@%p1 bra NOT_TB;
sub.u64 %rd8, %rd4, 4104;
ld.global.u32 %r31, [%rd8];
sub.u32 %r22, %r21, 136;
st.shared.u32 [%r22], %r31;
add.u64 %rd8, %rd4, 32832;
ld.global.u32 %r31, [%rd8];
add.u32 %r22, %r21, 1088;
st.shared.u32 [%r22], %r31;
NOT_TB:
bar.sync 0;
sub.u32 %r22, %r21, 4;
ld.shared.u32 %r31, [%r22];
ld.shared.u32 %r32, [%r21+4];
sub.u32 %r22, %r21, 136;
ld.shared.u32 %r33, [%r22];
ld.shared.u32 %r34, [%r21+136];
shl.b32 %r30, %r30, 2;
sub.u32 %r30, %r30, %r31;
sub.u32 %r30, %r30, %r32;
sub.u32 %r30, %r30, %r33;
sub.u32 %r30, %r30, %r34;
st.global.u32 [%rd7], %r30;
'''+END
 tuned='''extern "C" __global__ void kernel(const unsigned* __restrict__ input,unsigned* __restrict__ output,unsigned rows) {
__shared__ unsigned tile[10][34];unsigned tx=threadIdx.x,ty=threadIdx.y;
unsigned x=32*blockIdx.x+tx,y=8*blockIdx.y+ty;const unsigned* p=input+(y+1)*1026+x+1;
unsigned c=p[0];tile[ty+1][tx+1]=c;
if(tx==0){tile[ty+1][0]=p[-1];tile[ty+1][33]=p[32];}
if(ty==0){tile[0][tx+1]=p[-1026];tile[9][tx+1]=p[8*1026];}
__syncthreads();output[y*1024+x]=(c<<2)-tile[ty+1][tx]-tile[ty+1][tx+2]-tile[ty][tx+1]-tile[ty+2][tx+1];}\n'''
 return 'laplace',original,candidate,tuned,dict(width=1024,input_width=1026,tile=[32,8])

def main():
 version=subprocess.check_output(['nvcc','--version'],text=True)
 for name,original,candidate,tuned,op in list(maps())+[transpose(),laplace()]:
  target=D/name;target.mkdir(exist_ok=True);(target/'results').mkdir(exist_ok=True)
  if (target/'freeze.json').exists():raise RuntimeError('already frozen: '+name)
  (target/'original.cu').write_text(original)
  subprocess.run(['nvcc',*FLAGS,str(target/'original.cu'),'-o',str(target/'original.ptx')],check=True)
  freeze=dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),nvcc=version,flags=FLAGS,operator=op,
              sha256={p:hashlib.sha256((target/p).read_bytes()).hexdigest() for p in ['original.cu','original.ptx']})
  (target/'freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
  (target/'candidate.ptx').write_text('// Directly authored edit of frozen original; exploratory until strict acceptance.\n'+candidate)
  (target/'tuned.cu').write_text(tuned)
  subprocess.run(['nvcc',*FLAGS,str(target/'tuned.cu'),'-o',str(target/'tuned.ptx')],check=True)
  artifact=dict(authored_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='concrete PTX instruction template; no candidate CUDA compilation',
                sha256={p:hashlib.sha256((target/p).read_bytes()).hexdigest() for p in ['candidate.ptx','tuned.cu','tuned.ptx']})
  (target/'artifacts.json').write_text(json.dumps(artifact,indent=2)+'\n')
  print(name,freeze['sha256']['original.ptx'][:12],artifact['sha256']['candidate.ptx'][:12],flush=True)
if __name__=='__main__':main()
