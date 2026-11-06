"""Direct PTX edits of frozen real CuPy programs; never compiles candidate CUDA."""
from pathlib import Path
import re,json,hashlib
D=Path(__file__).resolve().parent
# Unpack: same ABI; a thread expands one byte to eight output bytes instead
# of eight threads repeating division/indexing and reloading the same byte.
p=D/'unpackbits';s=(p/'original.ptx').read_text();start=s.index('{',s.index('.visible .entry'))
body='''{
.reg .pred %p<3>;
.reg .b32 %r<8>;
.reg .b64 %rd<12>;
ld.param.u64 %rd1, [cupy_unpackbits_big_param_0];
ld.param.u64 %rd2, [cupy_unpackbits_big_param_1];
ld.param.u64 %rd3, [cupy_unpackbits_big_param_2];
shr.u64 %rd3, %rd3, 3;
mov.u32 %r1, %ctaid.x;
mov.u32 %r2, %ntid.x;
mov.u32 %r3, %tid.x;
mul.wide.u32 %rd4, %r1, %r2;
cvt.u64.u32 %rd5, %r3;
add.u64 %rd4, %rd4, %rd5;
setp.ge.u64 %p1, %rd4, %rd3;
@%p1 bra DONE;
mov.u32 %r4, %nctaid.x;
mul.wide.u32 %rd6, %r4, %r2;
LOOP:
add.u64 %rd7, %rd1, %rd4;
ld.global.u8 %r5, [%rd7];
mov.u64 %rd8, 0;
'''
for j in range(8):
 body+=f'shr.u32 %r6, %r5, {7-j};\nand.b32 %r7, %r6, 1;\ncvt.u64.u32 %rd9, %r7;\nshl.b64 %rd9, %rd9, {8*j};\nor.b64 %rd8, %rd8, %rd9;\n'
body+='''shl.b64 %rd10, %rd4, 3;
add.u64 %rd11, %rd2, %rd10;
st.global.u64 [%rd11], %rd8;
add.u64 %rd4, %rd4, %rd6;
setp.lt.u64 %p2, %rd4, %rd3;
@%p2 bra LOOP;
DONE:
ret;
}
'''
(p/'edited.ptx').write_text(s[:start]+body)
# Pack: normal full-byte domain; remove per-bit redundant bounds branches and
# seven externally unobservable intermediate stores. This alone does not reduce
# unique compulsory DRAM bytes; measure against native/tuned baseline.
p=D/'packbits';s=(p/'original.ptx').read_text()
s=re.sub(r'^\s*@%p(?:19|21|23|25|27|29|31|33) bra[^\n]*\n','',s,flags=re.M)
s=re.sub(r'^\s*st.global.u8\s+\[%rd11\], %rs[1-7];\n','',s,flags=re.M)
(p/'edited.ptx').write_text(s)
for name in ('packbits','unpackbits'):
 p=D/name
 (p/'edit.json').write_text(json.dumps(dict(method='direct frozen PTX text edit',sha256=hashlib.sha256((p/'edited.ptx').read_bytes()).hexdigest(),
  domain=('uint8 contiguous nonaliasing, size positive multiple8 below2^31; output stride1, indexer size=size/8; normal launch' if name=='packbits' else 'uint8 contiguous nonaliasing, output8-aligned, output size=input size*8 below2^31; normal block128, candidate grid ceil(input bytes/128)'),
  strict_accepted=False,proof_status='pending original frontend export'),indent=2)+'\n')
