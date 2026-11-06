#!/usr/bin/env python3
"""Narrow integer differential cases and independent Python byte reference.

ISA source: NVIDIA PTX 8.8 §9.4.1, §9.7.8 and §9.7.9.
No external implementation was consulted. Existing gen.py supplies only the
common kernel/launch ABI, not the independent expected operation results.
"""
import os
import random
import sys
from gen import kernel_text

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
rng = random.Random(20261106)
edge = [0, 1, 7, 8, 15, 16, 17, 31, 32, 63, 64, 127, 128, 255,
        256, 32767, 32768, 65535, 65536, 0xffffffff, 0xffffffffffffffff]
inputs = [(a, b, b) for a in edge for b in edge]
inputs += [(rng.getrandbits(64), rng.getrandbits(64), rng.randrange(40)) for _ in range(512)]
# Return the low 16-bit result, independently from the interpreters' dispatch.
forms = [
    ('and.b16', 'and.b16 %h0, %h1, %h2;', lambda a,b,n: a & b),
    ('or.b16', 'or.b16 %h0, %h1, %h2;', lambda a,b,n: a | b),
    ('xor.b16', 'xor.b16 %h0, %h1, %h2;', lambda a,b,n: a ^ b),
    ('not.b16', 'not.b16 %h0, %h1;', lambda a,b,n: ~a),
    ('mov.b16', 'mov.b16 %h0, %h1;', lambda a,b,n: a),
    ('shl.b16', 'shl.b16 %h0, %h1, %r7;', lambda a,b,n: 0 if n >= 16 else a << n),
    ('shr.b16', 'shr.b16 %h0, %h1, %r7;', lambda a,b,n: 0 if n >= 16 else a >> n),
    ('shr.u16', 'shr.u16 %h0, %h1, %r7;', lambda a,b,n: 0 if n >= 16 else a >> n),
    ('shr.s16', 'shr.s16 %h0, %h1, %r7;', lambda a,b,n: signed(a) >> min(n,15)),
]

def signed(a):
    return a if a < 32768 else a - 65536

for ty in ['u16', 's16', 'b16']:
    forms.append((f'mov.{ty}', f'mov.{ty} %h0, %h1;', lambda a,b,n:a))
    forms.append((f'selp.{ty}', f'setp.ne.s16 %p0, %h1, 0;\nselp.{ty} %h0, %h1, %h2, %p0;', lambda a,b,n:a if a else b))
for dt in ['u16', 's16']:
    for st,reg in [('u16','%h1'),('s16','%h1'),('u32','%r5'),('s32','%r5'),('u64','%rd5'),('s64','%rd5')]:
        forms.append((f'cvt.{dt}.{st}',f'cvt.{dt}.{st} %h0, {reg};',lambda a,b,n:a))

for ty in ['u16', 's16', 'b16']:
    for cmp in ['eq', 'ne'] + ([] if ty == 'b16' else ['lt', 'le', 'gt', 'ge']):
        def ref(a, b, n, ty=ty, cmp=cmp):
            x,y = (signed(a),signed(b)) if ty=='s16' else (a,b)
            yes = {'eq':x==y, 'ne':x!=y, 'lt':x<y, 'le':x<=y, 'gt':x>y, 'ge':x>=y}[cmp]
            return a if yes else b
        forms.append((f'setp.{cmp}.{ty}/selp.u16', f'setp.{cmp}.{ty} %p0, %h1, %h2;\nselp.u16 %h0, %h1, %h2, %p0;', ref))
for cmp in ['lo','ls','hi','hs']:
    def ref(a,b,n,cmp=cmp):
        return a if {'lo':a<b,'ls':a<=b,'hi':a>b,'hs':a>=b}[cmp] else b
    forms.append((f'setp.{cmp}.u16/selp.u16',f'setp.{cmp}.u16 %p0, %h1, %h2;\nselp.u16 %h0, %h1, %h2, %p0;', ref))

with open(out+'/diff.ptx','w') as ptx, open(out+'/cases.txt','w') as cases, open(out+'/expected.txt','w') as expected, open(out+'/forms.txt','w') as descriptions:
    ptx.write('.version 8.0\n.target sm_86\n.address_size 64\n')
    for i,(desc,op,ref) in enumerate(forms):
        k=f'n{i}'
        load_ty = 'u16' if i % 2 else 'b16'
        store_ty = ['u16', 's16', 'b16'][i % 3]
        body = [
            'cvt.u16.u32 %h1, %r5;', 'cvt.u16.u32 %h2, %r6;', op,
            f'st.global.{store_ty} [%rd4+16], %h0;',
            # All relaxed widths, and mixed-width stores with visible frames.
            'ld.global.u8 %h0, [%rd3+1];', 'st.global.u8 [%rd4], %h0;',
            'st.global.u8 [%rd4+1], %r5;',
            f'ld.global.{load_ty} %h0, [%rd3+2];', f'st.global.{store_ty} [%rd4+2], %h0;',
            'ld.global.u8 %r8, [%rd3+1];', 'st.global.u32 [%rd4+4], %r8;',
            f'ld.global.{load_ty} %rd8, [%rd3+2];', 'st.global.u64 [%rd4+8], %rd8;',
            'cvt.u16.u32 %r8, %r5;', 'st.global.u32 [%rd4+20], %r8;',
            'cvt.u64.s16 %rd8, %rd5;', 'st.global.u64 [%rd4+24], %rd8;',
            'cvt.u32.s16 %r8, %r5;', 'st.global.u32 [%rd4+32], %r8;',
            'cvt.u32.u16 %r8, %r5;', 'st.global.u32 [%rd4+36], %r8;',
            'ld.global.u8 %rd8, [%rd3+1];', 'st.global.u64 [%rd4+40], %rd8;',
            'cvt.u16.u32 %rd8, %r5;', 'st.global.u64 [%rd4+48], %rd8;',
            'cvt.u64.u16 %rd8, %rd5;', 'st.global.u64 [%rd4+56], %rd8;',
        ]
        text=kernel_text(k,body).replace('\t.reg .pred', f'\t.reg .{store_ty} %h<3>;\n\t.reg .pred',1).replace('%r4, 48;', '%r4, 64;')
        ptx.write(text)
        descriptions.write(f'{k}\t{desc}; unsigned8/16 loads, truncating stores, signed/unsigned conversion\n')
        # Keep case records small enough for the C runner's fixed line buffer.
        for start in range(0,len(inputs),64):
            batch=inputs[start:start+64]
            raw=b''.join(a.to_bytes(8,'little')+b.to_bytes(8,'little')+n.to_bytes(8,'little') for a,b,n in batch)
            cases.write(f'case {k} 1 1 1 {len(batch)} 1 1 0 {raw.hex()} {len(batch)*64}\n')
            result=bytearray([0xa5]*(len(batch)*64))
            for j,(a,b,n) in enumerate(batch):
                o=j*64
                def put(offset,width,value):
                    result[o+offset:o+offset+width]=(value % (1<<(width*8))).to_bytes(width,'little')
                put(0,1,a>>8); put(1,1,a); put(2,2,a>>16)
                put(4,4,(a>>8)&255); put(8,8,(a>>16)&65535)
                put(16,2,ref(a&65535,b&65535,n&0xffffffff))
                put(20,4,a&65535); put(24,8,signed(a&65535)); put(32,4,signed(a&65535))
                put(36,4,a&65535); put(40,8,(a>>8)&255)
                put(48,8,a&65535); put(56,8,a&65535)
            expected.write(f'result {k} {result.hex()}\n')
print(f'narrow: {len(forms)} kernels, {len(inputs)} inputs each, {len(forms)*len(inputs)} thread cases')
