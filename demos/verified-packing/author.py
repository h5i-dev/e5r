"""Emit directly authored PTX text and identical per-kernel JSON contracts.
No CUDA compiler is used to generate candidate PTX.
"""
from pathlib import Path
import json
HERE = Path(__file__).resolve().parent
for op in ('pack', 'unpack', 'threshold'):
    lines = ['.version 8.0', '.target sm_86', '.address_size 64',
             f'.visible .entry {op}(.param .u64 input, .param .u64 output, .param .u32 n)', '{',
             '.reg .pred %p<3>;', '.reg .b32 %r<64>;', '.reg .b64 %rd<8>;',
             'ld.param.u64 %rd1, [input];', 'ld.param.u64 %rd2, [output];',
             'ld.param.u32 %r1, [n];', 'mov.u32 %r2, %ctaid.x;',
             'mov.u32 %r3, %ntid.x;', 'mov.u32 %r4, %tid.x;',
             'mad.lo.u32 %r5, %r2, %r3, %r4;',
             'setp.ge.u32 %p1, %r5, %r1;', '@%p1 bra DONE;',
             f'mul.wide.u32 %rd3, %r5, {4 if op == "unpack" else 32};',
             f'mul.wide.u32 %rd4, %r5, {32 if op == "unpack" else 4};',
             'add.u64 %rd5, %rd1, %rd3;', 'add.u64 %rd6, %rd2, %rd4;']
    if op == 'unpack':
        # Each thread writes four contiguous bytes. Eight threads reuse one
        # aligned packed word; shared reads are safe and cache-friendly.
        lines = lines[:lines.index('mul.wide.u32 %rd3, %r5, 4;')]
        lines += ['shr.u32 %r10, %r5, 3;', 'and.b32 %r11, %r5, 7;',
                  'shl.b32 %r11, %r11, 2;',
                  'mul.wide.u32 %rd3, %r10, 4;', 'mul.wide.u32 %rd4, %r5, 4;',
                  'add.u64 %rd5, %rd1, %rd3;', 'add.u64 %rd6, %rd2, %rd4;',
                  'ld.global.u32 %r6, [%rd5];', 'shr.u32 %r7, %r6, %r11;',
                  'and.b32 %r7, %r7, 15;',
                  'shl.b32 %r8, %r7, 14;', 'or.b32 %r7, %r7, %r8;',
                  'and.b32 %r7, %r7, 196611;',
                  'shl.b32 %r8, %r7, 7;', 'or.b32 %r7, %r7, %r8;',
                  'and.b32 %r7, %r7, 16843009;', 'st.global.u32 [%rd6], %r7;']
    else:
        lines += ['mov.u32 %r7, 0;']
        for j in range(8):
            lines += [f'ld.global.u32 %r6, [%rd5+{4*j}];']
            for k in range(4):
                mask = (128 if op == 'threshold' else 255) << (8*k)
                lines += [f'and.b32 %r8, %r6, {mask};', 'setp.ne.u32 %p2, %r8, 0;',
                          f'selp.u32 %r9, {1 << (4*j+k)}, 0, %p2;', 'or.b32 %r7, %r7, %r9;']
        lines += ['st.global.u32 [%rd6], %r7;']
    lines += ['DONE:', 'ret;', '}']
    (HERE / f'{op}.ptx').write_text('\n'.join(lines)+'\n')
    (HERE / f'{op}.json').write_text(json.dumps(dict(schema='e5r.ptx.spec.v1',
        kernel=op, **{'class': 'packing'}, op=op, input='input', output='output', length='n'), indent=2)+'\n')
