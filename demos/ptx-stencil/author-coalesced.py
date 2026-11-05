"""Direct instruction templates for this concrete stencil; never compile CUDA."""
from pathlib import Path

D = Path(__file__).resolve().parent
HEADER = '''// Agent-authored direct PTX, 17-tap uint32 stencil, four outputs/thread.
.version 9.2
.target sm_86
.address_size 64
.visible .entry stencil17(
 .param .u64 stencil17_param_0,
 .param .u64 stencil17_param_1,
 .param .u32 stencil17_param_2
) {
.reg .pred %p<8>;
.reg .b32 %r<90>;
.reg .b64 %rd<30>;
'''
PARAMS = '''ld.param.u64 %rd1, [stencil17_param_0];
ld.param.u64 %rd2, [stencil17_param_1];
ld.param.u32 %r2, [stencil17_param_2];
mov.u32 %r3, %ntid.x;
mov.u32 %r4, %ctaid.x;
mov.u32 %r5, %tid.x;
'''
STRIPED_INDEX = '''// 64-bit arithmetic also handles inactive oversized launches without wrap.
mul.wide.u32 %rd10, %r4, %r3;
shl.b64 %rd10, %rd10, 2;
cvt.u64.u32 %rd11, %r5;
add.u64 %rd10, %rd10, %rd11;
cvt.u64.u32 %rd12, %r2;
cvt.u64.u32 %rd13, %r3;
'''


def striped():
    s = HEADER + PARAMS + STRIPED_INDEX
    for k in range(4):
        s += 'setp.ge.u64 %p1, %rd10, %rd12;\n@%p1 bra DONE;\n'
        s += 'shl.b64 %rd14, %rd10, 2;\nadd.u64 %rd6, %rd1, %rd14;\nadd.u64 %rd7, %rd2, %rd14;\n'
        s += 'mov.u32 %r40, 0;\n'
        for j in range(17):
            s += f'ld.global.u32 %r10, [%rd6+{4*j}];\nadd.u32 %r40, %r40, %r10;\n'
        s += 'st.global.u32 [%rd7], %r40;\n'
        if k < 3:
            s += 'add.u64 %rd10, %rd10, %rd13;\n'
    return s + 'DONE:\nret;\n}\n'


def staged():
    # Keep the existing concrete rolling instruction sequence. Replace its
    # stores with block-local staging; every path reaches the same barrier.
    old = (D / 'edited.ptx').read_text()
    body = old[old.index('ld.param.u64'):old.index('DONE:')]
    body = body.replace('bra DONE;', 'bra BARRIER;')
    setup = 'mov.u32 %r70, stage;\nshl.b32 %r71, %r5, 4;\nadd.u32 %r70, %r70, %r71;\n'
    body = body.replace('ld.global.u32 %r10,', setup + 'ld.global.u32 %r10,', 1)
    for j in range(4):
        old_store = 'st.global.u32 [%rd7' + (f'+{4*j}' if j else '') + '], %r40;'
        new_store = 'st.shared.u32 [%r70' + (f'+{4*j}' if j else '') + '], %r40;'
        assert old_store in body, old_store
        body = body.replace(old_store, new_store)
    s = HEADER + '.shared .align 8 .b8 stage[8192];\n' + body
    s += 'BARRIER:\nbar.sync 0;\n' + STRIPED_INDEX
    s += 'mov.u32 %r70, stage;\nmov.u32 %r71, %r5;\n'
    for k in range(4):
        s += 'setp.ge.u64 %p1, %rd10, %rd12;\n@%p1 bra DONE;\n'
        s += 'shl.b32 %r72, %r71, 2;\nadd.u32 %r72, %r70, %r72;\n'
        s += 'ld.shared.u32 %r40, [%r72];\n'
        s += 'shl.b64 %rd14, %rd10, 2;\nadd.u64 %rd7, %rd2, %rd14;\nst.global.u32 [%rd7], %r40;\n'
        if k < 3:
            s += 'add.u64 %rd10, %rd10, %rd13;\nadd.u32 %r71, %r71, %r3;\n'
    return s + 'DONE:\nret;\n}\n'


def input_tiled(four):
    count = 4 if four else 1
    s = HEADER + f'.shared .align 4 .b8 stage[{4*(512*count+16)}];\n' + PARAMS
    s += 'mul.wide.u32 %rd10, %r4, %r3;\n'
    if four:
        s += 'shl.b64 %rd10, %rd10, 2;\n'
    s += '''cvt.u64.u32 %rd11, %r5;
add.u64 %rd10, %rd10, %rd11;
cvt.u64.u32 %rd12, %r2;
add.u64 %rd15, %rd12, 16;
cvt.u64.u32 %rd13, %r3;
mov.u32 %r70, stage;
mov.u32 %r71, %r5;
'''
    for k in range(count):
        s += f'''mov.u32 %r40, 0;
setp.ge.u64 %p1, %rd10, %rd15;
@%p1 bra LOAD_{k}_END;
shl.b64 %rd14, %rd10, 2;
add.u64 %rd6, %rd1, %rd14;
ld.global.u32 %r40, [%rd6];
LOAD_{k}_END:
shl.b32 %r72, %r71, 2;
add.u32 %r72, %r70, %r72;
st.shared.u32 [%r72], %r40;
add.u64 %rd10, %rd10, %rd13;
add.u32 %r71, %r71, %r3;
'''
    s += '''setp.ge.u32 %p1, %r5, 16;
@%p1 bra LOADED;
mov.u32 %r40, 0;
setp.ge.u64 %p1, %rd10, %rd15;
@%p1 bra HALO_END;
shl.b64 %rd14, %rd10, 2;
add.u64 %rd6, %rd1, %rd14;
ld.global.u32 %r40, [%rd6];
HALO_END:
shl.b32 %r72, %r71, 2;
add.u32 %r72, %r70, %r72;
st.shared.u32 [%r72], %r40;
LOADED:
bar.sync 0;
mul.wide.u32 %rd10, %r4, %r3;
'''
    if four:
        s += 'shl.b64 %rd10, %rd10, 2;\n'
    s += 'add.u64 %rd10, %rd10, %rd11;\nmov.u32 %r71, %r5;\n'
    for k in range(count):
        s += '''setp.ge.u64 %p1, %rd10, %rd12;
@%p1 bra DONE;
shl.b32 %r72, %r71, 2;
add.u32 %r72, %r70, %r72;
mov.u32 %r40, 0;
'''
        for j in range(17):
            s += f'ld.shared.u32 %r10, [%r72+{4*j}];\nadd.u32 %r40, %r40, %r10;\n'
        s += 'shl.b64 %rd14, %rd10, 2;\nadd.u64 %rd7, %rd2, %rd14;\nst.global.u32 [%rd7], %r40;\n'
        if k < count-1:
            s += 'add.u64 %rd10, %rd10, %rd13;\nadd.u32 %r71, %r71, %r3;\n'
    return s + 'DONE:\nret;\n}\n'


if __name__ == '__main__':
    (D / 'striped.ptx').write_text(striped())
    (D / 'staged.ptx').write_text(staged())
    (D / 'tiled.ptx').write_text(input_tiled(False))
    (D / 'tiled4.ptx').write_text(input_tiled(True))
