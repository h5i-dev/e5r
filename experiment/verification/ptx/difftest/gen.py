#!/usr/bin/env python3
"""Generate the differential test of the instruction semantics.

Writes, into the output directory:

  diff.ptx    one kernel per instruction form of the subset, each of which
              reads a per-thread input record, applies the form, and stores
              the result to a per-thread output record;
  forms.txt   kernel name -> the form it tests;
  cases.txt   the launches and their input bytes.

The same cases.txt is run by gpurun (on the GPU) and by the Lean model
(`lake exe ptxdiff`); scripts/check-ptx-difftest.sh compares the outputs
byte for byte. The input values are a fixed list of edge values plus
pseudo-random ones from a fixed seed, so a run is reproducible.

Kernel signature: (.param .u64 in, .param .u64 out, .param .u32 s).
Input record (24 bytes per thread): a, b, c as u64. Output record (48 bytes
per thread), filled with 0xA5 before the launch so the width of every store
is visible.
"""
import os
import random
import sys

TYS = ["u32", "s32", "b32", "u64", "s64", "b64"]
ARITH = ["u32", "s32", "u64", "s64"]
BITS = ["b32", "b64"]
REC_IN, REC_OUT = 24, 48


def w(t):
    return 32 if t.endswith("32") else 64


def regs(t):
    """a, b, c and destination registers at the width of t."""
    return ("%r5", "%r6", "%r7", "%r8") if w(t) == 32 else ("%rd5", "%rd6", "%rd7", "%rd8")


def store(t, d="%r8"):
    return f"st.global.{'u32' if w(t) == 32 else 'u64'} \t[%rd4], {d if w(t) == 32 else '%rd8'};"


PROLOGUE = """\tld.param.u64 \t%rd1, [{k}_in];
\tld.param.u64 \t%rd2, [{k}_out];
\tld.param.u32 \t%r9, [{k}_s];
\tmov.u32 \t%r1, %ctaid.x;
\tmov.u32 \t%r2, %ntid.x;
\tmov.u32 \t%r3, %tid.x;
\tmad.lo.u32 \t%r4, %r1, %r2, %r3;
\tmul.wide.u32 \t%rd3, %r4, 24;
\tadd.u64 \t%rd3, %rd1, %rd3;
\tmul.wide.u32 \t%rd4, %r4, 48;
\tadd.u64 \t%rd4, %rd2, %rd4;
\tld.global.u64 \t%rd5, [%rd3];
\tld.global.u64 \t%rd6, [%rd3+8];
\tld.global.u64 \t%rd7, [%rd3+16];
\tcvt.u32.u64 \t%r5, %rd5;
\tcvt.u32.u64 \t%r6, %rd6;
\tcvt.u32.u64 \t%r7, %rd7;
"""

IMMS32 = ["0", "1", "-1", "7", "0x7fffffff", "-2147483648", "4294967295", "0x80000000"]
IMMS64 = ["0", "1", "-1", "0x7fffffffffffffff", "-9223372036854775808", "18446744073709551615"]


def forms():
    """(form description, body lines)."""
    out = []
    for op in ["add", "sub", "mul.lo"]:
        for t in ARITH:
            a, b, c, d = regs(t)
            out.append((f"{op}.{t} reg", [f"{op}.{t} \t{d}, {a}, {b};", store(t)]))
            for i in IMMS32 if w(t) == 32 else IMMS64:
                out.append((f"{op}.{t} imm {i}", [f"{op}.{t} \t{d}, {a}, {i};", store(t)]))
            out.append((f"{op}.{t} imm-first", [f"{op}.{t} \t{d}, 5, {b};", store(t)]))
    for t in ARITH:
        a, b, c, d = regs(t)
        out.append((f"mad.lo.{t}", [f"mad.lo.{t} \t{d}, {a}, {b}, {c};", store(t)]))
        out.append((f"mad.lo.{t} imm", [f"mad.lo.{t} \t{d}, {a}, -3, {c};", store(t)]))
    for t in ["u32", "s32"]:
        out.append((f"mul.wide.{t}", [f"mul.wide.{t} \t%rd8, %r5, %r6;", store("u64")]))
        for i in ["4", "-1", "0x7fffffff", "4294967295"]:
            out.append((f"mul.wide.{t} imm {i}", [f"mul.wide.{t} \t%rd8, %r5, {i};", store("u64")]))
    for op in ["and", "or", "xor"]:
        for t in BITS:
            a, b, c, d = regs(t)
            out.append((f"{op}.{t}", [f"{op}.{t} \t{d}, {a}, {b};", store(t)]))
            imm = "0xffff0000" if w(t) == 32 else "0xffff0000ffff0000"
            out.append((f"{op}.{t} imm", [f"{op}.{t} \t{d}, {a}, {imm};", store(t)]))
    for t in BITS:
        a, b, c, d = regs(t)
        out.append((f"not.{t}", [f"not.{t} \t{d}, {a};", store(t)]))
    for op, ts in [("shl", BITS), ("shr", TYS)]:
        for t in ts:
            a, b, c, d = regs(t)
            # shift amount is the 32-bit view of c (edge values include >= width)
            out.append((f"{op}.{t} reg", [f"{op}.{t} \t{d}, {a}, %r7;", store(t)]))
            for i in ["0", "1", "31", "32", "63", "64", "100", "-1"]:
                out.append((f"{op}.{t} imm {i}", [f"{op}.{t} \t{d}, {a}, {i};", store(t)]))
    for t in TYS:
        a, b, c, d = regs(t)
        out.append((f"mov.{t}", [f"mov.{t} \t{d}, {a};", store(t)]))
        for i in IMMS32[:4] if w(t) == 32 else IMMS64[:4]:
            out.append((f"mov.{t} imm {i}", [f"mov.{t} \t{d}, {i};", store(t)]))
        out.append((f"selp.{t}", [f"setp.ne.u32 \t%p1, %r7, 0;", f"selp.{t} \t{d}, {a}, {b}, %p1;", store(t)]))
        out.append((f"selp.{t} imm", [f"setp.ne.u32 \t%p1, %r7, 0;", f"selp.{t} \t{d}, 1, -1, %p1;", store(t)]))
        for cmp in ["eq", "ne", "lt", "le", "gt", "ge", "lo", "ls", "hi", "hs"]:
            ordered = cmp not in ("eq", "ne")
            if ordered and t.startswith("b"):
                continue
            if cmp in ("lo", "ls", "hi", "hs") and not t.startswith("u"):
                continue
            out.append((f"setp.{cmp}.{t}", [f"setp.{cmp}.{t} \t%p1, {a}, {b};", "selp.u32 \t%r8, 1, 0, %p1;", store("u32")]))
            out.append((f"setp.{cmp}.{t} a,a", [f"setp.{cmp}.{t} \t%p1, {a}, {a};", "selp.u32 \t%r8, 1, 0, %p1;", store("u32")]))
            imm = "-1" if t.startswith("s") else "0x7fffffff"
            out.append((f"setp.{cmp}.{t} imm", [f"setp.{cmp}.{t} \t%p1, {a}, {imm};", "selp.u32 \t%r8, 1, 0, %p1;", store("u32")]))
    for dt in ARITH:
        for st in ARITH:
            src = regs(st)[0]
            d = regs(dt)[3]
            out.append((f"cvt.{dt}.{st}", [f"cvt.{dt}.{st} \t{d}, {src};", store(dt)]))
    out.append(("cvta.to.global.u64", ["cvta.to.global.u64 \t%rd8, %rd5;", store("u64")]))
    # loads and stores at every type and at offsets
    for t in TYS:
        d = regs(t)[3]
        out.append((f"ld.global.{t}", [f"ld.global.{t} \t{d}, [%rd3+{w(t) // 8}];", store(t)]))
        out.append((f"ld.global.{t} -off", ["add.u64 \t%rd9, %rd3, 16;", f"ld.global.{t} \t{d}, [%rd9+-8];", store(t)]))
        a = regs(t)[0]
        out.append((f"st.global.{t} +off", [f"st.global.{t} \t[%rd4+8], {a};"]))
        out.append((f"st.global.{t} imm", [f"st.global.{t} \t[%rd4+16], -2;"]))
    out.append(("ld.param.u32", ["mov.u32 \t%r8, %r9;", store("u32")]))
    out.append(("ld.param.u32 arith", ["add.u32 \t%r8, %r5, %r9;", store("u32")]))
    # guards and branches
    out.append(("guard @p", ["setp.ne.u32 \t%p1, %r7, 0;", "mov.u32 \t%r8, 11;", "@%p1 mov.u32 \t%r8, %r5;", store("u32")]))
    out.append(("guard @!p", ["setp.ne.u32 \t%p1, %r7, 0;", "mov.u32 \t%r8, 11;", "@!%p1 mov.u32 \t%r8, %r5;", store("u32")]))
    out.append(("guarded store", ["setp.lt.u32 \t%p1, %r7, %r6;", "@%p1 st.global.u32 \t[%rd4], %r5;"]))
    out.append(("guarded ret", ["setp.lt.s32 \t%p1, %r7, 0;", "@%p1 ret;", "st.global.u32 \t[%rd4], %r5;"]))
    out.append(("guarded exit", ["setp.lt.s32 \t%p1, %r7, 0;", "@%p1 exit;", "st.global.u32 \t[%rd4], %r5;"]))
    out.append(("branch", ["setp.ge.u32 \t%p1, %r5, %r6;", "mov.u32 \t%r8, 1;", "@%p1 bra \tLD;", "mov.u32 \t%r8, 2;", "LD:", store("u32")]))
    out.append(("branch @!p", ["setp.ge.u32 \t%p1, %r5, %r6;", "mov.u32 \t%r8, 1;", "@!%p1 bra \tLD;", "mov.u32 \t%r8, 2;", "LD:", store("u32")]))
    # a counted loop: r8 = sum_{k < c mod 16} (a xor k), written each iteration
    out.append(("loop", [
        "and.b32 \t%r7, %r7, 15;", "mov.u32 \t%r8, 0;", "mov.u32 \t%r3, 0;",
        "LL:", "setp.ge.u32 \t%p1, %r3, %r7;", "@%p1 bra \tLE;",
        "xor.b32 \t%r2, %r5, %r3;", "add.u32 \t%r8, %r8, %r2;", "st.global.u32 \t[%rd4+4], %r8;",
        "add.u32 \t%r3, %r3, 1;", "bra.uni \tLL;", "LE:", store("u32")]))
    return out


# M4: every form below may use the shared array sm (8 bytes per thread at
# %r10 = sm + 8 * tid) and %r10..%r15, %rd10..%rd15.
SLOT = ["shl.b32 \t%r10, %r3, 3;", "mov.u32 \t%r11, sm;", "add.u32 \t%r10, %r11, %r10;"]
# a word shared by the whole grid, after every thread's record (OUTEXTRA)
TAIL = ["mov.u32 \t%r12, %nctaid.x;", "mul.lo.u32 \t%r12, %r12, %r2;",
        "mul.wide.u32 \t%rd10, %r12, 48;", "add.u64 \t%rd10, %rd2, %rd10;"]
OUTEXTRA = 16

ATOM_TYS = {"add": ["u32", "s32", "u64"], "min": ARITH, "max": ARITH,
            "exch": BITS, "and": BITS, "or": BITS, "xor": BITS}


def m4_forms():
    """(form description, body lines, needs the grid tail word)."""
    out = []
    for t in TYS:
        a, b, c, d = regs(t)
        out.append((f"st/ld.shared.{t} own slot", SLOT + [f"st.shared.{t} \t[%r10], {a};",
                    f"ld.shared.{t} \t{d}, [%r10];", store(t)], False))
    out.append(("ld.shared +off, 64-bit address", SLOT + ["st.shared.u32 \t[%r10+4], %r5;",
                "cvt.u64.u32 \t%rd11, %r10;", "ld.shared.u32 \t%r8, [%rd11+4];", store("u32")], False))
    out.append(("st.shared.u32 imm", SLOT + ["st.shared.u32 \t[%r10], -7;",
                "ld.shared.u32 \t%r8, [%r10];", store("u32")], False))
    # a value from the next thread, through shared memory and a barrier
    nxt = ["add.u32 \t%r12, %r3, 1;", "setp.eq.u32 \t%p2, %r12, %r2;", "selp.u32 \t%r12, 0, %r12, %p2;",
           "shl.b32 \t%r12, %r12, 3;", "add.u32 \t%r12, %r11, %r12;"]
    out.append(("bar.sync: neighbour's value", SLOT + nxt + ["st.shared.u32 \t[%r10], %r5;", "bar.sync \t0;",
                "ld.shared.u32 \t%r8, [%r12];", store("u32")], False))
    out.append(("bar.sync: two phases", SLOT + nxt + ["st.shared.u64 \t[%r10], %rd5;", "bar.sync \t0;",
                "ld.shared.u64 \t%rd8, [%r12];", "bar.sync \t0;", "st.shared.u64 \t[%r10], %rd6;",
                "bar.sync \t0;", "ld.shared.u64 \t%rd9, [%r12];", "xor.b64 \t%rd8, %rd8, %rd9;", store("u64")], False))
    # interleaved tree reduction over the block, any block size, with the
    # barrier inside the loop
    out.append(("bar.sync in a loop: block sum", SLOT + ["st.shared.u32 \t[%r10], %r5;", "bar.sync \t0;",
                "mov.u32 \t%r12, 1;", "LR:", "setp.ge.u32 \t%p2, %r12, %r2;", "@%p2 bra \tLE;",
                "shl.b32 \t%r13, %r12, 1;", "sub.u32 \t%r14, %r13, 1;", "and.b32 \t%r14, %r3, %r14;",
                "setp.ne.u32 \t%p1, %r14, 0;", "add.u32 \t%r15, %r3, %r12;", "setp.ge.u32 \t%p2, %r15, %r2;",
                "@%p2 mov.u32 \t%r14, 1;",
                "setp.ne.u32 \t%p1, %r14, 0;", "@%p1 bra \tLS;",
                "shl.b32 \t%r15, %r12, 3;", "add.u32 \t%r15, %r10, %r15;", "ld.shared.u32 \t%r6, [%r15];",
                "ld.shared.u32 \t%r7, [%r10];", "add.u32 \t%r7, %r7, %r6;", "st.shared.u32 \t[%r10], %r7;",
                "LS:", "bar.sync \t0;", "mov.u32 \t%r12, %r13;", "bra.uni \tLR;",
                "LE:", "ld.shared.u32 \t%r8, [sm];", store("u32")], False))
    # atomics on a location only this thread touches: old and new values
    # are both determined
    for op, ts in ATOM_TYS.items():
        for t in ts:
            a, b, c, d = regs(t)
            st8 = f"st.global.{t} \t[%rd4+8], {d};"
            out.append((f"atom.global.{op}.{t}", [f"st.global.{t} \t[%rd4], {a};",
                        f"atom.global.{op}.{t} \t{d}, [%rd4], {b};", st8], False))
            out.append((f"atom.shared.{op}.{t}", SLOT + [f"st.shared.{t} \t[%r10], {a};",
                        f"atom.shared.{op}.{t} \t{d}, [%r10], {b};", st8,
                        f"ld.shared.{t} \t{d}, [%r10];", f"st.global.{t} \t[%rd4], {d};"], False))
            if op != "exch":
                out.append((f"red.global.{op}.{t}", [f"st.global.{t} \t[%rd4], {a};",
                            f"red.global.{op}.{t} \t[%rd4], {b};"], False))
                imm = "-2" if t.startswith("s") else "7"
                out.append((f"red.shared.{op}.{t} imm", SLOT + [f"st.shared.{t} \t[%r10], {a};",
                            f"red.shared.{op}.{t} \t[%r10], {imm};", f"ld.shared.{t} \t{d}, [%r10];", store(t)], False))
    for t in BITS:
        a, b, c, d = regs(t)
        st8 = f"st.global.{t} \t[%rd4+8], {d};"
        out.append((f"atom.global.cas.{t} equal", [f"st.global.{t} \t[%rd4], {a};",
                    f"atom.global.cas.{t} \t{d}, [%rd4], {a}, {c};", st8], False))
        out.append((f"atom.global.cas.{t} maybe", [f"st.global.{t} \t[%rd4], {a};",
                    f"atom.global.cas.{t} \t{d}, [%rd4], {b}, {c};", st8], False))
        out.append((f"atom.shared.cas.{t}", SLOT + [f"st.shared.{t} \t[%r10], {a};",
                    f"atom.shared.cas.{t} \t{d}, [%r10], {a}, 5;", st8,
                    f"ld.shared.{t} \t{d}, [%r10];", f"st.global.{t} \t[%rd4], {d};"], False))
    # contended atomics: the final value does not depend on the order
    # (every commutative, associative op at 32 and 64 bits; init is its unit)
    for op, t, init in [("add", "u32", "0"), ("add", "u64", "0"),
                        ("and", "b32", "-1"), ("and", "b64", "-1"), ("or", "b32", "0"), ("or", "b64", "0"),
                        ("xor", "b32", "0"), ("xor", "b64", "0"),
                        ("min", "u32", "-1"), ("min", "s32", "2147483647"),
                        ("min", "u64", "-1"), ("min", "s64", "9223372036854775807"),
                        ("max", "u32", "0"), ("max", "s32", "-2147483648"),
                        ("max", "u64", "0"), ("max", "s64", "-9223372036854775808")]:
        a, b, c, d = regs(t)
        wt = "u32" if w(t) == 32 else "u64"
        out.append((f"contended red.shared.{op}.{t}", ["setp.ne.u32 \t%p1, %r3, 0;",
                    f"@!%p1 st.shared.{wt} \t[sm], {init};", "bar.sync \t0;",
                    f"red.shared.{op}.{t} \t[sm], {a};", "bar.sync \t0;",
                    f"ld.shared.{t} \t{d}, [sm];", store(t)], False))
        out.append((f"contended atom.global.{op}.{t}", TAIL + [f"atom.global.{op}.{t} \t{d}, [%rd10], {a};"], True))
    return out


SREG_KERNEL = """
.visible .entry sregs(
\t.param .u64 sregs_in,
\t.param .u64 sregs_out,
\t.param .u32 sregs_s
)
{{
\t.reg .pred \t%p<3>;
\t.reg .b32 \t%r<24>;
\t.reg .b64 \t%rd<12>;

\tld.param.u64 \t%rd2, [sregs_out];
\tmov.u32 \t%r1, %tid.x;
\tmov.u32 \t%r2, %tid.y;
\tmov.u32 \t%r3, %tid.z;
\tmov.u32 \t%r4, %ntid.x;
\tmov.u32 \t%r5, %ntid.y;
\tmov.u32 \t%r6, %ntid.z;
\tmov.u32 \t%r7, %ctaid.x;
\tmov.u32 \t%r8, %ctaid.y;
\tmov.u32 \t%r9, %ctaid.z;
\tmov.u32 \t%r10, %nctaid.x;
\tmov.u32 \t%r11, %nctaid.y;
\tmov.u32 \t%r12, %nctaid.z;
\tmad.lo.u32 \t%r13, %r9, %r11, %r8;
\tmad.lo.u32 \t%r13, %r13, %r10, %r7;
\tmad.lo.u32 \t%r14, %r3, %r5, %r2;
\tmad.lo.u32 \t%r14, %r14, %r4, %r1;
\tmul.lo.u32 \t%r15, %r4, %r5;
\tmul.lo.u32 \t%r15, %r15, %r6;
\tmad.lo.u32 \t%r16, %r13, %r15, %r14;
\tmul.wide.u32 \t%rd3, %r16, 48;
\tadd.u64 \t%rd4, %rd2, %rd3;
\tst.global.u32 \t[%rd4], %r1;
\tst.global.u32 \t[%rd4+4], %r2;
\tst.global.u32 \t[%rd4+8], %r3;
\tst.global.u32 \t[%rd4+12], %r4;
\tst.global.u32 \t[%rd4+16], %r5;
\tst.global.u32 \t[%rd4+20], %r6;
\tst.global.u32 \t[%rd4+24], %r7;
\tst.global.u32 \t[%rd4+28], %r8;
\tst.global.u32 \t[%rd4+32], %r9;
\tst.global.u32 \t[%rd4+36], %r10;
\tst.global.u32 \t[%rd4+40], %r11;
\tst.global.u32 \t[%rd4+44], %r12;
\tret;
}}
"""


# Misaligned accesses: the model faults, and the GPU must refuse the launch
# (CUDA_ERROR_MISALIGNED_ADDRESS). Out-of-bounds accesses are not tested:
# the GPU only reports those that leave its allocation granularity.
FAULT_FORMS = [
    ("misaligned ld.shared.u32", SLOT + ["ld.shared.u32 \t%r8, [%r10+1];", store("u32")]),
    ("misaligned st.shared.u64", SLOT + ["st.shared.u64 \t[%r10+4], %rd5;"]),
    ("misaligned atom.global.add.u32", ["atom.global.add.u32 \t%r8, [%rd4+2], 1;"]),
    ("misaligned atom.shared.add.u32", SLOT + ["atom.shared.add.u32 \t%r8, [%r10+1], 1;"]),
    ("misaligned red.global.add.u64", ["red.global.add.u64 \t[%rd4+4], 1;"]),
    ("misaligned ld.global.u32", ["ld.global.u32 \t%r8, [%rd3+1];", store("u32")]),
    ("misaligned ld.global.u64", ["ld.global.u64 \t%rd8, [%rd3+4];", store("u64")]),
    ("misaligned ld.global.s32", ["ld.global.s32 \t%r8, [%rd3+2];", store("u32")]),
    ("misaligned st.global.u32", ["st.global.u32 \t[%rd4+3], %r5;"]),
    ("misaligned st.global.b64", ["st.global.b64 \t[%rd4+12], %rd5;"]),
]


def kernel_text(name, body):
    lines = []
    for l in body:
        lines.append(l if l.endswith(":") else "\t" + l)
    shared = any("sm" in l for l in body)
    regs, rregs = "%r<16>", "%rd<16>"
    decl = "\t.shared .align 8 .b8 \tsm[1024];\n" if shared else ""
    fdecl = "\t.reg .f32 \t%f<8>;\n\t.reg .f64 \t%fd<8>;\n" if any("%f" in l for l in body) else ""
    return (
        f"\n.visible .entry {name}(\n\t.param .u64 {name}_in,\n\t.param .u64 {name}_out,\n"
        f"\t.param .u32 {name}_s\n)\n{{\n\t.reg .pred \t%p<3>;\n\t.reg .b32 \t{regs};\n"
        f"\t.reg .b64 \t{rregs};\n{fdecl}{decl}\n" + PROLOGUE.format(k=name) + "\n".join(lines) + "\n\tret;\n}\n"
    )


# Floating point. a, b, c are the bit patterns of the inputs (the low 32 bits
# for .f32); a float result is stored with every NaN replaced by one
# canonical pattern first (setp.nan, selp), because PTX leaves the bits of a
# NaN result unspecified and the model takes them from an oracle. Every other
# result is compared bit for bit.
RNDS = ["rn", "rz", "rm", "rp"]


def fregs(t):
    return ("%f1", "%f2", "%f3", "%f4") if t == "f32" else ("%fd1", "%fd2", "%fd3", "%fd4")


def fload(t):
    if t == "f32":
        return ["mov.b32 \t%f1, %r5;", "mov.b32 \t%f2, %r6;", "mov.b32 \t%f3, %r7;"]
    return ["mov.b64 \t%fd1, %rd5;", "mov.b64 \t%fd2, %rd6;", "mov.b64 \t%fd3, %rd7;"]


def fstore(t, d=None):
    d = d or fregs(t)[3]
    if t == "f32":
        return ["setp.nan.f32 \t%p2, " + d + ", " + d + ";", "mov.b32 \t%r8, " + d + ";",
                "selp.b32 \t%r8, 2147483647, %r8, %p2;", "st.global.u32 \t[%rd4], %r8;"]
    return ["setp.nan.f64 \t%p2, " + d + ", " + d + ";", "mov.b64 \t%rd8, " + d + ";",
            "selp.b64 \t%rd8, 9223372036854775807, %rd8, %p2;", "st.global.u64 \t[%rd4], %rd8;"]


def fmods(ftz, sat):
    return (".ftz" if ftz else "") + (".sat" if sat else "")


def float_forms():
    """(description, body, float width) for every float form of the subset."""
    out = []
    for t in ["f32", "f64"]:
        a, b, c, d = fregs(t)
        fl = ["ftz/sat"] if t == "f32" else [None]
        combos = [(f, s) for f in (False, True) for s in (False, True)] if t == "f32" else [(False, False)]
        for op in ["add", "sub", "mul"]:
            for r in RNDS:
                for ftz, sat in combos:
                    m = f"{op}.{r}{fmods(ftz, sat)}.{t}"
                    out.append((m, fload(t) + [f"{m} \t{d}, {a}, {b};"] + fstore(t), t))
        for r in RNDS:
            for ftz, sat in combos:
                m = f"fma.{r}{fmods(ftz, sat)}.{t}"
                out.append((m, fload(t) + [f"{m} \t{d}, {a}, {b}, {c};"] + fstore(t), t))
        ftzs = [False, True] if t == "f32" else [False]
        for op in ["div", "sqrt", "rcp"]:
            for r in RNDS:
                for ftz in ftzs:
                    m = f"{op}.{r}{fmods(ftz, False)}.{t}"
                    args = f"{a}, {b}" if op == "div" else a
                    out.append((m, fload(t) + [f"{m} \t{d}, {args};"] + fstore(t), t))
        for op in ["neg", "abs"]:
            for ftz in ftzs:
                m = f"{op}{fmods(ftz, False)}.{t}"
                out.append((m, fload(t) + [f"{m} \t{d}, {a};"] + fstore(t), t))
        for op in ["min", "max"]:
            for ftz in ftzs:
                for nan in ([False, True] if t == "f32" else [False]):
                    m = f"{op}{fmods(ftz, False)}{'.NaN' if nan else ''}.{t}"
                    out.append((m, fload(t) + [f"{m} \t{d}, {a}, {b};"] + fstore(t), t))
        for cmp in ["eq", "ne", "lt", "le", "gt", "ge", "equ", "neu", "ltu", "leu", "gtu", "geu", "num", "nan"]:
            for ftz in ftzs:
                m = f"setp.{cmp}{fmods(ftz, False)}.{t}"
                out.append((m, fload(t) + [f"{m} \t%p1, {a}, {b};", "selp.u32 \t%r8, 1, 0, %p1;",
                                           store("u32")], t))
        # literals, moves, loads and stores at the float type
        lit = "0f3FC00000" if t == "f32" else "0d3FF8000000000000"
        out.append((f"fma.rn.{t} literal", fload(t) + [f"fma.rn.{t} \t{d}, {a}, {lit}, {b};"] + fstore(t), t))
        out.append((f"mov.{t}", fload(t) + [f"mov.{t} \t{d}, {a};"] + fstore(t), t))
        out.append((f"mov.{t} literal", fload(t) + [f"mov.{t} \t{d}, {lit};"] + fstore(t), t))
        out.append((f"selp.{t}", fload(t) + ["setp.ne.u32 \t%p1, %r7, 0;", f"selp.{t} \t{d}, {a}, {b}, %p1;"]
                    + fstore(t), t))
        sz = 4 if t == "f32" else 8
        out.append((f"ld/st.global.{t}", [f"ld.global.{t} \t{d}, [%rd3+{sz}];",
                                          f"st.global.{t} \t[%rd4+8], {d};"] + fstore(t), t))
        # integer to float, every rounding
        for st in ARITH:
            src = regs(st)[0]
            for r in RNDS:
                for sat in ([False, True] if t == "f32" else [False]):
                    m = f"cvt.{r}{fmods(False, sat)}.{t}.{st}"
                    out.append((m, [f"{m} \t{d}, {src};"] + fstore(t), "i" + t))
        # float to integer, every integer rounding
        for dt in ARITH:
            dst = regs(dt)[3]
            for r in RNDS:
                for ftz in ftzs:
                    m = f"cvt.{r}i{fmods(ftz, False)}.{dt}.{t}"
                    out.append((m, fload(t) + [f"{m} \t{dst}, {a};", store(dt)], t))
        # round to an integral value
        for r in RNDS:
            for ftz in ftzs:
                m = f"cvt.{r}i{fmods(ftz, False)}.{t}.{t}"
                out.append((m, fload(t) + [f"{m} \t{d}, {a};"] + fstore(t), t))
    for ftz, sat in [(False, False), (True, False), (False, True)]:
        m = f"cvt{fmods(ftz, sat)}.f64.f32"
        out.append((m, fload("f32") + [f"{m} \t%fd4, %f1;"] + fstore("f64"), "f32"))
    for r in RNDS:
        for ftz, sat in [(False, False), (True, False), (False, True), (True, True)]:
            m = f"cvt.{r}{fmods(ftz, sat)}.f32.f64"
            out.append((m, fload("f64") + [f"{m} \t%f4, %fd1;"] + fstore("f32"), "f64"))
    return out


# Float inputs: special values, the subnormal and overflow boundaries, values
# one unit in the last place apart, and random patterns, random normal
# numbers of moderate exponent, and pairs chosen to cancel.
F32_EDGE = [0x00000000, 0x80000000, 0x00000001, 0x80000001, 0x007FFFFF, 0x807FFFFF, 0x00800000,
            0x80800000, 0x00800001, 0x3F800000, 0xBF800000, 0x3F7FFFFF, 0x3F800001, 0x3FC00000,
            0x40000000, 0x3F000000, 0x3EAAAAAB, 0x7F7FFFFF, 0xFF7FFFFF, 0x7F000000, 0x7F800000,
            0xFF800000, 0x7FC00000, 0xFFC00000, 0x7FC12345, 0x7F800001, 0xFF800001, 0x4B000000,
            0x4B7FFFFF, 0x4F000000, 0x4F800000, 0x5F000000, 0x5F800000, 0xCF000000, 0xDF000000,
            0x3F7FFFFE, 0xB2800000, 0x00400000, 0x34000000, 0x33800000, 0x3EFFFFFF, 0x3F400000,
            0x40400000, 0x4EFFFFFF, 0xCF000001]
F64_EDGE = [0x0, 0x8000000000000000, 0x1, 0x8000000000000001, 0x000FFFFFFFFFFFFF, 0x0010000000000000,
            0x8010000000000000, 0x3FF0000000000000, 0xBFF0000000000000, 0x3FEFFFFFFFFFFFFF,
            0x3FF0000000000001, 0x3FF8000000000000, 0x4000000000000000, 0x3FE0000000000000,
            0x3FD5555555555555, 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, 0x7FE0000000000000,
            0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0xFFF8000000000000,
            0x7FF8000000012345, 0x7FF0000000000001, 0x4330000000000000, 0x433FFFFFFFFFFFFF,
            0x41E0000000000000, 0x41F0000000000000, 0x43E0000000000000, 0x43F0000000000000,
            0xC1E0000000000000, 0xC3E0000000000000, 0x3CA0000000000000, 0x3CB0000000000000,
            0x3690000000000000, 0x380FFFFFFFFFFFFF, 0x3800000000000000, 0x47EFFFFFE0000000,
            0x47EFFFFFF0000000, 0x47F0000000000000, 0x36A0000000000000, 0xC1E0000000200000]


def fvalues(rng, n, t):
    """n (a, b, c) bit-pattern triples for format t ('f32', 'f64', or 'if32'
    and 'if64' for integer-to-float, whose inputs are integers)."""
    if t.startswith("i"):
        return [(rng.choice([rng.getrandbits(64), rng.choice(EDGE64), rng.getrandbits(rng.randrange(1, 64))]),
                 0, 0) for _ in range(n)]
    w = 32 if t == "f32" else 64
    fb, eb = (23, 8) if w == 32 else (52, 11)
    edge = F32_EDGE if w == 32 else F64_EDGE
    bias = (1 << (eb - 1)) - 1

    def normal(lo, hi):
        e = rng.randrange(lo, hi) + bias
        return (rng.getrandbits(1) << (w - 1)) | (e << fb) | rng.getrandbits(fb)

    def one():
        k = rng.randrange(8)
        if k == 0:
            return rng.choice(edge)
        if k == 1:
            return rng.getrandbits(w)
        if k == 2:  # near the subnormal boundary
            return normal(-bias - 2 + 3, -bias + 6) if rng.randrange(2) else rng.getrandbits(fb)
        if k == 3:  # near overflow
            return normal(bias - 4, bias + 1)
        return normal(-30, 30)

    pairs = [(x, y) for x in edge for y in edge]
    rng.shuffle(pairs)
    out = []
    for i in range(n):
        if i < min(len(pairs), n // 2):
            a, b = pairs[i]
            c = rng.choice(edge) if rng.randrange(2) else one()
        else:
            a, b, c = one(), one(), one()
            k = rng.randrange(6)
            if k == 0:  # b one or two units in the last place from ±a: cancellation
                b = (a ^ (1 << (w - 1))) + rng.choice([-2, -1, 0, 1, 2])
                b &= (1 << w) - 1
            elif k == 1:  # c close to -(a*b): fma cancellation
                c = (b ^ (1 << (w - 1)))
        out.append((a, b, c))
    return out


EDGE64 = [0, 1, 2, 3, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF,
          0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFF80000000,
          0x00000000FFFFFFFE, 31, 32, 33, 63, 64, 65, 100]


def values(rng, n):
    """n (a, b, c) triples: edge-value products first, then random."""
    out = []
    for i in range(n):
        if i < len(EDGE64) * 3:
            a = EDGE64[i % len(EDGE64)]
            b = EDGE64[(i // len(EDGE64) * 7 + i) % len(EDGE64)]
        else:
            k = rng.randrange(4)
            a = rng.getrandbits(64) if k else rng.choice(EDGE64)
            b = rng.getrandbits(64) if k != 1 else rng.choice(EDGE64)
            if rng.randrange(3) == 0:  # sign-extended 32-bit values
                a = (a & 0xFFFFFFFF) | (0xFFFFFFFF00000000 if a & 0x80000000 else 0)
        c = rng.choice([0, 1, 5, 15, 31, 32, 33, 63, 64, 65, 100, 0xFFFFFFFF, rng.getrandbits(32),
                        rng.getrandbits(64)])
        if rng.randrange(4) == 0:
            c |= 0x80000000
        out.append((a, b, c))
    return out


def main():
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)
    rng = random.Random(20261101)
    fs = [(d, b, False) for d, b in forms()] + m4_forms()
    ffs = float_forms()
    nint = len(fs)
    fs += [("float: " + d, b, False) for d, b, _ in ffs]
    with open(os.path.join(outdir, "diff.ptx"), "w") as f:
        f.write("// Generated by verification/ptx/difftest/gen.py. Do not edit.\n")
        f.write(".version 8.0\n.target sm_86\n.address_size 64\n")
        for i, (_, body, _) in enumerate(fs):
            f.write(kernel_text(f"d{i}", body))
        f.write(SREG_KERNEL.format())
        for i, (_, body) in enumerate(FAULT_FORMS):
            f.write(kernel_text(f"f{i}", body))
    with open(os.path.join(outdir, "forms.txt"), "w") as f:
        for i, (desc, _, _) in enumerate(fs):
            f.write(f"d{i}\t{desc}\n")
        f.write("sregs\tspecial registers, 3-D launch\n")
        for i, (desc, _) in enumerate(FAULT_FORMS):
            f.write(f"f{i}\t{desc}\n")
    # launches: (grid, block)
    launches = [((2, 1, 1), (64, 1, 1)), ((1, 1, 1), (96, 1, 1))]
    with open(os.path.join(outdir, "cases.txt"), "w") as f:
        for i, (_, _, tail) in enumerate(fs):
            if i >= nint:
                ft = ffs[i - nint][2]
                fl = [((8, 1, 1), (256, 1, 1)), ((1, 1, 1), (128, 1, 1))]
                allv = fvalues(rng, sum(g[0] * b[0] for g, b in fl), ft)
                at = 0
                for (g, b) in fl:
                    n = g[0] * b[0]
                    vals, at = allv[at:at + n], at + n
                    inb = b"".join(x.to_bytes(8, "little") + y.to_bytes(8, "little") + z.to_bytes(8, "little")
                                   for x, y, z in vals)
                    f.write(f"case d{i} {' '.join(map(str, g))} {' '.join(map(str, b))} 0 {inb.hex()} {n * REC_OUT}\n")
                continue
            for (g, b) in launches:
                n = g[0] * g[1] * g[2] * b[0] * b[1] * b[2]
                vals = values(rng, n)
                inb = b"".join(x.to_bytes(8, "little") + y.to_bytes(8, "little") + z.to_bytes(8, "little")
                               for x, y, z in vals)
                s = rng.getrandbits(32)
                outn = n * REC_OUT + (OUTEXTRA if tail else 0)
                f.write(f"case d{i} {' '.join(map(str, g))} {' '.join(map(str, b))} {s} {inb.hex()} {outn}\n")
        for (g, b) in [((2, 3, 2), (4, 2, 3)), ((1, 1, 1), (1, 1, 1)), ((3, 1, 1), (2, 5, 1))]:
            n = g[0] * g[1] * g[2] * b[0] * b[1] * b[2]
            f.write(f"case sregs {' '.join(map(str, g))} {' '.join(map(str, b))} 0 00 {n * REC_OUT}\n")
    with open(os.path.join(outdir, "faults.txt"), "w") as f:
        for i in range(len(FAULT_FORMS)):
            vals = values(rng, 32)
            inb = b"".join(x.to_bytes(8, "little") + y.to_bytes(8, "little") + z.to_bytes(8, "little")
                           for x, y, z in vals)
            f.write(f"case f{i} 1 1 1 32 1 1 0 {inb.hex()} {32 * REC_OUT}\n")
    print(f"{len(fs) + 1 + len(FAULT_FORMS)} kernels ({len(ffs)} float), {nint * len(launches) + 2 * len(ffs) + 3} launches, "
          f"{len(FAULT_FORMS)} fault launches")


if __name__ == "__main__":
    main()
