#!/usr/bin/env python3
"""Decoder sweep: the model's decode16/decode32 against binutils objdump.

Original review code, Apache-2.0. Every 16-bit parcel (the 49152 with low
bits != 11) and a seeded sample of 32-bit words (half with an in-scope major
opcode, half any major opcode, plus every SYSTEM funct12 with zero fields and
every AMO funct5) are disassembled by objdump for rv32imac_zicsr_zifencei
(`-M no-aliases,numeric`) and decoded by the model (review/DecodeSweep.lean).
objdump's text is mapped to the model's canonical form here, with the RVC
expansions written from the RVC table of the unprivileged spec (chapter
"C" Standard Extension, 20240411).

Outcomes per encoding:
  agree         both decode, to the same instruction
  both-illegal  objdump: not an instruction of the ISA; model: none
  e31-illegal   objdump decodes a privileged instruction the E31 does not
                implement (no S/U-mode/debug): model none is right
  WRONG         the model decodes something objdump rejects, or decodes it as
                another instruction (unsound direction: silent success)
  STRICT        objdump decodes an ISA instruction the model rejects (traps:
                conservative, but recorded)

Usage: decode_sweep.py [--samples N] [--seed S] [--out DIR] [--summary F] [--controls]
Exit 0 iff there is no WRONG. --controls instead builds decoder mutants in a
scratch copy and requires each to produce WRONG (exit 1); a mutant that does
not build is a failure of the controls, not a rejection.
"""
import argparse
import collections
import json
import os
from pathlib import Path
import random
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ARCH = 'rv32imac_zicsr_zifencei'
IN_SCOPE = [0x37, 0x17, 0x6f, 0x67, 0x63, 0x03, 0x23, 0x13, 0x33, 0x0f, 0x73, 0x2f]
# Privileged/debug instructions objdump knows that need S-, U- or debug mode,
# or a hypervisor; the E31 (M-mode only) raises illegal instruction for them.
E31_ILLEGAL = {'sfence.vm', 'hret', 'sret', 'uret', 'dret', 'sfence.vma', 'sinval.vma', 'sfence.w.inval',
               'sfence.inval.ir', 'hfence.vvma', 'hfence.gvma', 'hinval.vvma', 'hinval.gvma'}
ILLEGAL_TEXT = ('.insn', '.2byte', '.4byte', '.short', '.word', 'c.unimp', '0x')


def tools_env():
    sys.path.insert(0, str(HERE))
    from harness import tools_env as te
    return te()


def h32(v):
    return format(v & 0xffffffff, 'x')


def reg(s):
    assert s[0] == 'x', s
    return int(s[1:])


def memop(s):
    m = re.fullmatch(r'(-?(?:0x)?[0-9a-f]+)\((x\d+)\)', s)
    return int(m[1], 0), reg(m[2])


ALU_I = {'addi': 'add', 'slti': 'slt', 'sltiu': 'sltu', 'xori': 'xor', 'ori': 'or', 'andi': 'and',
         'slli': 'sll', 'srli': 'srl', 'srai': 'sra'}
ALU_R = {'add', 'sub', 'sll', 'slt', 'sltu', 'xor', 'srl', 'sra', 'or', 'and'}
MUL = {'mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu'}
BR = {'beq': 'eq', 'bne': 'ne', 'blt': 'lt', 'bge': 'ge', 'bltu': 'ltu', 'bgeu': 'geu'}
LD = {'lb': ('b', 'true'), 'lh': ('h', 'true'), 'lw': ('w', 'true'), 'lbu': ('b', 'false'),
      'lhu': ('h', 'false')}
ST = {'sb': 'b', 'sh': 'h', 'sw': 'w'}
AMO = {'swap', 'add', 'xor', 'and', 'or', 'min', 'max', 'minu', 'maxu'}


def canon(pc, mn, ops, csrs):
    """objdump mnemonic and operands -> the model's canonical form, or a
    category string starting with '!'."""
    a = ops.split(',') if ops else []
    base = re.sub(r'\.(aqrl|aq|rl)$', '', mn)
    if mn == 'unimp':
        # The canonical 32-bit unimp is csrrw x0,cycle,x0: a write to a
        # read-only CSR, which exec (not decode) must turn into a trap.
        return 'csr rw 0 r0 c00'
    if mn in E31_ILLEGAL:
        return '!e31'
    if mn.startswith(ILLEGAL_TEXT) or mn.startswith('.'):
        return '!illegal'
    # RVC, expanded per the spec's table.
    if mn.startswith('c.'):
        c = mn[2:]
        if c == 'addi4spn':
            return f'opimm add {reg(a[0])} 2 {h32(int(a[2], 0))}'
        if c == 'lw':
            off, rs1 = memop(a[1]); return f'load w true {reg(a[0])} {rs1} {h32(off)}'
        if c == 'sw':
            off, rs1 = memop(a[1]); return f'store w {rs1} {reg(a[0])} {h32(off)}'
        if c == 'nop':
            return f'opimm add 0 0 {h32(int(a[0], 0) if a else 0)}'
        if c == 'addi':
            return f'opimm add {reg(a[0])} {reg(a[0])} {h32(int(a[1], 0))}'
        if c == 'jal':
            return f'jal 1 {h32(int(a[0], 0) - pc)}'
        if c == 'li':
            return f'opimm add {reg(a[0])} 0 {h32(int(a[1], 0))}'
        if c == 'addi16sp':
            return f'opimm add 2 2 {h32(int(a[1], 0))}'
        if c == 'lui':
            v = int(a[1], 0)          # nzimm[17:12], printed as a 20-bit field
            v = v - (1 << 20) if v & (1 << 19) else v
            return f'lui {reg(a[0])} {h32(v << 12)}'
        if c in ('srli', 'srai', 'andi', 'slli'):
            op = {'srli': 'srl', 'srai': 'sra', 'andi': 'and', 'slli': 'sll'}[c]
            return f'opimm {op} {reg(a[0])} {reg(a[0])} {h32(int(a[1], 0))}'
        if c in ('sub', 'xor', 'or', 'and'):
            return f'op {c} {reg(a[0])} {reg(a[0])} {reg(a[1])}'
        if c == 'j':
            return f'jal 0 {h32(int(a[0], 0) - pc)}'
        if c in ('beqz', 'bnez'):
            return f'branch {"eq" if c == "beqz" else "ne"} {reg(a[0])} 0 {h32(int(a[1], 0) - pc)}'
        if c == 'lwsp':
            off, _ = memop(a[1]); return f'load w true {reg(a[0])} 2 {h32(off)}'
        if c == 'swsp':
            off, _ = memop(a[1]); return f'store w 2 {reg(a[0])} {h32(off)}'
        if c == 'jr':
            return f'jalr 0 {reg(a[0])} 0'
        if c == 'jalr':
            return f'jalr 1 {reg(a[0])} 0'
        if c == 'mv':
            return f'op add {reg(a[0])} 0 {reg(a[1])}'
        if c == 'add':
            return f'op add {reg(a[0])} {reg(a[0])} {reg(a[1])}'
        if c == 'ebreak':
            return 'ebreak'
        if c in ('slli64', 'srli64', 'srai64'):
            # shamt = 0: a HINT, executes as the shift by zero (RVC table).
            return f'opimm {c[:3]} {reg(a[0])} {reg(a[0])} 0'
        return f'!unknown-rvc {mn}'
    if mn in ('lui', 'auipc'):
        return f'{mn} {reg(a[0])} {h32(int(a[1], 0) << 12)}'
    if mn == 'jal':
        return f'jal {reg(a[0])} {h32(int(a[1], 0) - pc)}'
    if mn == 'jalr':
        off, rs1 = memop(a[1]); return f'jalr {reg(a[0])} {rs1} {h32(off)}'
    if mn in BR:
        return f'branch {BR[mn]} {reg(a[0])} {reg(a[1])} {h32(int(a[2], 0) - pc)}'
    if mn in LD:
        off, rs1 = memop(a[1]); w, s = LD[mn]
        return f'load {w} {s} {reg(a[0])} {rs1} {h32(off)}'
    if mn in ST:
        off, rs1 = memop(a[1]); return f'store {ST[mn]} {rs1} {reg(a[0])} {h32(off)}'
    if mn in ALU_I:
        return f'opimm {ALU_I[mn]} {reg(a[0])} {reg(a[1])} {h32(int(a[2], 0))}'
    if mn in ALU_R:
        return f'op {mn} {reg(a[0])} {reg(a[1])} {reg(a[2])}'
    if mn in MUL:
        return f'muldiv {mn} {reg(a[0])} {reg(a[1])} {reg(a[2])}'
    if base == 'lr.w':
        return f'lr {reg(a[0])} {reg(a[1].strip("()"))}'
    if base == 'sc.w':
        return f'sc {reg(a[0])} {reg(a[2].strip("()"))} {reg(a[1])}'
    if base.startswith('amo') and base.endswith('.w') and base[3:-2] in AMO:
        return f'amo {base[3:-2]} {reg(a[0])} {reg(a[2].strip("()"))} {reg(a[1])}'
    if mn in ('fence', 'fence.tso', 'pause'):
        return 'fence'
    if mn == 'fence.i':
        return 'fencei'
    if mn in ('csrrw', 'csrrs', 'csrrc', 'csrrwi', 'csrrsi', 'csrrci'):
        addr = csrs.get(a[1], None)
        if addr is None:
            addr = int(a[1], 0)
        src = f'i{h32(int(a[2], 0))}' if mn.endswith('i') else f'r{reg(a[2])}'
        return f'csr r{mn[4]} {reg(a[0])} {src} {addr:x}'
    if mn in ('ecall', 'ebreak', 'mret', 'wfi'):
        return mn
    return f'!unknown {mn}'


LINE = re.compile(r'^\s*([0-9a-f]+):\s+([0-9a-f]+)\s+(\S+)\s*(\S*)')


def objdump(env, out, name, half, values):
    s = out / f'{name}.S'
    d = '.half' if half else '.word'
    s.write_text('.text\n' + ''.join(f'{d} 0x{v:x}\n' for v in values))
    o = out / f'{name}.o'
    subprocess.run(['riscv64-linux-gnu-as', f'-march={ARCH}', '-mabi=ilp32', str(s), '-o', str(o)],
                   check=True, env=env)
    # Without the $d mapping symbols objdump disassembles the data.
    subprocess.run(['riscv64-linux-gnu-objcopy', '--strip-all', str(o)], check=True, env=env)
    p = subprocess.run(['riscv64-linux-gnu-objdump', '-d', '-M', 'no-aliases,numeric', str(o)],
                       check=True, env=env, capture_output=True, text=True)
    res = {}
    for line in p.stdout.splitlines():
        m = LINE.match(line)
        if m:
            res[int(m[1], 16)] = (int(m[2], 16), m[3], m[4])
    step = 2 if half else 4
    got = []
    for i, v in enumerate(values):
        e = res.get(i * step)
        if e is None or e[0] != v:
            raise SystemExit(f'objdump misaligned at {name}[{i}] {v:#x}: {e}')
        got.append((i * step, e[1], e[2]))
    return got


def model(out, items):
    f = out / 'model-in.txt'
    f.write_text(''.join(f'{n} {v:x}\n' for n, v in items))
    exe = HERE / '.lake/build/bin/decodesweep'
    subprocess.run(['lake', 'build', 'decodesweep'], cwd=HERE, check=True, stdout=subprocess.DEVNULL)
    subprocess.run([str(exe), str(f), str(out / 'model-out.txt')], check=True)
    return (out / 'model-out.txt').read_text().splitlines()


MUTANTS = [
    ('c.addi4spn nzuimm=0 accepted',
     'if n = 0 then none else some (.opimm .add (creg h 2) 2', 'some (.opimm .add (creg h 2) 2'),
    ('load funct3=6 accepted (lwu, RV64 only)',
     '| 5 => some (.load .h false rd rs1 (immI w))',
     '| 5 => some (.load .h false rd rs1 (immI w))\n    | 6 => some (.load .w false rd rs1 (immI w))'),
    ('srai accepts any funct7 >= 0x20', 'else if f7 = 0x20 then some (.opimm .sra', 'else if f7 ≥ 0x20 then some (.opimm .sra'),
    ('jal immediate bit 11 misplaced', 'bits w 20 1 * 2048', 'bits w 20 1 * 1024'),
    ('c.srli with shamt[5]=1 accepted', '| 0 => if bits h 12 1 = 0 then some (.opimm .srl r r sh) else none',
     '| 0 => some (.opimm .srl r r sh)'),
]


def controls(a):
    import shutil
    import tempfile
    rv32 = HERE.parent
    scratch = Path(tempfile.mkdtemp(prefix='decode-mutant-', dir='/dev/shm' if Path('/dev/shm').is_dir() else None))
    failures = []
    try:
        skip = {'firmware', 'build'}
        shutil.copytree(rv32, scratch / 'rv32', symlinks=True,
                        ignore=lambda d, names: [n for n in names if Path(d) == rv32 and n in skip])
        hart = scratch / 'rv32/Theories/Hart.lean'
        orig = hart.read_text()
        for name, old, new in MUTANTS:
            if orig.count(old) != 1:
                print(f'FAIL {name}: mutation site not found exactly once (TOOL)')
                failures.append(name)
                continue
            hart.write_text(orig.replace(old, new))
            p = subprocess.run([sys.executable, str(scratch / 'rv32/review/decode_sweep.py'),
                                '--samples', str(a.samples), '--seed', str(a.seed),
                                '--out', str(scratch / 'out')], capture_output=True, text=True)
            wrong = [l for l in p.stdout.splitlines() if 'WRONG' in l and not l.startswith(' ')]
            ok = p.returncode == 1 and wrong
            print(f'{"ok  " if ok else "FAIL"} {name}: exit {p.returncode} {"; ".join(wrong) or p.stderr.strip()[-200:]}')
            if not ok:
                failures.append(name)
            hart.write_text(orig)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    if failures:
        sys.exit(f'{len(failures)} decoder control(s) failed: {failures}')
    print('every decoder mutant was caught')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--samples', type=int, default=1_000_000)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--out', default=os.environ.get('E5R_SCRATCH', '/dev/shm') + '/decode-sweep')
    ap.add_argument('--summary')
    ap.add_argument('--controls', action='store_true')
    a = ap.parse_args()
    if a.controls:
        return controls(a)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    env = tools_env()
    rnd = random.Random(a.seed)

    halves = [v for v in range(1 << 16) if v & 3 != 3]
    words = []
    for f12 in range(1 << 12):
        words.append((f12 << 20) | 0x73)                 # SYSTEM, every funct12
    for f5 in range(32):
        for f3 in range(8):
            words.append((f5 << 27) | (rnd.getrandbits(2) << 25) | (rnd.getrandbits(10) << 15)
                         | (f3 << 12) | (rnd.getrandbits(5) << 7) | 0x2f)
    for i in range(a.samples):
        hi = rnd.getrandbits(25) << 7
        op = rnd.choice(IN_SCOPE) if i % 2 == 0 else (rnd.getrandbits(5) << 2) | 3
        if op & 0x1c == 0x1c:
            # bits[4:2] = 111 announce a 48-bit or longer encoding; there is
            # none in the ISA and the model's 4-byte fetch decodes them as
            # none. objdump would consume the next word too, so skip.
            op = 0x7f & ~0x10
        words.append(hi | op)
    # CSR names objdump prints -> numbers: disassemble csrrs x0,<n>,x0.
    csr_lines = objdump(env, out, 'csrs', False, [(n << 20) | 0x2073 for n in range(4096)])
    # (0xc0001073, csrrw x0,cycle,x0, prints as `unimp`.)
    csrs = {ops.split(',')[1]: n for n, (_, _, ops) in enumerate(csr_lines) if ops.count(',') == 2}

    dis16 = objdump(env, out, 'c16', True, halves)
    dis32 = objdump(env, out, 'w32', False, words)
    mod = model(out, [(16, v) for v in halves] + [(32, v) for v in words])

    counts = collections.Counter()
    examples = collections.defaultdict(list)
    for (pc, mn, ops), v, n, m in zip(dis16 + dis32, halves + words,
                                      [16] * len(halves) + [32] * len(words), mod):
        c = canon(pc, mn, ops, csrs)
        if c.startswith('!'):
            kind = {'!illegal': 'both-illegal', '!e31': 'e31-illegal'}.get(c.split()[0])
            if kind is None:
                kind = 'UNMAPPED'
            if m != 'none':
                kind = 'WRONG'
        elif m == 'none':
            kind = 'STRICT'
        elif m == c:
            kind = 'agree'
        else:
            kind = 'WRONG'
        if kind == 'WRONG' and c == '!illegal' and n == 32 and v & 0x7f == 0x0f and \
                ((v >> 12) & 7, m) in ((0, 'fence'), (1, 'fencei')):
            # Unprivileged spec 20240411, FENCE / Zifencei: reserved fm,
            # pred/succ, rs1, rd (and FENCE.I imm) "shall" be ignored and
            # the instruction executed as an ordinary fence. objdump rejects.
            kind = 'spec-fence'
        if kind == 'STRICT' and re.match(r'(c\.)?s(ll|rl|ra)i$', mn) and int(ops.split(',')[-1], 0) >= 32:
            # RV32: shamt[5] = 1 is reserved (custom for RVC); objdump
            # decodes it anyway. The model's none (trap) is the RV32 rule.
            kind = 'rv32-shamt5'
        if kind == 'STRICT' and mn == 'c.addi16sp' and int(ops.split(',')[-1], 0) == 0:
            kind = 'rvc-reserved'  # RVC table: nzimm = 0 is reserved
        counts[(n, kind)] += 1
        if kind in ('WRONG', 'STRICT', 'UNMAPPED') and len(examples[(n, kind)]) < 12:
            examples[(n, kind)].append(f'{v:0{n // 4}x}: objdump "{mn} {ops}" -> {c}; model {m}')
    for k in sorted(counts):
        print(f'{k[0]}-bit {k[1]:13} {counts[k]}')
    for k in sorted(examples):
        print(f'-- {k[0]}-bit {k[1]} examples:')
        for e in examples[k]:
            print('   ' + e)
    if a.summary:
        Path(a.summary).write_text(json.dumps({
            'arch': ARCH, 'seed': a.seed, 'samples': a.samples,
            'counts': {f'{n}-bit {k}': c for (n, k), c in sorted(counts.items())},
            'examples': {f'{n}-bit {k}': e for (n, k), e in sorted(examples.items())}}, indent=1))
    bad = sum(c for (n, k), c in counts.items() if k in ('WRONG', 'UNMAPPED'))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
