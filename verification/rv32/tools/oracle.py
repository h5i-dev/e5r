#!/usr/bin/env python3
"""QEMU user-mode differential tests. Linux observation wrapper is outside the model.
Original test code, Apache-2.0. No QEMU or other emulator implementation used.
"""
import os
from pathlib import Path
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[3]
BUILD = ROOT / 'fixtures/build/lean-rv32'
CROSS = os.environ.get('CROSS_COMPILE', 'riscv64-linux-gnu-')
QEMU = os.environ.get('QEMU_RISCV32', 'qemu-riscv32')


def run(args):
    return subprocess.check_output([str(a) for a in args])


def r(f7, f3, rd=10):
    return f7 << 25 | 12 << 20 | 11 << 15 | f3 << 12 | rd << 7 | 0x33


def i(imm, f3=0, op=0x13, rd=10):
    return (imm & 4095) << 20 | 11 << 15 | f3 << 12 | rd << 7 | op


def b(f3, offset=12):
    return ((offset >> 12 & 1) << 31 | (offset >> 5 & 63) << 25 |
            12 << 20 | 11 << 15 | f3 << 12 | (offset >> 1 & 15) << 8 |
            (offset >> 11 & 1) << 7 | 0x63)


def generate():
    # (word, a1, a2, observation), edge values include wrap and signed boundaries.
    cases = []
    for a, bb in [(0, 0), (0xffffffff, 1), (0x7fffffff, 1),
                  (0x80000000, 0xffffffff), (1, 0xffffffff)]:
        for f7 in [0, 32]:
            cases.append((r(f7, 0), a, bb, 'reg'))
    for a in [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]:
        for imm in [-2048, -1, 0, 1, 2047]:
            cases.append((i(imm), a, 0, 'reg'))
    cases += [(i(7, rd=0), 123, 0, 'zero'), (0xfffff537, 0, 0, 'reg')]
    cases += [(upper << 12 | 10 << 7 | 0x17, 0, 0, 'reg') for upper in [0, 0x80000, 0xfffff]]
    for f3 in [0, 1, 4, 5, 6, 7]:
        for a, bb in [(0, 0), (1, 0), (0, 1), (0x80000000, 0x7fffffff),
                      (0xffffffff, 0), (0x7fffffff, 0xffffffff)]:
            cases.append((b(f3), a, bb, 'branch'))
        cases.append((b(f3, -12), 0xffffffff, 0, 'backbranch'))
    cases += [(i(0, 2, 3), 8192, 0, 'reg'), (i(-4, 2, 3), 8196, 0, 'reg')]
    for v in [0, 0xffffffff, 0x80000000, 0x12345678]:
        cases.append((12 << 20 | 11 << 15 | 2 << 12 | 4 << 7 | 0x23,
                      8192, v, 'mem'))
    for v in [0, 0xffffffff, 0x80000000, 0x12345678]:
        cases.append((127 << 25 | 12 << 20 | 11 << 15 | 2 << 12 | 28 << 7 | 0x23,
                      8200, v, 'mem'))
    cases += [(0x00c0056f, 0, 0, 'reg'), (i(0, 0, 0x67), 0, 0, 'jalr')]
    asm = ['.option norvc', '.option norelax', '.section .text', '.global _start', '_start:']
    for n, (w, a, bb, mode) in enumerate(cases):
        asm += ['lui t0,2', 'li t1,0x80000001', 'sw t1,0(t0)', 'sw zero,4(t0)',
                f'li a1,{a}', f'li a2,{bb}', 'li a0,0x12345678']
        if mode == 'jalr':
            asm += [f'lui a1,%hi(taken{n})', f'addi a1,a1,%lo(taken{n})+1']
        if mode == 'backbranch':
            asm += [f'jal zero,candidate{n}', 'addi a0,zero,22', f'jal zero,finish{n}', 'nop']
        asm += [f'candidate{n}:', f'.word {w}', 'addi a0,zero,11', f'jal zero,finish{n}',
                f'taken{n}:']
        if mode == 'branch':
            asm += ['addi a0,zero,22']
        asm += [f'finish{n}:']
        # Arithmetic/load/store instructions must skip the branch-observation code.
        # Patch it to nops below so a0 retains the candidate's result.
        if mode == 'mem':
            asm += ['lw a0,4(t0)']
        if mode == 'zero':
            asm += ['addi a0,zero,0']
        asm += [f'sw a0,{256+4*n}(t0)']
    asm += ['li a0,1', 'li a1,0x2100', f'li a2,{4*len(cases)}', 'li a7,64',
            'ecall', 'li a0,0', 'li a7,93', 'ecall', '.section .data',
            '.word 0,0', '.space 248', f'.space {4*len(cases)}']
    # Only branches should replace a0 with a path marker.
    for n, (_, _, _, mode) in enumerate(cases):
        if mode not in ['branch', 'backbranch']:
            pos = asm.index(f'candidate{n}:')
            asm[pos+2] = 'addi zero,zero,0'
    source = BUILD / 'oracle.S'
    source.write_text('\n'.join(asm)+'\n')
    run([CROSS+'as', '-march=rv32i', '-mabi=ilp32', '-o', BUILD/'oracle.o', source])
    link = BUILD / 'oracle.ld'
    link.write_text((ROOT/'verification/rv32/Projects/clamp/link.ld').read_text().replace('0x1000', '0x10000'))
    run([CROSS+'ld', '-m', 'elf32lriscv', '--no-relax', '-T',
         link, '-o', BUILD/'oracle.elf', BUILD/'oracle.o'])
    symbols = {}
    for line in run([CROSS+'nm', BUILD/'oracle.elf']).decode().splitlines():
        parts = line.split()
        if len(parts) == 3:
            symbols[parts[2]] = int(parts[0], 16)
    raw = run([QEMU, BUILD/'oracle.elf'])
    if len(raw) != 4*len(cases):
        raise RuntimeError(f'QEMU returned {len(raw)} bytes, expected {4*len(cases)}')
    values = struct.unpack('<'+'I'*len(cases), raw)
    lean = ['import Theories.RV32', 'open RV32', 'set_option maxRecDepth 100000',
            'set_option maxHeartbeats 0', 'namespace Oracle',
            'def check (pc w a b expected mode : Nat) : Bool :=',
            '  let code : Region := ⟨pc, [w%256,w/256%256,w/65536%256,w/16777216%256], true, false, true⟩',
            '  let data : Region := ⟨8192, [1,0,0,128,0,0,0,0], true, true, false⟩',
            '  let s := put (put ({pc := pc, mem := [code,data]} : State) 11 a) 12 b',
            '  match step s with',
            '  | .error _ => false',
            '  | .ok t => if mode = 1 then t.pc == expected',
            '             else if mode = 2 then decide (readWord t.mem 8196 = .ok expected)',
            '             else if mode = 3 then reg t 0 == expected',
            '             else if mode = 4 then reg t 10 == expected && t.pc == b',
            '             else reg t 10 == expected']
    for n, ((w, a, bb, mode), val) in enumerate(zip(cases, values)):
        pc = symbols[f'candidate{n}']
        if mode in ['branch', 'backbranch']:
            if val not in [11, 22]:
                raise RuntimeError(f'bad QEMU branch observation {val}')
            val = pc+((12 if mode == 'branch' else -12) if val == 22 else 4)
        if mode == 'jalr':
            a = symbols[f'taken{n}']+1
        tag = {'branch': 1, 'backbranch': 1, 'mem': 2, 'zero': 3}.get(mode, 0)
        if mode == 'jalr' or w & 0x7f == 0x6f:
            # Link observation comes from QEMU; target address independently
            # comes from the assembled wrapper's symbol table.
            bb = symbols[f'taken{n}']
            tag = 4
        lean += [f'theorem case{n} : check {pc} {w} {a} {bb} {val} {tag} = true := by decide +kernel',
                 f'#print axioms case{n}']
    lean += ['end Oracle']
    (ROOT/'verification/rv32/Oracle.lean').write_text('\n'.join(lean)+'\n')
    print(f'QEMU supplied {len(cases)} instruction observations; generated Oracle.lean')


if __name__ == '__main__':
    generate()
