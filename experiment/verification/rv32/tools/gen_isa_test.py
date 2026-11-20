#!/usr/bin/env python3
"""Generate a deterministic RV32IMAC differential test program.

Every instruction class the model supports outside machine mode appears
with edge-case and random operands: base ALU and shifts, upper immediates,
all six branches both ways, jumps (including JALR's bit-0 clearing), every
load and store width, all of M (division by zero and overflow included),
every AMO, LR/SC, FENCE/FENCE.I and the RV32C forms compilers emit. The
program runs under `qemu-riscv32 -one-insn-per-tb -d cpu`; tools/ReplayIsa
then replays that trace in the Lean model and compares every register after
every instruction. Original e5r test code, Apache-2.0.
"""
import random
import sys

EDGE = [0, 1, 2, 0xffffffff, 0xfffffffe, 0x7fffffff, 0x80000000, 0x80000001,
        0x55555555, 0xaaaaaaaa, 0x0000ffff, 0xffff0000, 0x00000080, 0x000007ff, 0xfffff800]


def val(rng):
    return rng.choice(EDGE) if rng.random() < 0.6 else rng.getrandbits(32)


def li(reg, v):
    return f'  li {reg}, {v - (1 << 32) if v >= 1 << 31 else v}'


def generate(seed, count):
    rng = random.Random(seed)
    regs = ['a0', 'a1', 'a2', 'a3', 'a4', 'a5', 't1', 't2', 't3', 's1']
    creg = ['s0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5']
    out = ['.option norelax', '.section .text', '.global _start', '_start:',
           '  la t0, buf', '  addi sp, t0, 1024']
    label = [0]

    def fresh():
        label[0] += 1
        return f'L{label[0]}'

    rtype = ['add', 'sub', 'sll', 'slt', 'sltu', 'xor', 'srl', 'sra', 'or', 'and',
             'mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu']
    itype = ['addi', 'slti', 'sltiu', 'xori', 'ori', 'andi']
    shifts = ['slli', 'srli', 'srai']
    branches = ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu']
    amos = ['amoswap.w', 'amoadd.w', 'amoxor.w', 'amoand.w', 'amoor.w',
            'amomin.w', 'amomax.w', 'amominu.w', 'amomaxu.w']
    loads = [('lb', 1), ('lbu', 1), ('lh', 2), ('lhu', 2), ('lw', 4)]
    stores = [('sb', 1), ('sh', 2), ('sw', 4)]
    for _ in range(count):
        kind = rng.choice(['r', 'r', 'r', 'i', 'shift', 'upper', 'branch', 'jump',
                           'load', 'store', 'amo', 'lrsc', 'fence', 'c', 'c', 'c'])
        a, b, d = rng.sample(regs, 3)
        if kind == 'r':
            if rng.random() < 0.5:
                out += [li(a, val(rng)), li(b, val(rng))]
            out.append(f'  {rng.choice(rtype)} {d}, {a}, {b}')
        elif kind == 'i':
            out += [li(a, val(rng)), f'  {rng.choice(itype)} {d}, {a}, {rng.randint(-2048, 2047)}']
        elif kind == 'shift':
            out += [li(a, val(rng)), f'  {rng.choice(shifts)} {d}, {a}, {rng.randint(0, 31)}']
        elif kind == 'upper':
            op = rng.choice(['lui', 'auipc'])
            out.append(f'  {op} {d}, {rng.randint(0, 0xfffff)}')
        elif kind == 'branch':
            l = fresh()
            out += [li(a, val(rng)), li(b, rng.choice([val(rng), 0]))]
            out += [f'  {rng.choice(branches)} {a}, {b}, {l}', f'  addi {d}, {d}, 1', f'{l}:']
        elif kind == 'jump':
            l = fresh()
            if rng.random() < 0.5:
                out += [f'  jal {d}, {l}', '  addi t1, t1, 1', f'{l}:']
            else:
                # JALR clears bit 0 of the target: aim one byte past the label.
                out += [f'  la {a}, {l}', f'  jalr {d}, {rng.choice([0, 1])}({a})',
                        '  addi t1, t1, 1', f'{l}:']
        elif kind == 'load':
            op, n = rng.choice(loads)
            off = rng.randrange(0, 2040 // n) * n
            out.append(f'  {op} {d}, {off}(t0)')
        elif kind == 'store':
            op, n = rng.choice(stores)
            off = rng.randrange(0, 2040 // n) * n
            out += [li(a, val(rng)), f'  {op} {a}, {off}(t0)']
        elif kind == 'amo':
            off = rng.randrange(0, 510) * 4
            out += [li(a, val(rng)), f'  addi {b}, t0, {off}', f'  {rng.choice(amos)} {d}, {a}, ({b})']
        elif kind == 'lrsc':
            off = rng.randrange(0, 510) * 4
            out += [f'  addi {b}, t0, {off}', li(a, val(rng))]
            if rng.random() < 0.7:
                out.append(f'  lr.w {d}, ({b})')
            out.append(f'  sc.w {d}, {a}, ({b})')
        elif kind == 'fence':
            out.append(rng.choice(['  fence', '  fence.i', '  fence rw, w', '  fence r, rw']))
        else:
            x, y = rng.sample(creg, 2)
            c = rng.choice(['addi', 'li', 'lui', 'mv', 'add', 'sub', 'xor', 'or', 'and',
                            'srli', 'srai', 'andi', 'slli', 'lw', 'sw', 'lwsp', 'swsp',
                            'addi16sp', 'addi4spn', 'beqz', 'bnez', 'j', 'jal', 'jr', 'jalr',
                            'nop'])
            if c in ['addi', 'andi']:
                imm = rng.choice([v for v in range(-32, 32) if c == 'andi' or v != 0])
                out += [li(x, val(rng)), f'  c.{c} {x}, {imm}']
            elif c == 'li':
                out.append(f'  c.li {x}, {rng.randint(-32, 31)}')
            elif c == 'lui':
                out.append(f'  c.lui {x}, {rng.choice([1, 2, 31, 0xfffe0, 0xfffff])}')
            elif c in ['mv', 'add']:
                out += [li(y, val(rng)), f'  c.{c} {x}, {y}']
            elif c in ['sub', 'xor', 'or', 'and']:
                out += [li(x, val(rng)), li(y, val(rng)), f'  c.{c} {x}, {y}']
            elif c in ['srli', 'srai', 'slli']:
                out += [li(x, val(rng)), f'  c.{c} {x}, {rng.randint(1, 31)}']
            elif c in ['lw', 'sw']:
                if c == 'sw':
                    out.append(li(y, val(rng)))
                out += ['  mv s0, t0', f'  c.{c} {y if c == "sw" else x}, {rng.randrange(0, 32) * 4}(s0)']
            elif c == 'lwsp':
                out.append(f'  c.lwsp {x}, {rng.randrange(0, 64) * 4}(sp)')
            elif c == 'swsp':
                out += [li(x, val(rng)), f'  c.swsp {x}, {rng.randrange(0, 64) * 4}(sp)']
            elif c == 'addi16sp':
                imm = rng.choice([-496, -16, 16, 496])
                out += [f'  c.addi16sp sp, {imm}', f'  c.addi16sp sp, {-imm}']
            elif c == 'addi4spn':
                out.append(f'  c.addi4spn {x}, sp, {rng.randrange(1, 255) * 4}')
            elif c in ['beqz', 'bnez']:
                l = fresh()
                out += [li(x, rng.choice([0, val(rng)])), f'  c.{c} {x}, {l}', '  addi t1, t1, 1', f'{l}:']
            elif c in ['j', 'jal']:
                l = fresh()
                out += [f'  c.{c} {l}', '  addi t1, t1, 1', f'{l}:']
            elif c in ['jr', 'jalr']:
                l = fresh()
                out += [f'  la {x}, {l}', f'  c.{c} {x}', '  addi t1, t1, 1', f'{l}:']
            else:
                out.append('  c.nop')
    out += ['  li a0, 0', '  li a7, 93', '  ecall',
            '.section .bss', '.balign 64', 'buf:', '  .space 4096']
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    seed, count, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    with open(path, 'w') as f:
        f.write(generate(seed, count))
