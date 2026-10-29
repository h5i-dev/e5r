#!/usr/bin/env python3
"""Bare-metal instruction-level differential harness: QEMU sifive_e vs the Lean model.

Original review code, Apache-2.0. Independent of tools/oracle.py,
tools/qemu_trace.py and tools/Replay.lean: it does not parse QEMU's `-d cpu`
log. The firmware it builds runs on `qemu-system-riscv32 -M sifive_e,revb=true`
in M-mode, sets up every GPR, the modeled CSRs, CLINT msip/mtimecmp and a
64-byte RAM window from a descriptor, runs one candidate instruction (or a
short straight-line sequence), and saves the full post-state from the
firmware itself:

* normal completion: a landing pad saves x1..x31 through a base register the
  candidate does not name, then the CSRs; the pad that was reached (fall-
  through or taken) gives the post PC;
* trap or interrupt: a handler entered through mtvec saves x1..x31 via an
  mscratch swap, then mcause/mepc/mstatus and the entry address reached.

Each case is printed on UART0 as one line; the Lean side (review/Diff.lean)
rebuilds the pre-state from the dump, runs `stepInstr`/`takeIrq` and compares.
Passing is differential testing of selected behavior, not a proof.
"""
import argparse
import dataclasses
import json
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
RV32 = HERE.parent
REPO = RV32.parents[1]

RECORD = 0x80001000
WINDOW = RECORD + 192
CUR_DESC = 0x80000000
LRKILL = 0x80000040
DESC_WORDS = 64
REC_WORDS = 64
# Default pre-state: distinct, sign-bit-mixed values so that a write to the
# wrong register or a lost write shows up in the comparison.
REGDEF = {i: (0x9e3779b9 * i + 0x01234567) & 0xffffffff for i in range(1, 32)}
WINDEF = [(0xf0e1d2c3 + 0x1b2c3d4e * k) & 0xffffffff for k in range(16)]
MSTATUS_DEF = 0x1800  # MPP = M, MIE = MPIE = 0
# Bytes from the end of the candidate to a forward taken pad with K = 0: the
# fall-through pad (sw + j) and the save block (31 sw, la, jr).
SAVE_BYTES = 31 * 4 + 12
FT_TO_TK = 8 + SAVE_BYTES


def fwd(length, k=0):
    """Offset from a candidate of `length` bytes to its forward pad `('fwd', k)`."""
    return length + FT_TO_TK + k


def bk(k=0):
    """Offset to the backward pad `('bk', k)`."""
    return -(8 + k)


CSR_SLOTS = ['mstatus', 'mie', 'mtvec', 'mepc', 'mcause', 'mscratch', 'msip',
             'mtimecmp_lo', 'mtimecmp_hi']


@dataclasses.dataclass
class Case:
    name: str
    family: str
    insns: list                      # ints (encodings) or asm strings ({n} = case index)
    regs: dict = dataclasses.field(default_factory=dict)
    csr: dict = dataclasses.field(default_factory=dict)
    win: list = None
    expect: str = 'ok'               # 'ok' | 'trap:<cause>' | 'irq:<code>'
    model: str = 'agree'             # 'agree' | 'decline' | 'oracle-divergence'
    tk: tuple = None                 # None | ('fwd', K) | ('bk', K)
    rb: int = None
    uses: set = None
    note: str = ''


def insn_len(x):
    return 2 if isinstance(x, int) and x & 3 != 3 else 4


def fields(x):
    """Every register an encoding could name, conservatively."""
    if not isinstance(x, int):
        return set()
    if x & 3 == 3:
        return {x >> 7 & 31, x >> 15 & 31, x >> 20 & 31}
    return {x >> 7 & 31, x >> 2 & 31, 8 + (x >> 7 & 7), 8 + (x >> 2 & 7), 1, 2}


def choose_rb(c):
    used = set(c.uses or ()) | set(c.regs)
    for x in c.insns:
        used |= fields(x)
    if c.rb is not None:
        assert c.rb not in used, (c.name, c.rb)
        return c.rb
    for r in [27, 26, 25, 24, 23, 22, 21, 20, 19, 18]:
        if r not in used:
            return r
    raise ValueError(f'{c.name}: no free base register')


def emit(cases):
    a = ['.option norvc', '.option norelax', '.section .text', '.global _start', '_start:',
         'la t0, handler', 'csrw mtvec, t0', f'li t0, {RECORD}', 'csrw mscratch, t0',
         'j case_0']
    for n, c in enumerate(cases):
        rb = c._rb
        a += ['.balign 4', f'case_{n}:', f'la a0, desc_{n}', 'call setup', f'la x31, desc_{n}']
        a += [f'lw x{i}, {4 * (i - 1)}(x31)' for i in range(1, 32)]
        a += [f'j cand_{n}']
        if c.tk and c.tk[0] == 'bk':
            a += [f'tk_{n}:', f'sw x{rb}, 152(x{rb})', f'j save_{n}'] + ([f'.skip {c.tk[1]}'] if c.tk[1] else [])
        a += [f'cand_{n}:']
        for x in c.insns:
            if isinstance(x, int):
                a += [f'.half {x:#x}'] if insn_len(x) == 2 else [f'.word {x:#x}']
            else:
                a += [x.format(n=n)]
        a += [f'ft_{n}:', 'sw x0, 152(x%d)' % rb, f'j save_{n}', f'save_{n}:']
        a += [f'sw x{i}, {4 * i}(x{rb})' for i in range(1, 32)]
        a += ['la t0, save_common', 'jr t0']
        if c.tk and c.tk[0] == 'fwd':
            a += ([f'.skip {c.tk[1]}'] if c.tk[1] else []) + [f'tk_{n}:', f'sw x{rb}, 152(x{rb})', f'j save_{n}']
    a += ['.balign 4', f'case_{len(cases)}:', 'li a0, 68', 'call putc', 'li a0, 10', 'call putc',
          '1: j 1b']
    a += ['.balign 4', 'save_common:', f'li t0, {RECORD}']
    for off, name in [(128, 'mstatus'), (132, 'mie'), (136, 'mtvec'), (140, 'mepc'),
                      (144, 'mcause'), (148, 'mscratch'), (156, 'mtval'), (160, 'mip')]:
        a += [f'csrr t1, {name}', f'sw t1, {off}(t0)']
    a += ['li t2, 0x2000000', 'lw t1, 0(t2)', 'sw t1, 164(t0)', 'li t1, 1', 'sw t1, 0(t0)',
          'j finish']
    # Trap entry: direct handler and a 16-entry vector table.
    a += ['.balign 64', 'handler:', 'csrrw t6, mscratch, t6', 'sw t5, 120(t6)', 'la t5, handler',
          'sw t5, 152(t6)', 'j trap_common', '.balign 64', 'vtable:']
    a += [f'j vh_{k}' for k in range(16)]
    for k in range(16):
        a += [f'vh_{k}:', 'csrrw t6, mscratch, t6', 'sw t5, 120(t6)', f'la t5, vtable + {4 * k}',
              'sw t5, 152(t6)', 'j trap_common']
    a += ['trap_common:'] + [f'sw x{i}, {4 * i}(t6)' for i in range(1, 30)]
    a += ['csrr t5, mscratch', 'sw t5, 124(t6)']
    for off, name in [(128, 'mstatus'), (132, 'mie'), (136, 'mtvec'), (140, 'mepc'),
                      (144, 'mcause'), (156, 'mtval'), (160, 'mip')]:
        a += [f'csrr t5, {name}', f'sw t5, {off}(t6)']
    a += ['sw t6, 148(t6)', 'li t4, 0x2000000', 'lw t5, 0(t4)', 'sw t5, 164(t6)',
          'li t5, 2', 'sw t5, 0(t6)', 'j finish']
    a += ['finish:', 'li t0, 0x1800', 'csrw mstatus, t0', 'csrw mie, zero',
          'li t0, 0x2000000', 'sw zero, 0(t0)', 'li t0, 0x2004000', 'li t1, -1',
          'sw t1, 4(t0)', 'sw t1, 0(t0)', 'la t0, handler', 'csrw mtvec, t0',
          f'li t0, {RECORD}', 'csrw mscratch, t0',
          'li a0, 82', 'call putc', f'li t0, {CUR_DESC}', 'lw s0, 0(t0)',
          'mv a1, s0', f'li a2, {DESC_WORDS}', 'li a4, 0', 'call putwords',
          'lw a1, 164(s0)', 'li a2, 16', 'li a4, 1', 'call putwords',
          f'li a1, {RECORD}', f'li a2, {REC_WORDS}', 'li a4, 0', 'call putwords',
          'li a0, 10', 'call putc', 'lw t0, 172(s0)', 'jr t0']
    a += ['putc:', 'li t6, 0x10013000', 'sw a0, 0(t6)', 'ret']
    # putwords(a1 = address, a2 = count, a4 = 1 to assemble from halfwords).
    a += ['putwords:', 'mv s1, ra',
          '1:', 'beqz a4, 2f', 'lhu a3, 0(a1)', 'lhu a5, 2(a1)', 'slli a5, a5, 16',
          'or a3, a3, a5', 'j 3f', '2:', 'lw a3, 0(a1)', '3:',
          'li a0, 32', 'call putc', 'li a5, 28',
          '4:', 'srl a0, a3, a5', 'andi a0, a0, 15', 'li t5, 10', 'blt a0, t5, 5f',
          'addi a0, a0, 39', '5:', 'addi a0, a0, 48', 'call putc', 'addi a5, a5, -4',
          'bgez a5, 4b', 'addi a1, a1, 4', 'addi a2, a2, -1', 'bnez a2, 1b',
          'mv ra, s1', 'ret']
    a += ['setup:', f'li t0, {CUR_DESC}', 'sw a0, 0(t0)', 'li t0, 0x1800', 'csrw mstatus, t0',
          'csrw mie, zero', f'li t1, {RECORD}', 'li t2, 48', 'mv t3, t1',
          '1:', 'sw zero, 0(t3)', 'addi t3, t3, 4', 'addi t2, t2, -1', 'bnez t2, 1b',
          'addi t3, a0, 192', 'addi t4, t1, 192', 'li t2, 16',
          '2:', 'lw t5, 0(t3)', 'sw t5, 0(t4)', 'addi t3, t3, 4', 'addi t4, t4, 4',
          'addi t2, t2, -1', 'bnez t2, 2b',
          f'li t3, {LRKILL}', 'sc.w zero, zero, (t3)',
          'li t3, 0x2004000', 'li t4, -1', 'sw t4, 4(t3)', 'lw t5, 152(a0)', 'sw t5, 0(t3)',
          'lw t5, 156(a0)', 'sw t5, 4(t3)', 'li t3, 0x2000000', 'lw t5, 148(a0)', 'sw t5, 0(t3)']
    for off, name in [(132, 'mtvec'), (136, 'mepc'), (140, 'mcause'), (144, 'mscratch'),
                      (128, 'mie')]:
        a += [f'lw t5, {off}(a0)', f'csrw {name}, t5']
    for off, name in [(172, 'mie'), (176, 'mtvec'), (180, 'mepc'), (184, 'mcause'),
                      (188, 'mscratch')]:
        a += [f'csrr t5, {name}', f'sw t5, {off}(t1)']
    a += ['lw t5, 124(a0)', 'csrw mstatus, t5', 'csrr t6, mstatus', 'sw t6, 168(t1)', 'ret']
    a += ['.section .rodata', '.balign 4']
    for n, c in enumerate(cases):
        d = c._desc
        a += [f'desc_{n}:'] + [f'.word {v}' for v in d]
    return '\n'.join(a) + '\n'


def describe(cases):
    for n, c in enumerate(cases):
        c._rb = choose_rb(c)
        regs = dict(REGDEF)
        regs.update(c.regs)
        regs[c._rb] = RECORD
        cs = {'mstatus': MSTATUS_DEF, 'mie': 0, 'mtvec': 'handler', 'mepc': 0x20000100,
              'mcause': 0, 'mscratch': RECORD, 'msip': 0, 'mtimecmp_lo': 0xffffffff,
              'mtimecmp_hi': 0xffffffff}
        cs.update(c.csr)
        win = c.win if c.win is not None else WINDEF
        assert len(win) == 16
        d = [regs[i] for i in range(1, 32)] + [cs[k] for k in CSR_SLOTS]
        d += [len(c.insns), f'cand_{n}', n, f'case_{n + 1}', f'ft_{n}',
              f'tk_{n}' if c.tk else 1, c._rb, 0] + list(win)
        assert len(d) == DESC_WORDS
        c._desc = [(f'{v}' if isinstance(v, int) else v).format(n=n) for v in d]
        c._intended = d


def tools_env():
    env = dict(os.environ)
    bins = os.environ.get('E5R_BINUTILS_ROOT',
                          str(Path.home() / '.local/state/e5r-lean-agent-20261028/tools/root'))
    qemu = os.environ.get('E5R_QEMU_ROOT',
                          str(Path.home() / '.local/state/e5r-claude-production-20261029T024659Z/tools/root'))
    env['PATH'] = f'{bins}/usr/bin:{qemu}/usr/bin:' + env.get('PATH', '')
    libs = [f'{bins}/usr/lib/x86_64-linux-gnu', f'{qemu}/usr/lib/x86_64-linux-gnu',
            f'{qemu}/lib/x86_64-linux-gnu']
    env['LD_LIBRARY_PATH'] = ':'.join(libs + [env.get('LD_LIBRARY_PATH', '')]).rstrip(':')
    return env


def build(cases, out):
    out.mkdir(parents=True, exist_ok=True)
    describe(cases)
    (out / 'cases.S').write_text(emit(cases))
    env = tools_env()
    subprocess.run(['riscv64-linux-gnu-as', '-march=rv32imac_zicsr_zifencei', '-mabi=ilp32',
                    str(out / 'cases.S'), '-o', str(out / 'cases.o')], check=True, env=env)
    subprocess.run(['riscv64-linux-gnu-ld', '-m', 'elf32lriscv', '--no-relax',
                    '-Ttext=0x20010000', '-Tdata=0x80002000', '-e', '_start',
                    str(out / 'cases.o'), '-o', str(out / 'cases.elf')], check=True, env=env)
    return env


def run_qemu(out, env, ncases, timeout):
    log = out / 'uart.txt'
    with open(log, 'wb') as f:
        p = subprocess.Popen(['qemu-system-riscv32', '-M', 'sifive_e,revb=true', '-nographic',
                              '-bios', 'none', '-kernel', str(out / 'cases.elf'),
                              '-accel', 'tcg,one-insn-per-tb=on', '-monitor', 'none',
                              '-serial', 'stdio'], stdout=f, stderr=subprocess.STDOUT, env=env)
        t0 = time.time()
        while time.time() - t0 < timeout:
            time.sleep(0.2)
            if log.stat().st_size and log.read_bytes().rstrip().endswith(b'\nD'):
                break
            if p.poll() is not None:
                break
        p.kill()
        p.wait()
    lines = [ln for ln in log.read_text(errors='replace').splitlines() if ln.startswith('R ')]
    done = log.read_text(errors='replace').rstrip().endswith('D')
    return lines, done


def resolve_symbols(out, env):
    nm = subprocess.check_output(['riscv64-linux-gnu-nm', str(out / 'cases.elf')], env=env, text=True)
    syms = {}
    for ln in nm.splitlines():
        parts = ln.split()
        if len(parts) == 3:
            syms[parts[2]] = int(parts[0], 16)
    return syms


def intended_value(v, n, syms):
    if isinstance(v, int):
        return v & 0xffffffff
    expr = v.format(n=n)
    # Expressions are `sym` or `sym + k` / `sym - k`.
    for op in ['+', '-']:
        if f' {op} ' in expr:
            s, k = expr.split(f' {op} ')
            return (syms[s] + (int(k, 0) if op == '+' else -int(k, 0))) & 0xffffffff
    return syms[expr]


def setup_checks(cases, lines, syms):
    """Oracle-setup validation: QEMU really ran with the intended pre-state."""
    problems = []
    for ln in lines:
        w = [int(x, 16) for x in ln.split()[1:]]
        desc, code, rec = w[:64], w[64:80], w[80:]
        n = desc[42]
        c = cases[n]
        want = [intended_value(v, n, syms) for v in c._intended]
        if desc != want:
            problems.append(f'{c.name}: descriptor dump differs from intent')
        rb = dict(zip(['mie', 'mtvec', 'mepc', 'mcause', 'mscratch'], rec[43:48]))
        rb['mstatus'] = rec[42]
        for k, got in rb.items():
            if got != want[31 + CSR_SLOTS.index(k)]:
                problems.append(f'{c.name}: QEMU legalized pre {k} {want[31 + CSR_SLOTS.index(k)]:#x} -> {got:#x}')
        # The bytes QEMU fetched are the encodings the generator meant.
        raw = b''.join(x.to_bytes(4, 'little') for x in code)
        off = 0
        for x in c.insns:
            ln_ = insn_len(x)
            if isinstance(x, int):
                got = int.from_bytes(raw[off:off + ln_], 'little')
                if got != x:
                    problems.append(f'{c.name}: candidate bytes {got:#x} != {x:#x}')
            off += ln_ if isinstance(x, int) else 4
    return problems


def expect_check(c, rec):
    st, cause = rec[0], rec[36]
    if c.expect == 'ok':
        return st == 1
    kind, v = c.expect.split(':')
    if kind == 'trap':
        return st == 2 and cause == int(v, 0)
    if kind == 'irq':
        return st == 2 and cause == (1 << 31 | int(v, 0))
    raise ValueError(c.expect)


def evaluate(cases, out, lean_root=None):
    """Run the Lean side over `out/qemu.txt` and classify each verdict."""
    verdict_file = out / 'verdicts.txt'
    if verdict_file.exists():
        verdict_file.unlink()
    cmd = ['lake', 'env', 'lean', '--run', str(HERE / 'Diff.lean'), str(out / 'qemu.txt'),
           str(verdict_file)]
    r = subprocess.run(cmd, cwd=str(lean_root or RV32), capture_output=True, text=True, timeout=1800)
    if r.returncode != 0 or not verdict_file.exists():
        return 3, {}, [], [], (r.stdout[-4000:] + r.stderr[-4000:])
    verdicts = {}
    for ln in verdict_file.read_text().splitlines():
        k, _, rest = ln.partition(' ')
        verdicts[int(k)] = rest
    stats, unexpected, rows = {}, [], []
    for n, c in enumerate(cases):
        v = verdicts.get(n, 'MISSING')
        kind = v.split()[0]
        stats.setdefault(c.family, {}).setdefault(kind, 0)
        stats[c.family][kind] += 1
        want = {'agree': ('AGREE', 'AGREE-TRAP', 'AGREE-IRQ'), 'decline': ('DECLINE',),
                'oracle-divergence': ('MISMATCH',)}[c.model]
        if kind not in want:
            unexpected.append(f'{c.name}: {v} (expected model {c.model}) {c.note}')
        rows.append({'name': c.name, 'family': c.family, 'expect': c.expect, 'model': c.model,
                     'verdict': v})
    return (1 if unexpected else 0), stats, unexpected, rows, ''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default='/dev/shm/e5r-isa-review-20261029T042314Z/diff')
    ap.add_argument('--filter', default='')
    ap.add_argument('--timeout', type=float, default=300)
    ap.add_argument('--no-lean', action='store_true')
    ap.add_argument('--summary', default='')
    args = ap.parse_args()
    sys.path.insert(0, str(HERE))
    import cases as catalog
    cases = [c for c in catalog.all_cases() if args.filter in c.name or args.filter in c.family]
    out = Path(args.out)
    env = build(cases, out)
    syms = resolve_symbols(out, env)
    lines, done = run_qemu(out, env, len(cases), args.timeout)
    print(f'{len(cases)} cases, {len(lines)} QEMU records, run complete: {done}')
    if len(lines) != len(cases) or not done:
        print('QEMU did not report every case; refusing to compare a partial run')
        return 2
    probs = setup_checks(cases, lines, syms)
    bad_expect = []
    for ln in lines:
        w = [int(x, 16) for x in ln.split()[1:]]
        c = cases[w[42]]
        if not expect_check(c, w[80:]):
            bad_expect.append(f'{c.name}: QEMU status {w[80]} mcause {w[80 + 36]:#x}, expected {c.expect}')
    (out / 'qemu.txt').write_text('\n'.join(lines) + '\n')
    for p in probs + bad_expect:
        print('SETUP', p)
    if args.no_lean:
        return 1 if probs or bad_expect else 0
    rc, stats, unexpected, rows, err = evaluate(cases, out)
    if rc == 3:
        print('Lean comparison did not run to completion (this is a tool failure, not a verdict):')
        print(err)
        return 3
    for fam in sorted(stats):
        print(f'{fam:12s} ' + ' '.join(f'{k}={v}' for k, v in sorted(stats[fam].items())))
    for u in unexpected:
        print('UNEXPECTED', u)
    if args.summary:
        Path(args.summary).write_text(json.dumps(
            {'cases': len(cases), 'stats': stats, 'unexpected': unexpected,
             'setup_problems': probs, 'expect_problems': bad_expect, 'rows': rows}, indent=1) + '\n')
    return 1 if unexpected or probs or bad_expect else 0


if __name__ == '__main__':
    sys.exit(main())
