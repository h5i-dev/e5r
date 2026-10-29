#!/usr/bin/env python3
"""Compact a QEMU `-d cpu,int` single-instruction trace for Lean replay.

Each output line is one CPU state: `pc x1..x31 mstatus mie mtvec mepc mcause
mscratch` in hex, prefixed with `I` when QEMU reported an interrupt between
the previous state and this one, else `S`. The trace is QEMU's observation,
used to test the Lean model; it is not trusted by any proof."""
import re
import sys

FIELDS = ['mstatus', 'mie', 'mtvec', 'mepc', 'mcause', 'mscratch']


def states(lines):
    cur, irq = None, False
    for line in lines:
        if line.startswith('riscv_cpu_do_interrupt') and 'async:0' in line and 'cause:00000008' in line:
            continue  # a user-mode ecall: the end of the test program
        if line.startswith('riscv_cpu_do_interrupt'):
            if 'async:1' not in line:
                raise SystemExit(f'synchronous exception in trace: {line.strip()}')
            irq = True
            continue
        m = re.match(r'^ pc\s+([0-9a-f]+)$', line)
        if m:
            if cur is not None:
                yield cur
            cur = {'pc': int(m[1], 16), 'x': {}, 'irq': irq}
            irq = False
            continue
        if cur is None:
            continue
        m = re.match(r'^ (\w+)\s+([0-9a-f]{8})$', line)
        if m and m[1] in FIELDS:
            cur[m[1]] = int(m[2], 16)
        for reg, val in re.findall(r'x(\d+)/\w+\s+([0-9a-f]{8})', line):
            cur['x'][int(reg)] = int(val, 16)
    if cur is not None:
        yield cur


def main():
    # --user: a qemu-riscv32 user-mode trace, which has no CSRs; they are
    # recorded as zero and the replay does not compare them. --start sets
    # the first pc the model sees.
    args = sys.argv[1:]
    user = '--user' in args
    start = 0x20010000
    if '--start' in args:
        start = int(args[args.index('--start') + 1], 0)
        del args[args.index('--start'):args.index('--start') + 2]
    args = [a for a in args if a != '--user']
    src, dst, limit = args[0], args[1], int(args[2])
    n = dups = 0
    prev = None
    with open(src, errors='replace') as f, open(dst, 'w') as out:
        started = False
        for s in states(f):
            # The model starts at the firmware entry, after QEMU's reset ROM.
            started = started or s['pc'] == start
            if not started:
                continue
            if user:
                for k in FIELDS:
                    s.setdefault(k, 0)
            if len(s['x']) != 32 or any(k not in s for k in FIELDS):
                continue  # a state cut off at the end of the log
            vals = [s['pc']] + [s['x'][i] for i in range(1, 32)] + [s[k] for k in FIELDS]
            # Under -icount QEMU ends a translation block at a device access
            # and logs the same state again before re-executing. No
            # instruction of the scope leaves the whole state unchanged
            # except a jump to itself, which is a failure state anyway.
            if vals == prev and not s['irq']:
                dups += 1
                continue
            prev = vals
            out.write(('I ' if s['irq'] else 'S ') + ' '.join(f'{v:x}' for v in vals) + '\n')
            n += 1
            if n >= limit:
                break
    print(f'{n} states ({dups} repeated QEMU log entries dropped)')


if __name__ == '__main__':
    main()
