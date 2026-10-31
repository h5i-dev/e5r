#!/usr/bin/env python3
"""Compact a QEMU single-instruction trace for Lean replay. The trace is
QEMU's observation, used to test the Lean model; it is not trusted by any
proof.

System mode (the default): the log of `qemu-system-riscv32 -d cpu,int
-trace memory_region_ops_read -trace memory_region_ops_write`, converted to
trace format 2 for tools/Replay.lean:

    V 2                         header
    S pc x1..x31 mstatus mie mtvec mepc mcause mscratch
    R addr value size           an MMIO read QEMU performed
    W addr value size           an MMIO write QEMU performed
    I cause epc                 an interrupt QEMU took, with its own epc
    E states reads writes irqs  end marker, with the counts

Every line between two `S` lines happened in that transition, in QEMU's
order. A missing end marker or a count that does not match means the trace
is cut off or edited. Format 1 (`S`/`I` state lines only, the interrupt
inferred from mepc and no device traffic) is no longer read by the firmware
replay: regenerate the trace with the two `-trace` options.

`--user`: a qemu-riscv32 user-mode trace in format 1, for tools/ReplayIsa;
it has no CSRs (recorded as zero, not compared), devices or interrupts.
`--start` sets the first pc the model sees.

A state with missing fields is an error except at the very end of the log
(QEMU stopped mid-dump); a synchronous exception is an error, except a
user-mode ecall, which ends a test program."""
import re
import sys

FIELDS = ['mstatus', 'mie', 'mtvec', 'mepc', 'mcause', 'mscratch']
PC = re.compile(r'^ pc\s+([0-9a-f]+)$')
CSR = re.compile(r'^ (\w+)\s+([0-9a-f]{8})$')
GPR = re.compile(r'x(\d+)/\w+\s+([0-9a-f]{8})')
IRQ = re.compile(r'^riscv_cpu_do_interrupt: hart:\d+, async:(\d), cause:([0-9a-f]+), epc:0x([0-9a-f]+)')
MMIO = re.compile(r'^memory_region_ops_(read|write) .* addr 0x([0-9a-f]+) value 0x([0-9a-f]+) size (\d+)')


def records(lines, user):
    """Yield ('S', state) and ('R'|'W'|'I', fields) in log order."""
    cur = None
    for line in lines:
        line = line.rstrip('\n')
        m = IRQ.match(line)
        if m:
            if m[1] == '0' and user and int(m[2], 16) == 8:
                continue  # a user-mode ecall: the end of the test program
            if m[1] != '1':
                raise SystemExit(f'synchronous exception in trace: {line.strip()}')
            if cur is not None:
                yield 'S', cur
                cur = None
            # QEMU prints the cause code without the interrupt bit.
            yield 'I', (int(m[2], 16) | 1 << 31, int(m[3], 16))
            continue
        m = MMIO.match(line)
        if m:
            if cur is not None:
                yield 'S', cur
                cur = None
            yield m[1][0].upper(), (int(m[2], 16), int(m[3], 16), int(m[4]))
            continue
        m = PC.match(line)
        if m:
            if cur is not None:
                yield 'S', cur
            cur = {'pc': int(m[1], 16), 'x': {}}
            continue
        if cur is None:
            continue
        m = CSR.match(line)
        if m and m[1] in FIELDS:
            cur[m[1]] = int(m[2], 16)
        for reg, val in GPR.findall(line):
            cur['x'][int(reg)] = int(val, 16)
    if cur is not None:
        yield 'S', cur


def main():
    args = sys.argv[1:]
    user = '--user' in args
    start = 0x20010000
    if '--start' in args:
        start = int(args[args.index('--start') + 1], 0)
        del args[args.index('--start'):args.index('--start') + 2]
    args = [a for a in args if a != '--user']
    src, dst, limit = args[0], args[1], int(args[2])
    n = dups = 0
    counts = {'R': 0, 'W': 0, 'I': 0}
    prev = None
    pending = []      # events since the last state written
    irq = False       # format 1: an interrupt since the last state
    incomplete = None
    out_lines = [] if user else ['V 2']
    with open(src, errors='replace') as f:
        started = False
        for kind, r in records(f, user):
            if kind != 'S':
                if started:
                    if user and kind != 'I':
                        raise SystemExit('MMIO access in a user-mode trace')
                    pending.append((kind, r))
                continue
            s = r
            # The model starts at the firmware entry, after QEMU's reset ROM.
            started = started or s['pc'] == start
            if not started:
                continue
            if incomplete is not None:
                raise SystemExit(f'incomplete CPU state in the middle of the log at pc {incomplete:#x}')
            if user:
                for k in FIELDS:
                    s.setdefault(k, 0)
            if len(s['x']) != 32 or any(k not in s for k in FIELDS):
                incomplete = s['pc']  # fine only if nothing follows
                continue
            vals = [s['pc']] + [s['x'][i] for i in range(1, 32)] + [s[k] for k in FIELDS]
            # Under -icount QEMU ends a translation block at a device access
            # and logs the same state again before re-executing. No
            # instruction of the scope leaves the whole state unchanged
            # except a jump to itself, which is a failure state anyway. A
            # repeat with events in between is kept, so the replay sees them.
            if vals == prev and not pending:
                dups += 1
                continue
            prev = vals
            if user:
                irq = any(k == 'I' for k, _ in pending)
                out_lines.append(('I ' if irq else 'S ') + ' '.join(f'{v:x}' for v in vals))
            else:
                for k, ev in pending:
                    out_lines.append(k + ' ' + ' '.join(f'{v:x}' for v in ev))
                    counts[k] += 1
                out_lines.append('S ' + ' '.join(f'{v:x}' for v in vals))
            pending = []
            n += 1
            if n >= limit:
                break
    # Events after the last state belong to a transition with no observed
    # end state; they are dropped, never attached to another transition.
    if not user:
        out_lines.append(f'E {n:x} {counts["R"]:x} {counts["W"]:x} {counts["I"]:x}')
    with open(dst, 'w') as out:
        out.write('\n'.join(out_lines) + '\n')
    extra = '' if user else f', {counts["R"]} MMIO reads, {counts["W"]} MMIO writes, {counts["I"]} interrupts'
    print(f'{n} states{extra} ({dups} repeated QEMU log entries dropped)')


if __name__ == '__main__':
    main()
