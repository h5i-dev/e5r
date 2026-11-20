#!/usr/bin/env python3
"""Convert a QEMU sifive_e `-d cpu,int -trace memory_region_ops_write` log into
the input of review/FwReplay.lean.

Original review code, Apache-2.0. Written independently of tools/qemu_trace.py
to audit it. Differences that matter:

* interrupts carry QEMU's own `epc` (`I <cause> <epc>`), so the replay does
  not have to infer the boundary from mepc;
* every MMIO write QEMU performed between two states is emitted
  (`W <addr> <value> <size>`) and the replay compares it with the model's
  device events, so device traffic is checked, not just counted;
* a state with missing registers is an error unless it is the very last one
  (the log being cut off), never silently skipped;
* a synchronous exception is an error, as in qemu_trace.py.

Output lines: `S pc x1..x31 mstatus mie mtvec mepc mcause mscratch`, `I`, `W`.
"""
import re
import sys

CSRS = ['mstatus', 'mie', 'mtvec', 'mepc', 'mcause', 'mscratch']
ENTRY = 0x20010000
PC_RE = re.compile(r'^ pc\s+([0-9a-f]+)\s*$')
CSR_RE = re.compile(r'^ (\w+)\s+([0-9a-f]{8})\s*$')
GPR_RE = re.compile(r'x(\d+)/\w+\s+([0-9a-f]{8})')
IRQ_RE = re.compile(r'riscv_cpu_do_interrupt: hart:\d+, async:(\d), cause:([0-9a-f]+), epc:0x([0-9a-f]+)')
MMIO_RE = re.compile(r'memory_region_ops_write .* addr 0x([0-9a-f]+) value 0x([0-9a-f]+) size (\d+)')


def complete(s):
    return s is not None and len(s['x']) == 31 and all(k in s for k in CSRS)


def main():
    src, dst, limit = sys.argv[1], sys.argv[2], int(sys.argv[3])
    started = False
    cur = None
    events = []          # events seen since `cur` started
    out = []
    n = dropped = irqs = writes = 0
    prev_vals = None

    def flush(final=False):
        nonlocal n, dropped, prev_vals
        if cur is None:
            return
        if not complete(cur):
            if final:
                return
            raise SystemExit(f'incomplete CPU state in the middle of the log at pc {cur["pc"]:#x}')
        vals = [cur['pc']] + [cur['x'][i] for i in range(1, 32)] + [cur[k] for k in CSRS]
        if vals == prev_vals and not cur['before']:
            dropped += 1     # QEMU re-logging the same state (icount I/O restart)
            return
        out.extend(cur['before'])
        out.append('S ' + ' '.join(f'{v:x}' for v in vals))
        prev_vals = vals
        n += 1

    with open(src, errors='replace') as f:
        for line in f:
            m = PC_RE.match(line)
            if m:
                pc = int(m[1], 16)
                started = started or pc == ENTRY
                if started:
                    flush()
                    if n >= limit:
                        cur = None
                        break
                    cur = {'pc': pc, 'x': {}, 'before': events}
                    events = []
                continue
            m = IRQ_RE.search(line)
            if m:
                if not started:
                    continue
                if m[1] != '1':
                    raise SystemExit(f'synchronous exception in trace: {line.strip()}')
                # QEMU prints the cause code without the interrupt bit.
                events.append(f'I {int(m[2], 16) | 1 << 31:x} {int(m[3], 16):x}')
                irqs += 1
                continue
            m = MMIO_RE.search(line)
            if m:
                if started:
                    events.append(f'W {int(m[1], 16):x} {int(m[2], 16):x} {m[3]}')
                    writes += 1
                continue
            if cur is None:
                continue
            m = CSR_RE.match(line)
            if m and m[1] in CSRS:
                cur[m[1]] = int(m[2], 16)
            for r, v in GPR_RE.findall(line):
                if r != '0':
                    cur['x'][int(r)] = int(v, 16)
        flush(final=True)
    # Events after the last emitted state belong to a transition we cannot
    # compare; drop them rather than attach them to the wrong one.
    with open(dst, 'w') as f:
        f.write('\n'.join(out) + '\n')
    print(f'{n} states, {irqs} interrupts, {writes} MMIO writes, {dropped} repeated states dropped')


if __name__ == '__main__':
    main()
