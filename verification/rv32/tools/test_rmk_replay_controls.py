#!/usr/bin/env python3
"""Negative controls for the RMK QEMU virt replay (tools/ReplayVirt.lean).

Given a format 2 trace of the RMK ELF that the replay accepts and the
semihosting sites, check that each edited trace and each mutated model is
rejected for the right reason (exit 1 and the expected message):

* a UART write's value changed, a UART write removed, a UART read logged at
  another width, a register changed;
* a register other than a0 changed right after a semihosting call (QEMU's
  step is accepted only with every other register kept);
* the semihosting sites not given (the model then faults at the ebreak);
* a board mutant built in a scratch copy: UART0's LCR register declared
  4 bytes wide (the model must refuse the firmware's byte access).

A control rejected for another reason, or a mutant that does not build, is a
failure of this test. Each control replays a prefix of the trace containing
the semihosting calls and the first UART reads and writes.

Usage: test_rmk_replay_controls.py TRACE SITE... [--no-mutants]"""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile

VERIFY = Path(__file__).resolve().parents[1]
REPLAY = VERIFY / '.lake/build/bin/replay_virt'


def end_marker(body):
    n = {k: sum(1 for l in body if l.startswith(k + ' ')) for k in 'SRWI'}
    return f'E {n["S"]:x} {n["R"]:x} {n["W"]:x} {n["I"]:x}'


def prefix(lines, sites):
    """Header and body through 300 states after the first UART write and
    the last semihosting call, with a fresh end marker."""
    body = lines[1:-1]
    states = [i for i, l in enumerate(body) if l.startswith('S ')]
    first_w = next(i for i, l in enumerate(body) if l.startswith('W '))
    semi = [i for i in states if int(body[i].split()[1], 16) in sites]
    if not semi:
        sys.exit('the trace reaches no semihosting call; cannot build the controls')
    last = max(first_w, semi[-1])
    cut = next(k for k, i in enumerate(states) if i > last)
    body = body[:states[min(cut + 300, len(states) - 1)] + 1]
    if not any(l.startswith('R ') for l in body):
        sys.exit('the trace prefix has no UART read; cannot build the controls')
    return lines[:1] + body, semi[0]


def edit(base, f):
    body = f(list(base[1:]))
    return base[:1] + body + [end_marker(body)]


def field(line, k, g):
    w = line.split()
    w[k] = g(w[k])
    return ' '.join(w)


def first(body, tag):
    return next(i for i, l in enumerate(body) if l.startswith(tag + ' '))


def controls(base, semi_state):
    inc = lambda h: format((int(h, 16) + 1) % 256, 'x')

    def set_at(tag, k, g):
        def f(b):
            i = first(b, tag)
            b[i] = field(b[i], k, g)
            return b
        return f

    def drop(tag):
        def f(b):
            del b[first(b, tag)]
            return b
        return f

    def corrupt_reg(b):
        k = [i for i, l in enumerate(b) if l.startswith('S ')][len(b) // 3]
        b[k] = field(b[k], 11, lambda h: format(int(h, 16) ^ 1, 'x'))  # a0
        return b

    def after_semi(b):
        # The state QEMU reached by the first semihosting call (the next
        # state after the one at the ebreak): change a1 (field 12).
        k = next(i for i, l in enumerate(b) if i > semi_state and l.startswith('S '))
        b[k] = field(b[k], 12, lambda h: format(int(h, 16) ^ 1, 'x'))
        return b

    return [
        ('unchanged prefix', edit(base, lambda b: b), True, 0, 'agree'),
        ('UART write value changed', edit(base, set_at('W', 2, inc)), True, 1, 'device writes'),
        ('UART write removed', edit(base, drop('W')), True, 1, 'device writes'),
        ('UART read logged 4 bytes wide', edit(base, set_at('R', 3, lambda h: '4')), True, 1, 'QEMU\'s next MMIO read'),
        ('register changed', edit(base, corrupt_reg), True, 1, 'x10 model'),
        ('register other than a0 changed by a semihosting call', edit(base, after_semi), True, 1, 'x11 model'),
        ('semihosting sites not given', edit(base, lambda b: b), False, 1, 'model fault'),
    ]


def run(replay, lines, sites, work, name):
    path = work / (name.replace(' ', '-') + '.txt')
    path.write_text('\n'.join(lines) + '\n')
    p = subprocess.run([str(replay), str(path)] + [str(s) for s in sites],
                       capture_output=True, text=True, timeout=1800)
    return p.returncode, (p.stdout + p.stderr).strip()


def main():
    args = [a for a in sys.argv[1:] if a != '--no-mutants']
    mutants = '--no-mutants' not in sys.argv
    trace, sites = Path(args[0]), [int(a, 0) for a in args[1:]]
    base, semi_state = prefix(trace.read_text().splitlines(), sites)
    failures = []
    with tempfile.TemporaryDirectory(dir='/dev/shm') as tmp:
        work = Path(tmp)
        for name, lines, with_sites, code, needle in controls(base, semi_state):
            got, out = run(REPLAY, lines, sites if with_sites else [], work, name)
            ok = got == code and needle in out
            print(f'{"ok  " if ok else "FAIL"} {name}: exit {got} (want {code}) {out.splitlines()[-1] if out else ""}')
            if not ok:
                failures.append(name)
        if mutants:
            name = 'mutant UART LCR declared 4 bytes wide'
            copy = work / 'rv32'
            shutil.copytree(VERIFY, copy, ignore=shutil.ignore_patterns('build', '*.olean', '*.ilean'),
                            symlinks=True)
            board = copy / 'Theories/Board/QemuVirtRv32.lean'
            text = board.read_text()
            old = '⟨0x10000003, "uart0.lcr", true, true, 1⟩'
            if text.count(old) != 1:
                failures.append(name)
                print(f'FAIL {name}: mutation site not found exactly once (TOOL)')
            else:
                board.write_text(text.replace(old, '⟨0x10000003, "uart0.lcr", true, true, 4⟩'))
                b = subprocess.run(['lake', 'build', 'replay_virt'], cwd=copy, capture_output=True, text=True)
                if b.returncode != 0:
                    failures.append(name)
                    print(f'FAIL {name}: the mutant does not build (TOOL)')
                else:
                    got, out = run(copy / '.lake/build/bin/replay_virt', base + [end_marker(base[1:])],
                                   sites, work, name)
                    ok = got == 1 and 'model fault' in out
                    print(f'{"ok  " if ok else "FAIL"} {name}: exit {got} (want 1) {out.splitlines()[-1] if out else ""}')
                    if not ok:
                        failures.append(name)
    if failures:
        sys.exit(f'{len(failures)} control(s) failed: {failures}')
    print('every RMK replay control was rejected for the expected reason')


if __name__ == '__main__':
    main()
