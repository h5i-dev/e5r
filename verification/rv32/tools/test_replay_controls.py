#!/usr/bin/env python3
"""Negative controls for the whole-firmware replay (tools/Replay.lean).

Given a format 2 trace that the replay accepts, check that it rejects
edited traces and mutated models, each for the right reason:

* exit 1 (a semantic mismatch, with the expected message) for a trace whose
  QEMU observations were changed: a device write's value, a missing or extra
  device access, a device read at another address, an interrupt's epc, a
  register;
* exit 2 (a trace error) for a trace that is cut off or whose lines were
  removed without the end marker being updated, or that is in format 1;
* exit 1 for model mutants built in a scratch copy: a device write off by
  one or dropped (the replay must compare device traffic, not count it), a
  RAM store losing a byte and an mtvec write off by four (the environment
  values must not hide RAM or CSR bugs).

A control rejected for another reason, or a mutant that does not build, is a
failure of this test, never a rejection. Each control replays a prefix of the
trace that contains the first device read, device write and interrupt.

Usage: test_replay_controls.py TRACE [--no-mutants]
"""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile

VERIFY = Path(__file__).resolve().parents[1]
REPLAY = VERIFY / '.lake/build/bin/replay'

MUTANTS = [
    ('device write off by one', 'Theories/Platform.lean',
     'interp B img o k ram i (evs ++ [⟨a, devVal w v⟩])', 'interp B img o k ram i (evs ++ [⟨a, devVal w v + 1⟩])',
     'device writes'),
    ('device write dropped', 'Theories/Platform.lean',
     'interp B img o k ram i (evs ++ [⟨a, devVal w v⟩])', 'interp B img o k ram i evs',
     'device writes'),
    ('word store to RAM loses its top byte', 'Theories/Platform.lean',
     '(a+3) (byteOf v 3)', '(a+3) (byteOf v 2)',
     'model'),
    ('mtvec write off by four', 'Theories/Hart.lean',
     "if v.extractLsb' 0 2 = 0 then fin { c with mtvec := v }",
     "if v.extractLsb' 0 2 = 0 then fin { c with mtvec := v + 4 }",
     'mtvec model'),
]


def end_marker(body):
    n = {k: sum(1 for l in body if l.startswith(k + ' ')) for k in 'SRWI'}
    return f'E {n["S"]:x} {n["R"]:x} {n["W"]:x} {n["I"]:x}'


def prefix(lines):
    """Header and body up to a few states after the first interrupt, with a
    fresh end marker."""
    body = lines[1:-1]
    first_irq = next(i for i, l in enumerate(body) if l.startswith('I '))
    states = [i for i, l in enumerate(body) if l.startswith('S ') and i > first_irq]
    body = body[:states[200] + 1]
    if not any(l.startswith('R ') for l in body) or not any(l.startswith('W ') for l in body):
        sys.exit('the trace prefix has no device read or write; cannot build the controls')
    return lines[:1] + body


def first(body, tag):
    return next(i for i, l in enumerate(body) if l.startswith(tag + ' '))


def edit(base, f, remark=True):
    """Apply f to the body; recompute the end marker unless remark is False."""
    body = list(base[1:])
    body = f(body)
    out = base[:1] + body
    return out + [end_marker(body)] if remark else out + [end_marker(base[1:])]


def field(line, k, g):
    w = line.split()
    w[k] = g(w[k])
    return ' '.join(w)


def trace_controls(base):
    inc = lambda h: format((int(h, 16) + 1) % 2**32, 'x')

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

    def dup(tag):
        def f(b):
            i = first(b, tag)
            b.insert(i, b[i])
            return b
        return f

    def corrupt_reg(b):
        k = [i for i, l in enumerate(b) if l.startswith('S ')][len(b) // 4 or 1]
        b[k] = field(b[k], 11, lambda h: format(int(h, 16) ^ 1, 'x'))  # a0
        return b

    other_mtime = lambda h: format(int(h, 16) ^ 4, 'x')  # mtime_lo <-> mtime_hi
    return [
        ('unchanged prefix', edit(base, lambda b: b), 0, 'agree'),
        ('device write value changed', edit(base, set_at('W', 2, inc)), 1, 'device writes'),
        ('device write removed', edit(base, drop('W')), 1, 'device writes'),
        ('device write duplicated', edit(base, dup('W')), 1, 'device writes'),
        ('device read removed', edit(base, drop('R')), 1, 'model reads device'),
        ('device read duplicated', edit(base, dup('R')), 1, 'model performed no such read'),
        ('device read at another address', edit(base, set_at('R', 1, other_mtime)), 1, 'model reads device'),
        ('device read value changed', edit(base, set_at('R', 2, inc)), 1, 'model'),
        ('interrupt epc changed', edit(base, set_at('I', 2, lambda h: format(int(h, 16) + 2, 'x'))), 1, 'epc'),
        ('interrupt removed', edit(base, drop('I')), 1, 'model'),
        ('register changed', edit(base, corrupt_reg), 1, 'x10 model'),
        ('end marker removed', base[:], 2, 'end marker missing'),
        ('device write removed, end marker kept', edit(base, drop('W'), remark=False), 2, 'counts'),
        ('format 1 (no header)', edit(base, lambda b: b)[1:], 2, 'format 2'),
    ]


def run(replay, lines, work, name):
    path = work / (name.replace(' ', '-').replace('(', '').replace(')', '') + '.txt')
    path.write_text('\n'.join(lines) + '\n')
    p = subprocess.run([str(replay), str(path)], capture_output=True, text=True, timeout=600)
    return p.returncode, (p.stdout + p.stderr).strip()


def check(name, got, out, code, needle, failures):
    ok = got == code and needle in out
    msg = out.splitlines()[0] if out else ''
    print(f'{"ok  " if ok else "FAIL"} {name}: exit {got} (want {code}) {msg[:150]}')
    if not ok:
        failures.append(name)


def mutants(base, work, failures):
    scratch = Path(tempfile.mkdtemp(prefix='replay-mutant-', dir='/dev/shm' if Path('/dev/shm').is_dir() else None))
    try:
        src = scratch / 'rv32'
        # Keep .lake (the mutant rebuilds only what depends on the change);
        # leave out the large top-level directories the replay does not use.
        skip = {'firmware', 'build', 'review'}
        shutil.copytree(VERIFY, src, symlinks=True,
                        ignore=lambda d, names: [n for n in names if Path(d) == VERIFY and n in skip])
        for name, rel, old, new, needle in MUTANTS:
            f = src / rel
            orig = f.read_text()
            if orig.count(old) != 1:
                print(f'FAIL mutant {name}: mutation site not found exactly once (TOOL)')
                failures.append(name)
                continue
            f.write_text(orig.replace(old, new))
            b = subprocess.run(['lake', 'build', 'replay'], cwd=src, capture_output=True, text=True)
            if b.returncode != 0:
                print(f'FAIL mutant {name}: does not build (TOOL, not a rejection)')
                failures.append(name)
            else:
                got, out = run(src / '.lake/build/bin/replay', base, work, 'mutant')
                check(f'mutant {name}', got, out, 1, needle, failures)
            f.write_text(orig)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    lines = [l for l in Path(args[0]).read_text().splitlines() if l]
    if lines[:1] != ['V 2']:
        sys.exit('the controls need a format 2 trace')
    base = prefix(lines)
    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for name, t, code, needle in trace_controls(base):
            got, out = run(REPLAY, t, work, name)
            check(name, got, out, code, needle, failures)
        if '--no-mutants' not in sys.argv:
            mutants(edit(base, lambda b: b), work, failures)
    if failures:
        sys.exit(f'{len(failures)} replay control(s) failed: {failures}')
    print('every replay control was rejected for the expected reason')


if __name__ == '__main__':
    main()
