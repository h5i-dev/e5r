#!/usr/bin/env python3
"""Adversarial controls for main's session invariant and rounds (review of 094b8c6).

Original e5r code, Apache-2.0. Each control drops or weakens ONE hypothesis (or strengthens one
claim) in a scratch copy of main's sources and recompiles from the changed module to the end of
the chain. It passes only if the first error is in the expected declaration and is a proof
failure (REJECTED), not an elaboration failure. Main's tree is never modified.

Usage: test_rx_controls.py MAIN_RV32_DIR   (the directory must hold a fresh module-by-module
build of the chain in .lake, e.g. from build_main.sh; Projects/rmk/review/SessAudit.lean included)
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

R = 'Projects/rmk'
CHAIN = [f'{R}/Deframer/SessionInv.lean', f'{R}/Deframer/SomePath.lean', f'{R}/review/SessAudit.lean']
REJECT = re.compile(r'decide|omega could not|unsolved goals|rfl. failed|The rfl tactic|Type mismatch|'
                    r'type mismatch|bv_omega|Application type mismatch|failed to synthesize|rewrite. failed|'
                    r'Did not find an occurrence|simp made no progress|linarith failed|contradiction|expected type `False`')
ELAB = re.compile(r'unknown (identifier|constant|module|namespace)|unexpected token|object file|Unknown')


def replace(path, old, new):
    def f(src):
        assert src.count(old) == 1, f'{path}: {old!r} occurs {src.count(old)} times'
        return src.replace(old, new)
    return (path, f)


CONTROLS = [
    ('frame: session writes claimed to stay within 0x40 bytes below sp (receive uses 0x70)',
     [replace(f'{R}/Deframer/SessionInv.lean', '  (sp.toNat - 0x70 ≤ x.toNat ∧ x.toNat < sp.toNat) ∨ (0x8002a798 ≤ x.toNat',
              '  (sp.toNat - 0x40 ≤ x.toNat ∧ x.toNat < sp.toNat) ∨ (0x8002a798 ≤ x.toNat')],
     f'{R}/Deframer/SessionInv.lean', 'recvW_SW'),
    ('separation: task-flag byte allowed inside the deframer (flagSep dropped)',
     [replace(f'{R}/Deframer/SessionInv.lean',
              '  flagSep : (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w).toNat < dfr.toNat ∨\n'
              '    dfr.toNat + 12 ≤ (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w).toNat',
              '  flagSep : True')],
     f'{R}/Deframer/SessionInv.lean', 'none_of_recv'),
    ('boundary: round claimed never to stop at the read future 0x80003ff2',
     [replace(f'{R}/Deframer/SessionInv.lean',
              '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80003ff2 ∨ m.core.pc = 0x80004428 ∨ SomeAt m',
              '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ False ∨ m.core.pc = 0x80004428 ∨ SomeAt m')],
     f'{R}/Deframer/SessionInv.lean', 'session_round'),
    ('boundary: round claimed never to reach the Some point (SomeAt dropped)',
     [replace(f'{R}/Deframer/SessionInv.lean',
              '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80003ff2 ∨ m.core.pc = 0x80004428 ∨ SomeAt m',
              '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80003ff2 ∨ m.core.pc = 0x80004428 ∨ False')],
     f'{R}/Deframer/SessionInv.lean', 'session_round'),
    ('Some path: header high byte 0x7f (non-negative) claimed to take the unpark branch',
     [replace(f'{R}/Deframer/SomePath.lean',
              'theorem some_neg (m : Machine) (h : SomeAt m) (hneg : 0x80 ≤ (m.ram 0x8002a589).toNat) :',
              'theorem some_neg (m : Machine) (h : SomeAt m) (hneg : 0x7f ≤ (m.ram 0x8002a589).toNat) :')],
     f'{R}/Deframer/SomePath.lean', 'some_neg'),
    ('audit: UART struct placed in the receive buffer (base word at bufA) violates uSep',
     [replace(f'{R}/review/SessAudit.lean', '(hu : ramRead (mem t) uPtr .w = 0x8002a1c0) (hb : ramRead (mem t) 0x8002a1dc .w = 0x10000000)',
              '(hu : ramRead (mem t) uPtr .w = 0x8002a574) (hb : ramRead (mem t) 0x8002a590 .w = 0x10000000)'),
      replace(f'{R}/review/SessAudit.lean', '(hs : mem t 0x8002a1e0 = 1)', '(hs : mem t 0x8002a594 = 1)'),
      replace(f'{R}/review/SessAudit.lean', '  have e1 : ramRead (mem t) uPtr .w + 0x0000001c#32 = 0x8002a1dc := by rw [hu]; decide',
              '  have e1 : ramRead (mem t) uPtr .w + 0x0000001c#32 = 0x8002a590 := by rw [hu]; decide'),
      replace(f'{R}/review/SessAudit.lean', '  have e2 : ramRead (mem t) uPtr .w + 0x00000020#32 = 0x8002a1e0 := by rw [hu]; decide',
              '  have e2 : ramRead (mem t) uPtr .w + 0x00000020#32 = 0x8002a594 := by rw [hu]; decide')],
     f'{R}/review/SessAudit.lean', 'extras_of'),
    ('audit: witness core with the timer interrupt enabled is not quiet',
     [replace(f'{R}/review/SessAudit.lean', '  mie_ := false\n  mpie := false\n  mpp := 3\n  mieReg := 0\n',
              '  mie_ := true\n  mpie := false\n  mpp := 3\n  mieReg := 0x80\n')],
     f'{R}/review/SessAudit.lean', 'core_quiet'),
    ('audit: Some witness with header high byte 0x7f (some_neg must not apply)',
     [replace(f'{R}/review/SessAudit.lean', '(0x8002a58c, 3), (0x8002a589, 0x80)]', '(0x8002a58c, 3), (0x8002a589, 0x7f)]')],
     f'{R}/review/SessAudit.lean', 'some_neg_hits'),
]


def decl_at(src, line):
    name = None
    for i, l in enumerate(src.splitlines(), 1):
        if i > line:
            break
        m = re.match(r'\s*(?:private |protected )?(?:theorem|def|abbrev|structure|inductive)\s+([^\s:({]+)', l)
        if m:
            name = m[1]
    return name


def compile_chain(root, start, stop=None):
    for f in CHAIN[start:stop]:
        olean = root / '.lake/build/lib/lean' / (f[:-5] + '.olean')
        p = subprocess.run(['lake', 'env', 'lean', f, '-o', str(olean)], cwd=root,
                           capture_output=True, text=True, timeout=3600)
        out = p.stdout + p.stderr
        m = re.search(r'^(\S+?):(\d+):\d+: error(?:\([^)]*\))?: (.*(?:\n(?!\S+:\d+:\d+:).*){0,6})', out, re.M)
        if p.returncode != 0 or m:
            return (m[1], int(m[2]), m[3]) if m else (f, 0, out.strip()[-300:])
    return None


def main():
    src = Path(sys.argv[1]).resolve()
    scratch = Path(tempfile.mkdtemp(prefix='sess-controls-', dir='/dev/shm'))
    failures = []
    try:
        root = scratch / 'rv32'
        shutil.copytree(src, root, symlinks=True, ignore=shutil.ignore_patterns('.git'))
        base = compile_chain(root, 0)
        print(f'{"ok  " if base is None else "FAIL"} baseline: the chain compiles' + ('' if base is None else f': {base}'))
        if base is not None:
            sys.exit('baseline does not compile; controls are meaningless')
        for name, edits, efile, edecl in CONTROLS:
            saved = {}
            for path, f in edits:
                if path not in saved:
                    saved[path] = (root / path).read_text()
                (root / path).write_text(f((root / path).read_text()))
            start = min(CHAIN.index(path) for path, _ in edits)
            err = compile_chain(root, start)
            for path, s in saved.items():
                (root / path).write_text(s)
            if err is None:
                print(f'FAIL {name}: ACCEPTED (no error)')
                failures.append(name)
            else:
                file, line, msg = err
                text = (root / file).read_text() if (root / file).exists() else ''
                decl = decl_at(text, line)
                got = 'ELAB' if ELAB.search(msg) else 'REJECTED' if REJECT.search(msg) else 'OTHER'
                ok = got == 'REJECTED' and file == efile and decl == edecl
                print(f'{"ok  " if ok else "FAIL"} {name}: {got} in {file}:{line} ({decl}): {msg.splitlines()[0][:100]}')
                if not ok:
                    failures.append(name)
            stop = len(CHAIN) if err is None or err[0] not in CHAIN else CHAIN.index(err[0]) + 1
            compile_chain(root, start, stop)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    if failures:
        sys.exit(f'{len(failures)} control(s) failed: {failures}')
    print('every control failed in the expected declaration for the expected reason')


if __name__ == '__main__':
    main()
