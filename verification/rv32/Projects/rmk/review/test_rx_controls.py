#!/usr/bin/env python3
"""Adversarial controls for main's checkpoint trees and UART receive poll (review of f8f1c44).

Original e5r code, Apache-2.0. Each control drops or weakens ONE hypothesis (or strengthens one
claim) in a scratch copy of main's sources and recompiles from the changed module to the end of
the chain. It passes only if the first error is in the expected declaration and is a proof
failure (REJECTED), not an elaboration failure. Main's tree is never modified.

Usage: test_rx_controls.py MAIN_RV32_DIR   (the directory must hold a fresh module-by-module
build of the chain in .lake, e.g. from build_main.sh; Projects/rmk/review/RxAudit.lean included)
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

R = 'Projects/rmk'
CHAIN = [f'{R}/Trees.lean', f'{R}/Fetch.lean', f'{R}/DevRead.lean', f'{R}/Deframer/RxFetch.lean',
         f'{R}/Deframer/RxSegs.lean', f'{R}/Deframer/Rx.lean', f'{R}/review/RxAudit.lean']
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
    ('device read: register width check dropped (lbu from a non-byte register)',
     [replace(f'{R}/DevRead.lean', '(hw : d.width = 1)', '(hw : True)')],
     f'{R}/DevRead.lean', 'lands_lbu_dev'),
    ('device read: successors claimed only for the value 0 (oracle not quantified)',
     [replace(f'{R}/DevRead.lean',
              '(h : ∀ v : Word, Lands B img P ⟨m.core.wr rd (extend .b false (devVal .b v)) (m.core.pc + len), m.ram⟩)',
              '(h : Lands B img P ⟨m.core.wr rd (extend .b false (devVal .b 0)) (m.core.pc + len), m.ram⟩)'),
      replace(f'{R}/DevRead.lean', '  rw [this]; exact h (o 0)', '  rw [this]; exact h')],
     f'{R}/DevRead.lean', 'lands_lbu_dev'),
    ('trees: a non-quiet core\'s interrupt successor claimed to continue at the next instruction',
     [replace(f'{R}/review/RxAudit.lean', '    ∃ x, Step B img ⟨c1, M0⟩ x [] ∧ x.core.pc = 0x80000000 ∧',
              '    ∃ x, Step B img ⟨c1, M0⟩ x [] ∧ x.core.pc = 0x80004376 ∧')],
     f'{R}/review/RxAudit.lean', 'irq_counter'),
    ('rx: loop entered with cap = 0 allowed (cap ≥ 0, i ≤ cap)',
     [replace(f'{R}/Deframer/Rx.lean', '  cap : 1 ≤ (c0.get 20).toNat', '  cap : 0 ≤ (c0.get 20).toNat'),
      replace(f'{R}/Deframer/Rx.lean', '  lt : i < (c0.get 20).toNat', '  lt : i ≤ (c0.get 20).toNat')],
     f'{R}/Deframer/Rx.lean', 'rx_loop'),
    ('rx: assert_offset stack byte not required to be in RAM',
     [replace(f'{R}/Deframer/Rx.lean', '  stk : B.inRam (c0.get 2 + 0xffffffe0#32 + 0x0000000f#32) 1 = true',
              '  stk : True')],
     f'{R}/Deframer/Rx.lean', 'rx_loop'),
    ('rx: frame claim without the assert_offset stack byte',
     [replace(f'{R}/Deframer/Rx.lean',
              '  ∀ x : Word, ¬ ((c0.get 18).toNat ≤ x.toNat ∧ x.toNat < (c0.get 18).toNat + n) →\n'
              '    x ≠ c0.get 2 + 0xffffffe0#32 + 0x0000000f#32 → M x = M0 x',
              '  ∀ x : Word, ¬ ((c0.get 18).toNat ≤ x.toNat ∧ x.toNat < (c0.get 18).toNat + n) →\n'
              '    True → M x = M0 x')],
     f'{R}/Deframer/Rx.lean', 'rx_loop'),
    ('rx: LSR address off by one (0x10000004, not a device register)',
     [replace(f'{R}/Deframer/Rx.lean', '  lsr : c0.get 21 = 0x10000005', '  lsr : c0.get 21 = 0x10000004')],
     f'{R}/Deframer/Rx.lean', 'rx_loop'),
    ('audit: the faulting machine against main\'s Lands (no-fault field present)',
     [replace(f'{R}/review/RxAudit.lean',
              '    (hodd : m.core.pc.getLsbD 0 = true) : LandsW B img (fun _ => False) m := by',
              '    (hodd : m.core.pc.getLsbD 0 = true) : Lands B img (fun _ => False) m := by')],
     f'{R}/review/RxAudit.lean', 'weak_vacuous'),
    ('audit: non-vacuity witness with cap = 0',
     [replace(f'{R}/review/RxAudit.lean', 'if r.val = 20 then 16 else', 'if r.val = 20 then 0 else')],
     f'{R}/review/RxAudit.lean', 'rx_witness'),
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
    scratch = Path(tempfile.mkdtemp(prefix='rx-controls-', dir='/dev/shm'))
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
