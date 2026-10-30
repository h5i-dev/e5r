#!/usr/bin/env python3
"""Adversarial controls for main's Some round against named callee contracts (review of 07a17e5),
and for this review's own refutations (SomeAudit.lean).

Original e5r code, Apache-2.0. Each control drops or weakens ONE hypothesis (or strengthens one
claim) in a scratch copy of main's sources and recompiles from the changed module to the end of
the chain. It passes only if the first error is in the expected declaration and is a proof
failure (REJECTED), not an elaboration failure. Main's tree is never modified.

Usage: test_some_controls.py MAIN_RV32_DIR   (the directory must hold a fresh module-by-module
build of the chain in .lake, e.g. from build_main.sh; Projects/rmk/review/SessAudit.lean and SomeAudit.lean included)
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

R = 'Projects/rmk'
CHAIN = [f'{R}/Deframer/SessionInv.lean', f'{R}/Deframer/SomePath.lean', f'{R}/Deframer/SomeRound.lean',
         f'{R}/review/SessAudit.lean', f'{R}/review/SomeAudit.lean']
REJECT = re.compile(r'decide|omega could not|unsolved goals|rfl. failed|The rfl tactic|Type mismatch|'
                    r'type mismatch|bv_omega|Application type mismatch|failed to synthesize|rewrite. failed|'
                    r'Did not find an occurrence|simp made no progress|linarith failed|contradiction|expected type `False`')
ELAB = re.compile(r'unknown (identifier|constant|module|namespace)|unexpected token|object file|Unknown')


def replace(path, old, new):
    def f(src):
        assert src.count(old) == 1, f'{path}: {old!r} occurs {src.count(old)} times'
        return src.replace(old, new)
    return (path, f)


def replace_all(path, old, new, count):
    def f(src):
        assert src.count(old) == count, f'{path}: {old!r} occurs {src.count(old)} times'
        return src.replace(old, new)
    return (path, f)


CONTROLS = [
    ('frame: Kept omits the Uart16550 stride byte (k < 4)',
     [replace(f'{R}/Deframer/SomeRound.lean', '  (∃ k < 5, x = ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 k)',
              '  (∃ k < 4, x = ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 k)')],
     f'{R}/Deframer/SomeRound.lean', 'extras_ctx'),
    ('frame: Kept omits the top byte of the flag-pointer word sp+0x24',
     [replace(f'{R}/Deframer/SomeRound.lean', '  ((m₀.core.get 2).toNat + 0x24 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat + 0x28) ∨',
              '  ((m₀.core.get 2).toNat + 0x24 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat + 0x27) ∨')],
     f'{R}/Deframer/SomeRound.lean', 'extras_ctx'),
    ('ABI: callee may change s10 (x26)',
     [replace(f'{R}/Deframer/SomeRound.lean', '  saved : ∀ r : Reg, r.val ∉ callerSaved → m.core.get r = m₀.core.get r',
              '  saved : ∀ r : Reg, r.val ∉ callerSaved → r.val ≠ 26 → m.core.get r = m₀.core.get r')],
     f'{R}/Deframer/SomeRound.lean', 'ctx_call'),
    ('result: encode_frame length up to 8 (the 7-byte slice check)',
     [replace(f'{R}/Deframer/SomeRound.lean', 'theorem slice_ok (t : BitVec 8) (len : Word) (h : t.toNat = 1 ∨ (t.toNat = 0 ∧ len.toNat ≤ 7)) :',
              'theorem slice_ok (t : BitVec 8) (len : Word) (h : t.toNat = 1 ∨ (t.toNat = 0 ∧ len.toNat ≤ 8)) :')],
     f'{R}/Deframer/SomeRound.lean', 'slice_ok'),
    ('boundary: Some path claimed never to stop at Pending 0x80004204',
     [replace(f'{R}/Deframer/SomeRound.lean', '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80004204 ∨ m.core.pc = 0x80003fa6 ∨',
              '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ False ∨ m.core.pc = 0x80003fa6 ∨')],
     f'{R}/Deframer/SomeRound.lean', 'post_disp'),
    ('boundary: Some path claimed never to stop at the 0xff path 0x80003fa6',
     [replace(f'{R}/Deframer/SomeRound.lean', '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80004204 ∨ m.core.pc = 0x80003fa6 ∨',
              '  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80004204 ∨ False ∨')],
     f'{R}/Deframer/SomeRound.lean', 'post_disp'),
    ('boundary: Some path claimed never to reach the send loop 0x8000429e',
     [replace(f'{R}/Deframer/SomeRound.lean', '    m.core.pc = 0x8000429e\n\n/-! ## Helpers -/', '    False\n\n/-! ## Helpers -/')],
     f'{R}/Deframer/SomeRound.lean', 'post_enc'),
    ('h26: s10 = 0x8002a7f4 (the empty-response flag store leaves the poll write set PW)',
     [replace_all(f'{R}/Deframer/SomeRound.lean', 'get 26 = 0x8002a7f0', 'get 26 = 0x8002a7f4', 4)],
     f'{R}/Deframer/SomeRound.lean', 'post_enc'),
    ('SW: the widening reverted (0x8002a7b0..0x8002a7ca), PW no longer inside SW',
     [replace(f'{R}/Deframer/SessionInv.lean', '(0x8002a7b0 ≤ x.toNat ∧ x.toNat < 0x8002a7f4) ∨',
              '(0x8002a7b0 ≤ x.toNat ∧ x.toNat < 0x8002a7ca) ∨')],
     f'{R}/Deframer/SomeRound.lean', 'kept_pw'),
    ('audit: dispatch jump-table word misstated (0x8000023c), the rodata check must reject it',
     [replace(f'{R}/review/SomeAudit.lean', 'def rtS : List ((Nat × Nat) × Word) := [((0x800210dc, 4), 0x80000238#32)]',
              'def rtS : List ((Nat × Nat) × Word) := [((0x800210dc, 4), 0x8000023c#32)]')],
     f'{R}/review/SomeAudit.lean', 'dispatch_contract_false'),
    ('audit: first dispatch instruction misstated (addi sp,-0x3f0), the fetch check must reject it',
     [replace(f'{R}/review/SomeAudit.lean', '(0x800001f2#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xfffffc20#32',
              '(0x800001f2#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xfffffc10#32')],
     f'{R}/review/SomeAudit.lean', 'dispatch_contract_false'),
    ('audit: encode refutation with the real UART struct pointer (no alias with the buffer)',
     [replace(f'{R}/review/SomeAudit.lean', '   memT [(0x8002a784, 0x95), (0x8002a785, 0xa7), (0x8002a786, 2), (0x8002a787, 0x80), (0x8002a7b1, 0x55)]⟩',
              '   memT [(0x8002a784, 0xc0), (0x8002a785, 0xa1), (0x8002a786, 2), (0x8002a787, 0x80), (0x8002a7b1, 0x55)]⟩')],
     f'{R}/review/SomeAudit.lean', 'kept_E'),
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
    scratch = Path(tempfile.mkdtemp(prefix='some-controls-', dir='/dev/shm'))
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
