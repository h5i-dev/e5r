#!/usr/bin/env python3
"""Negative controls for the encode_frame proof (Projects/rmk/Encode).

Original e5r code, Apache-2.0. Each control drops or weakens ONE hypothesis (or strengthens one
claim) in a scratch copy of main's sources and recompiles from the changed module to the end of
the chain. It passes only if the first error is in the expected declaration and is a proof
failure (REJECTED), not an elaboration failure. Main's tree is never modified.

Usage: test_encode_controls.py RV32_DIR   (the directory must hold a fresh module-by-module
build of the chain in .lake, e.g. from review/build_main.sh)
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

R = 'Projects/rmk'
CHAIN = [f'{R}/Encode/Sym.lean', f'{R}/Encode/Table.lean', f'{R}/Encode/Encode.lean', f'{R}/Encode/Spec.lean']
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
    ('contract: response byte 9 admitted (RynkError has 9 variants; 9 jumps through unrelated rodata)',
     [replace(f'{R}/Encode/Encode.lean', 'def respVals : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 0xff]',
              'def respVals : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0xff]')],
     f'{R}/Encode/Encode.lean', 'enc_check'),
    ('frame: callee stack claimed to stay within sp-0x50 (serialize goes to sp-0x60)',
     [replace(f'{R}/Encode/Encode.lean', '  | some (true, k) => decide ((-0x60 ≤ k ∧ k + w.bytes ≤ 0) ∨ (0x40 ≤ k ∧ k + w.bytes ≤ 0x48))',
              '  | some (true, k) => decide ((-0x50 ≤ k ∧ k + w.bytes ≤ 0) ∨ (0x40 ≤ k ∧ k + w.bytes ≤ 0x48))')],
     f'{R}/Encode/Encode.lean', 'enc_check'),
    ('headroom: SomeAt\'s old sp bound 0x8002a808 (callee frame may overlap the frame buffer)',
     [replace(f'{R}/Encode/Encode.lean', "def encE : Env := ⟨0x8002a854, 0x81000000 - 0x148⟩", "def encE : Env := ⟨0x8002a808, 0x81000000 - 0x148⟩")],
     f'{R}/Encode/Encode.lean', 'enc_check'),
    ('ABI: a0 (caller-saved, holds the result pointer) claimed preserved',
     [replace(f'{R}/Encode/Encode.lean', 'def calleeSaved : List Nat := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]',
              'def calleeSaved : List Nat := [2, 3, 4, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]')],
     f'{R}/Encode/Encode.lean', 'enc_check'),
    ('image: RynkError jump-table word for discriminant 0 misstated',
     [replace(f'{R}/Encode/Encode.lean', '[(0x80026410, .w, 0x80014096)', '[(0x80026410, .w, 0x80014098)')],
     f'{R}/Encode/Encode.lean', 'encRom_ok'),
    ('image: encode_frame entry instruction misstated (addi sp,-0x40)',
     [replace(f'{R}/Encode/Table.lean', '(0x80008d5c#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffb0#32',
              '(0x80008d5c#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffc0#32')],
     f'{R}/Encode/Encode.lean', 'encTbl_ok'),
    ('executor: older writes read through a non-disjoint newer write',
     [replace(f'{R}/Encode/Sym.lean', '    else if disj E b w\'.bytes a w.bytes then rdW E ws a w\n    else rdCat',
              '    else if true then rdW E ws a w\n    else rdCat')],
     f'{R}/Encode/Sym.lean', 'rdW_sound'),
    ('executor: an undecided branch followed only on its taken side',
     [replace(f'{R}/Encode/Sym.lean', '      if (s.pc + off).getLsbD 0 then none else some [⟨s.pc + off, s.r, s.mem⟩, ⟨next, s.r, s.mem⟩]',
              '      if (s.pc + off).getLsbD 0 then none else some [⟨s.pc + off, s.r, s.mem⟩]')],
     f'{R}/Encode/Sym.lean', 'astepI_sound'),
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
    scratch = Path(tempfile.mkdtemp(prefix='enc-controls-', dir='/dev/shm'))
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
