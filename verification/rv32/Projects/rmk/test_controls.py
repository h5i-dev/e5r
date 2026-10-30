#!/usr/bin/env python3
"""Negative controls for the RMK memmove proofs (Projects/rmk).

Original e5r code, Apache-2.0. Each control changes one thing in a scratch
copy (an instruction byte of the packed image, the claimed result, the copy
direction condition, the size bound, a stack separation premise, a fetch
claim) and recompiles the affected modules with the pinned Lean. A control
passes only if the first error is in the expected declaration and of the
expected kind:

  REJECTED  a proof obligation is false (decide / omega / bv_omega / unsolved goals)
  ELAB      the source no longer elaborates (unknown name, missing import, ...)

An ELAB error where REJECTED is expected is a failure of this test, never a
rejected proof. The unmutated baseline must compile first.
Needs the Theories .olean files in .lake. Usage: test_controls.py [--keep]
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

RV32 = Path(__file__).resolve().parents[2]
R = 'Projects/rmk'
ELF = Path('/home/ht2673/.local/state/e5r-claude-isa-review-20261029T042314Z/rmk/rmk-qemu-riscv-f39d833f.elf')
CHAIN = [f'{R}/Elf.lean', f'{R}/Fetch.lean', f'{R}/MemmoveFetch.lean', f'{R}/Run.lean', f'{R}/Copy.lean',
         f'{R}/MemmoveLoops.lean', f'{R}/MemmoveSmall.lean', f'{R}/MemmoveBigLoops.lean',
         f'{R}/MemmoveAligned.lean', f'{R}/MemmoveContract.lean', f'{R}/Merge.lean', f'{R}/MemmoveMisLoop.lean',
         f'{R}/MemmoveMisStart.lean', f'{R}/MemmoveMisEnd.lean', f'{R}/MemmoveMis.lean', f'{R}/MemmoveFull.lean']

REJECT = re.compile(r'decide|evaluated to|omega could not|unsolved goals|rfl. failed|The rfl tactic|'
                    r'failed to reduce|Type mismatch|type mismatch|bv_omega')
ELAB = re.compile(r'unknown (identifier|constant|module|namespace)|unexpected token|object file|'
                  r'Unknown|unknownIdentifier|invalid pattern|too many arguments')


def image_byte(addr, old, new):
    """Change one byte of the packed ELF words in Elf.lean (file offset of a .text address)."""
    off = 4096 + (addr - 0x80000000)
    def f(src):
        m = re.search(r'\[\n(.*)\]⟩', src, re.S)
        words = [int(x) for x in m[1].split(',\n')]
        w, k = off // 64, off % 64
        assert words[w] // 256 ** k % 256 == old, (hex(addr), words[w] // 256 ** k % 256)
        words[w] += (new - old) * 256 ** k
        return src[:m.start(1)] + ',\n'.join(map(str, words)) + src[m.end(1):]
    return (f'{R}/Elf.lean', f)


def replace(path, old, new):
    def f(src):
        assert src.count(old) == 1, f'{path}: {old!r} occurs {src.count(old)} times'
        return src.replace(old, new)
    return (path, f)


CONTROLS = [
    ('changed instruction in the image (c.bnez -> c.beqz at 0x80020fd4)',
     [image_byte(0x80020fd5, 0xfa, 0xda)], f'{R}/MemmoveFetch.lean', 'f80020fd4', 'REJECTED'),
    ('false fetch claim (addi a2,a2,-2 at 0x80020fca)',
     [replace(f'{R}/MemmoveFetch.lean',
              'fetchDecode img 0x80020fca = some (Instr.opimm (AluOp.add) 12 12 0xffffffff#32, 2)',
              'fetchDecode img 0x80020fca = some (Instr.opimm (AluOp.add) 12 12 0xfffffffe#32, 2)')],
     f'{R}/MemmoveFetch.lean', 'f80020fca', 'REJECTED'),
    ('false result: memmove claimed to copy from src + 1',
     [replace(f'{R}/MemmoveSmall.lean', 'then ram (src + (x - dst)) else ram x',
              'then ram (src + (x - dst) + 1) else ram x')],
     f'{R}/MemmoveSmall.lean', 'finish', 'REJECTED'),
    ('forward copy claimed correct for any overlap',
     [replace(f'{R}/Copy.lean', '(d.toNat ≤ s.toNat ∨ s.toNat + n ≤ d.toNat) →',
              '(d.toNat ≤ s.toNat ∨ True) →')],
     f'{R}/Copy.lean', 'fwd_spec', 'REJECTED'),
    ('size bound relaxed to n < 17 (n = 16 takes the word path)',
     [replace(f'{R}/MemmoveSmall.lean',
              'theorem fwd_path (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)\n    (hn : (c.get 12).toNat < 16)',
              'theorem fwd_path (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)\n    (hn : (c.get 12).toNat < 17)')],
     f'{R}/MemmoveSmall.lean', 'fwd_path', 'REJECTED'),
    ('destination may overlap the save slots',
     [replace(f'{R}/MemmoveSmall.lean',
              '    (hdsep : (c.get 2).toNat ≤ (c.get 10).toNat ∨ (c.get 10).toNat + (c.get 12).toNat + 12 ≤ (c.get 2).toNat)\n    (hssep',
              '    (hdsep : True ∨ (c.get 10).toNat + (c.get 12).toNat + 12 ≤ (c.get 2).toNat)\n    (hssep')],
     f'{R}/MemmoveSmall.lean', 'finish', 'REJECTED'),
    ('n >= 16 with src, dst congruent only mod 2 (the misaligned path)',
     [replace(f'{R}/MemmoveAligned.lean',
              '    (hcong : (c.get 11).toNat % 4 = (c.get 10).toNat % 4) :',
              '    (hcong : (c.get 11).toNat % 2 = (c.get 10).toNat % 2) :')],
     f'{R}/MemmoveAligned.lean', 'big_aligned', 'REJECTED'),
    ('word copy claimed to need no direction condition',
     [replace(f'{R}/Copy.lean', '    (d.toNat ≤ s.toNat ∨ s.toNat + 4 ≤ d.toNat) →\n    words ram s d j = fwd ram s d (4 * j)',
              '    (d.toNat ≤ s.toNat ∨ True) →\n    words ram s d j = fwd ram s d (4 * j)')],
     f'{R}/Copy.lean', 'words_eq_fwd', 'REJECTED'),
    ('merged word: byte k claimed from prev while k + o < 3 only (wrong shift split)',
     [replace(f'{R}/Merge.lean', '      if k + o < 4 then byteOf p (k + o) else byteOf q (k + o - 4) := by',
              '      if k + o < 3 then byteOf p (k + o) else byteOf q (k + o - 4) := by')],
     f'{R}/Merge.lean', 'merge_byte', 'REJECTED'),
    ('misaligned path claimed to leave its stack temporaries alone (temps region shrunk)',
     [replace(f'{R}/MemmoveMis.lean', 'def InTemps (sp x : Word) : Prop := sp.toNat - 34 ≤ x.toNat ∧ x.toNat < sp.toNat - 24',
              'def InTemps (sp x : Word) : Prop := sp.toNat - 30 ≤ x.toNat ∧ x.toNat < sp.toNat - 24')],
     f'{R}/MemmoveMis.lean', 'big_mis', 'REJECTED'),
    ('infrastructure: a missing import (does not elaborate)',
     [replace(f'{R}/MemmoveLoops.lean', 'import Projects.rmk.Copy\n', 'import Projects.rmk.Copyy\n')],
     f'{R}/MemmoveLoops.lean', None, 'ELAB'),
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


def compile_chain(root, start):
    for f in CHAIN[start:]:
        olean = root / '.lake/build/lib/lean' / (f[:-5] + '.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        p = subprocess.run(['lake', 'env', 'lean', f, '-o', str(olean)], cwd=root,
                           capture_output=True, text=True, timeout=3600)
        out = p.stdout + p.stderr
        m = re.search(r'^(\S+?):(\d+):\d+: error(?:\([^)]*\))?: (.*(?:\n(?!\S+:\d+:\d+:).*){0,6})', out, re.M)
        if p.returncode != 0 or m:
            return (m[1], int(m[2]), m[3]) if m else (f, 0, out.strip()[-300:])
    return None


def main():
    keep = '--keep' in sys.argv
    scratch = Path(tempfile.mkdtemp(prefix='rmk-controls-', dir='/dev/shm'))
    failures = []
    try:
        root = scratch / 'rv32'
        root.mkdir()
        for d in ['Theories', R, '.lake']:
            shutil.copytree(RV32 / d, root / d, symlinks=True,
                            ignore=shutil.ignore_patterns('Projects', 'results') if d == '.lake' else None)
        (root / '.lake/build/lib/lean/Projects').mkdir(parents=True, exist_ok=True)
        for f in ['lakefile.lean', 'lean-toolchain', 'lake-manifest.json']:
            if (RV32 / f).exists():
                shutil.copy(RV32 / f, root / f)
        subprocess.run([sys.executable, '-I', str(root / R / 'gen_elf.py'), str(ELF), str(root / R / 'Elf.lean')],
                       check=True, capture_output=True)
        base = compile_chain(root, 0)
        print(f'{"ok  " if base is None else "FAIL"} baseline: the chain compiles' + ('' if base is None else f': {base}'))
        if base is not None:
            sys.exit('baseline does not compile; controls are meaningless')
        for name, edits, efile, edecl, kind in CONTROLS:
            saved = {}
            for path, f in edits:
                saved[path] = (root / path).read_text()
                (root / path).write_text(f(saved[path]))
            start = min(CHAIN.index(path) for path, _ in edits)
            err = compile_chain(root, start)
            for path, src in saved.items():
                (root / path).write_text(src)
            if err is None:
                print(f'FAIL {name}: ACCEPTED (no error)')
                failures.append(name)
            else:
                file, line, msg = err
                src = (root / file).read_text() if (root / file).exists() else ''
                decl = decl_at(src, line)
                got = 'ELAB' if ELAB.search(msg) else 'REJECTED' if REJECT.search(msg) else 'OTHER'
                ok = got == kind and file == efile and (edecl is None or decl == edecl)
                print(f'{"ok  " if ok else "FAIL"} {name}: {got} in {file}:{line} ({decl}): {msg.splitlines()[0][:100]}')
                if not ok:
                    failures.append(name)
            compile_chain(root, start)
    finally:
        if not keep:
            shutil.rmtree(scratch, ignore_errors=True)
    if failures:
        sys.exit(f'{len(failures)} control(s) failed: {failures}')
    print('every control failed in the expected declaration for the expected reason')


if __name__ == '__main__':
    main()
