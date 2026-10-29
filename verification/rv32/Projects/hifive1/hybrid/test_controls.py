#!/usr/bin/env python3
"""Mutation controls for the hybrid proofs (Projects/hifive1/hybrid).

Original e5r code, Apache-2.0. Each control changes one thing in a scratch
copy of verification/rv32 (an instruction byte in the image, the abstract
summary, the certificate, the wrap arithmetic, the masking premise) and
recompiles the affected modules with the pinned Lean. A control passes only
if the first error is in the expected declaration and is the expected kind:

  REJECTED  a proof obligation is false: decide/omega/unsolved goals/rfl
  ELAB      the source no longer elaborates (unknown name, pattern arity, ...)

A REJECTED control that fails with an ELAB error, or in another declaration,
is a failure of this test: an infrastructure error is never counted as a
rejected proof. The unmutated baseline must compile cleanly first.

Needs the modules' .olean files in .lake (the job runs or lake builds them).
Usage: test_controls.py [--keep]
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

RV32 = Path(__file__).resolve().parents[3]
H = 'Projects/hifive1/hybrid'
LOOP = ['Theories/Hybrid/Basic.lean', 'Theories/Hybrid/Wrap.lean', 'Theories/Hybrid/AIBridge.lean',
        f'{H}/demo/LoopImage.lean', f'{H}/demo/LoopConfig.lean', f'{H}/demo/LoopCert.lean',
        f'{H}/demo/LoopProof.lean', f'{H}/demo/LoopControls.lean']
RING = ['Projects/hifive1/Image.lean', 'Theories/Hybrid/Basic.lean', 'Theories/Hybrid/Wrap.lean',
        f'{H}/Ring.lean']

REJECT = re.compile(r'decide|evaluated to|omega could not|unsolved goals|rfl. failed|The rfl tactic|'
                    r'failed to reduce|Type mismatch|type mismatch')
ELAB = re.compile(r'unknown (identifier|constant|module|namespace)|unexpected token|object file|'
                  r'invalid pattern|too many arguments|invalid constructor|insufficient number of arguments|'
                  r'Function expected|function expected|application type mismatch|Unknown|Too many variable names')


def image_byte(path, addr, old, new):
    """Edit one byte of a generated image module (segment list of bytes)."""
    def f(src):
        m = re.search(r'⟨(0x[0-9a-f]+), \[([0-9, ]+)\]', src)
        base = int(m[1], 16)
        bs = [int(x) for x in m[2].split(',')]
        k = addr - base
        assert bs[k] == old, (hex(addr), bs[k], old)
        bs[k] = new
        return src[:m.start(2)] + ', '.join(map(str, bs)) + src[m.end(2):]
    return (path, f)


def replace(path, old, new, count=1):
    def f(src):
        assert src.count(old) == count, f'{path}: {old!r} occurs {src.count(old)} times'
        return src.replace(old, new)
    return (path, f)


CONTROLS = [
    # (name, chain, edits, expected file, expected declaration, kind)
    ('changed instruction in the demo image (c.and -> c.or at 0x20010024)', LOOP,
     [image_byte(f'{H}/demo/LoopImage.lean', 0x20010024, 0x75, 0x55)],
     f'{H}/demo/LoopProof.lean', 'i4', 'REJECTED'),
    ('changed instruction in the firmware image (c.and -> c.or at 0x200106ac)', RING,
     [image_byte('Projects/hifive1/Image.lean', 0x200106ac, 0x71, 0x51)],
     f'{H}/Ring.lean', 'i6', 'REJECTED'),
    ('false postcondition: the summary claims the new head is in 0..2', LOOP,
     [replace(f'{H}/demo/LoopConfig.lean', "def headAV : AV := .vals [0, 1, 2, 3]", "def headAV : AV := .vals [0, 1, 2]")],
     f'{H}/demo/LoopProof.lean', 'adapter', 'REJECTED'),
    ('false wrap: next h claimed to be h + 2', LOOP,
     [replace('Theories/Hybrid/Wrap.lean', 'if h = 3 then 0 else h + 1', 'if h = 3 then 0 else h + 2')],
     'Theories/Hybrid/Wrap.lean', 'next_lt', 'REJECTED'),
    ('invalid precondition: the entry node may hold head 4', LOOP,
     [replace(f'{H}/demo/LoopConfig.lean', "(s.get 12).leq (.rng 0 3) &&", "(s.get 12).leq (.rng 0 4) &&")],
     f'{H}/demo/LoopProof.lean', 'adapter', 'REJECTED'),
    ('interrupt obligation: the entry node may have MIE set', LOOP,
     [replace(f'{H}/demo/LoopConfig.lean', "s.mie == .no && ", "s.mie.mayBe false && ")],
     f'{H}/demo/LoopProof.lean', 'adapter', 'REJECTED'),
    ('tampered certificate: the delegation removed', LOOP,
     [replace(f'{H}/demo/LoopCert.lean', '  delegate := [(536936472, 0)]\n', '')],
     f'{H}/demo/LoopProof.lean', 'ai_check', 'REJECTED'),
    ('tampered certificate: the PWM values widened past 100', LOOP,
     [replace(f'{H}/demo/LoopCert.lean', '96, 97, 98, 99]', '96, 97, 98, 99, 132]', count=2)],
     f'{H}/demo/LoopProof.lean', 'ai_check', 'REJECTED'),
    ('infrastructure: masked runs without the masking premise (does not elaborate)', LOOP,
     [replace('Theories/Hybrid/Basic.lean', '| step {n m m₁ m₂} : Masked m → DetStep',
              '| step {n m m₁ m₂} : DetStep')],
     'Theories/Hybrid/Basic.lean', None, 'ELAB'),
    ('infrastructure: a missing import', LOOP,
     [replace(f'{H}/demo/LoopProof.lean', 'import Theories.Hybrid.Wrap\n', 'import Theories.Hybrid.Wrapp\n')],
     f'{H}/demo/LoopProof.lean', None, 'ELAB'),
]


def decl_at(src, line):
    name = None
    for i, l in enumerate(src.splitlines(), 1):
        if i > line:
            break
        m = re.match(r'\s*(?:private |protected )?(?:theorem|def|abbrev|structure|inductive|instance)\s+([^\s:({]+)', l)
        if m:
            name = m[1]
    return name


def compile_chain(root, chain, start):
    """Compile chain[start:] in order; return (file, line, message) of the
    first error, or None."""
    for f in chain[start:]:
        olean = root / '.lake/build/lib/lean' / (f[:-5] + '.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        p = subprocess.run(['lake', 'env', 'lean', f, '-o', str(olean)], cwd=root,
                           capture_output=True, text=True, timeout=1800)
        out = p.stdout + p.stderr
        m = re.search(r'^(\S+?):(\d+):\d+: error: (.*(?:\n(?!\S+:\d+:\d+:).*){0,6})', out, re.M)
        if p.returncode != 0 or m:
            if not m:
                return (f, 0, out.strip()[-300:])
            return (m[1], int(m[2]), m[3])
    return None


def main():
    keep = '--keep' in sys.argv
    scratch = Path(tempfile.mkdtemp(prefix='hybrid-controls-', dir='/dev/shm'))
    failures = []
    try:
        root = scratch / 'rv32'
        skip = {'firmware', 'build', 'review'}
        shutil.copytree(RV32, root, symlinks=True,
                        ignore=lambda d, names: [n for n in names if Path(d) == RV32 and n in skip])
        base = compile_chain(root, LOOP, 4)
        print(f'{"ok  " if base is None else "FAIL"} baseline: loop chain from LoopConfig compiles'
              + ('' if base is None else f': {base}'))
        if base is not None:
            sys.exit('baseline does not compile; controls are meaningless')
        for name, chain, edits, efile, edecl, kind in CONTROLS:
            saved = {}
            for path, f in edits:
                p = root / path
                saved[path] = p.read_text()
                p.write_text(f(saved[path]))
            start = min(chain.index(path) for path, _ in edits)
            err = compile_chain(root, chain, start)
            for path, src in saved.items():
                (root / path).write_text(src)
            # Restore the oleans of the mutated chain.
            if err is None:
                print(f'FAIL {name}: ACCEPTED (no error)')
                failures.append(name)
                compile_chain(root, chain, start)
                continue
            file, line, msg = err
            src = (root / file).read_text() if (root / file).exists() else ''
            decl = decl_at(src, line)
            first = msg.splitlines()[0][:110]
            got = 'ELAB' if ELAB.search(msg) else 'REJECTED' if REJECT.search(msg) else 'OTHER'
            ok = got == kind and file == efile and (edecl is None or decl == edecl)
            print(f'{"ok  " if ok else "FAIL"} {name}: {got} in {file}:{line} ({decl}): {first}')
            if not ok:
                failures.append(name)
            compile_chain(root, chain, start)
    finally:
        if not keep:
            shutil.rmtree(scratch, ignore_errors=True)
    if failures:
        sys.exit(f'{len(failures)} control(s) failed: {failures}')
    print('every control failed in the expected declaration for the expected reason')


if __name__ == '__main__':
    main()
