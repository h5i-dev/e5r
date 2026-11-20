#!/usr/bin/env python3
"""Independent review of the partitioned interrupt invariant (support-lean4 e41afad).

Original e5r code, Apache-2.0. Each control makes one of the new checker
conditions trivially true (same term shape) in Theories/Absint.lean (scratch copy in /dev/shm) and recompiles
Absint.lean and AbsintSound.lean with the pinned Lean. A condition is
load-bearing if the soundness proof no longer goes through: the first error
must be in AbsintSound.lean and be a proof failure, not an elaboration error
in Absint.lean. A control that compiles means the soundness proof does not
need that condition (reported, not necessarily a bug).

Usage: partition_controls.py   (needs Theories oleans in .lake)
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

RV32 = Path(__file__).resolve().parents[1]
CHAIN = ['Theories/Absint.lean', 'Theories/AbsintSound.lean']
A = 'Theories/Absint.lean'

CONTROLS = [
    ('handler successors may leave the partition',
     "    irqOk cfg cert j n.s &&\n    -- A handler node's successors are handler nodes of the same partition.\n"
     "    (!n.s.hnd || n.succ.all fun e => e.nodes.all fun h => cert.gOf h == cert.gOf j)",
     "    irqOk cfg cert j n.s &&\n    -- A handler node's successors are handler nodes of the same partition.\n"
     "    (!n.s.hnd || n.succ.all fun e => e.nodes.all fun h => cert.gOf h == cert.gOf h)"),
    ('interrupt may enter a handler node of another partition',
     "h.1 == code && cert.gOf h.2 == cert.gOf j && covered cert e h.2",
     "h.1 == code && cert.gOf h.2 == cert.gOf h.2 && covered cert e h.2"),
    ('mret checked against partition 0 (G) instead of the node\'s own',
     "(instrOk cfg cert (cert.Gat (cert.gOf j)) n ||",
     "(instrOk cfg cert cert.G n ||"),
    ('interruptible node checked against partition 0 (G)',
     "  let G := cert.Gat (cert.gOf j)\n  codes.isEmpty || (!s.hnd && interruptibleOk cfg cert G s",
     "  let G := cert.Gat (cert.gOf j)\n  codes.isEmpty || (!s.hnd && interruptibleOk cfg cert cert.G s"),
    ('extra invariants Gs not well-formed-checked',
     "(cert.G :: cert.Gs).all (·.all fun c =>",
     "[cert.G].all (·.all fun c =>"),
]

ELAB = re.compile(r'unknown (identifier|constant)|unexpected token|object file|Unknown|unknownIdentifier')


def compile_chain(root):
    for f in CHAIN:
        olean = root / '.lake/build/lib/lean' / (f[:-5] + '.olean')
        p = subprocess.run(['lake', 'env', 'lean', f, '-o', str(olean)], cwd=root,
                           capture_output=True, text=True, timeout=3600)
        out = p.stdout + p.stderr
        m = re.search(r'^(\S+?):(\d+):\d+: error(?:\([^)]*\))?: (.*)', out, re.M)
        if p.returncode != 0 or m:
            return (m[1], int(m[2]), m[3]) if m else (f, 0, out.strip()[-200:])
    return None


def main():
    scratch = Path(tempfile.mkdtemp(prefix='partition-controls-', dir='/dev/shm'))
    try:
        root = scratch / 'rv32'
        skip = {'firmware', 'build', 'review', 'Projects'}
        shutil.copytree(RV32, root, symlinks=True,
                        ignore=lambda d, names: [n for n in names if Path(d) == RV32 and n in skip])
        base = compile_chain(root)
        print(f'{"ok  " if base is None else "FAIL"} baseline compiles' + ('' if base is None else f': {base}'))
        if base is not None:
            sys.exit(1)
        src = (root / A).read_text()
        for name, old, new in CONTROLS:
            assert src.count(old) == 1, (name, src.count(old))
            (root / A).write_text(src.replace(old, new))
            err = compile_chain(root)
            (root / A).write_text(src)
            if err is None:
                print(f'NOTE {name}: soundness proof still compiles (condition not needed by the proof)')
            else:
                f, line, msg = err
                kind = 'ELAB' if ELAB.search(msg) else 'REJECTED'
                tag = 'ok  ' if (f.endswith('AbsintSound.lean') and kind == 'REJECTED') else 'FAIL'
                print(f'{tag} {name}: {kind} in {f}:{line}: {msg[:110]}')
        compile_chain(root)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


if __name__ == '__main__':
    main()
