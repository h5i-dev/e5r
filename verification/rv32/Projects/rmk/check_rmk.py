#!/usr/bin/env python3
"""Check the RMK proofs the way `e5r-verify check` checks a job, until the job
runner can export RAM-resident images (main owns job.rs; the exporter worker
owns `ram-image`).

Original e5r code, Apache-2.0. Stages, all in a fresh scratch tree in /dev/shm
(no .olean is reused from the working tree):

1. the ELF's sha256 must be the pin; Elf.lean is regenerated from it
   (gen_elf.py, main's 64-byte little-endian packing rule);
2. a forbidden-word scan of every module (comments and strings stripped), with
   the runner's list (crates/e5r-verify/src/job.rs FORBIDDEN);
3. every module compiled from source with the pinned Lean, in import order;
4. every module replayed by `leanchecker` (fresh kernel);
5. `#print axioms` of every theorem in the named namespaces: only propext,
   Classical.choice and Quot.sound are allowed.

Writes a JSON receipt. Usage: check_rmk.py ELF OUT.json [THEOREM_NAMESPACE ...]
"""
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

RV32 = Path(__file__).resolve().parents[2]
PIN = 'f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30'
ROOTS = ['Projects/rmk/MemmoveSmall.lean']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = ['sorry', 'admit', 'axiom', 'native_decide', 'ofReduceBool', 'implemented_by', 'extern',
             'unsafe', 'opaque', 'skipKernelTC', 'trustCompiler', 'run_cmd', 'run_elab', 'run_meta',
             '#eval', 'elab', 'elab_rules', 'macro', 'macro_rules', 'syntax', 'initialize',
             'builtin_initialize', 'addDecl']


def strip(code):
    """Remove comments (nested block, line) and string literals."""
    out, i, depth = [], 0, 0
    while i < len(code):
        if code.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and code.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if code.startswith('--', i):
            j = code.find('\n', i); i = len(code) if j < 0 else j; continue
        if code[i] == '"':
            j = i + 1
            while j < len(code) and code[j] != '"':
                j += 2 if code[j] == '\\' else 1
            i = j + 1; continue
        out.append(code[i]); i += 1
    return ''.join(out)


def imports(path):
    return re.findall(r'^import\s+(\S+)', path.read_text(), re.M)


def order(root, rels):
    seen, out = set(), []
    def visit(mod):
        if mod in seen:
            return
        seen.add(mod)
        f = root / (mod.replace('.', '/') + '.lean')
        for m in imports(f):
            visit(m)
        out.append(mod)
    for r in rels:
        visit(r[:-5].replace('/', '.'))
    return out


def run(cmd, cwd, env=None):
    t = time.time()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=env, timeout=3600)
    return p, time.time() - t


def main():
    elf, out = Path(sys.argv[1]), Path(sys.argv[2])
    spaces = sys.argv[3:] or ['E5R.Rmk']
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    receipt = {'schema': 'e5r.rmk.review-check.v1', 'elf_sha256': digest, 'stages': [], 'status': 'error'}
    def done(status, msg=''):
        receipt['status'] = status
        if msg:
            receipt['message'] = msg
        out.write_text(json.dumps(receipt, indent=2) + '\n')
        print(status, msg)
        sys.exit(0 if status == 'proved' else 1)
    if digest != PIN:
        done('error', f'ELF sha256 {digest} is not the pin')
    scratch = Path(tempfile.mkdtemp(prefix='rmk-check-', dir='/dev/shm'))
    try:
        root = scratch / 'rv32'
        shutil.copytree(RV32 / 'Theories', root / 'Theories')
        shutil.copytree(RV32 / 'Projects/rmk', root / 'Projects/rmk',
                        ignore=shutil.ignore_patterns('Elf.lean', '__pycache__'))
        for f in ['lean-toolchain']:
            shutil.copy(RV32 / f, root / f)
        p, _ = run([sys.executable, '-I', str(root / 'Projects/rmk/gen_elf.py'), str(elf),
                    str(root / 'Projects/rmk/Elf.lean')], root)
        if p.returncode:
            done('error', 'gen_elf: ' + p.stderr[-300:])
        mods = order(root, ROOTS)
        receipt['modules'] = mods
        receipt['sources'] = {m: hashlib.sha256((root / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest()
                              for m in mods}
        for m in mods:
            code = strip((root / (m.replace('.', '/') + '.lean')).read_text())
            words = set(w for t in re.split(r"[^A-Za-z0-9_.#]", code) for w in t.split('.'))
            bad = [f for f in FORBIDDEN if f in words]
            if bad:
                done('error', f'{m}: forbidden {bad}')
        env = {'PATH': '/home/ht2673/.elan/bin:/usr/bin:/bin', 'LEAN_PATH': str(root / 'build'),
               'HOME': '/home/ht2673'}
        for m in mods:
            o = root / 'build' / (m.replace('.', '/') + '.olean')
            o.parent.mkdir(parents=True, exist_ok=True)
            p, dt = run(['lean', m.replace('.', '/') + '.lean', '-o', str(o)], root, env)
            receipt['stages'].append({'name': f'lean {m}', 'seconds': round(dt, 1)})
            if p.returncode or re.search(r': error', p.stdout + p.stderr):
                done('failed', f'lean {m}: ' + (p.stdout + p.stderr)[-500:])
        for m in mods:
            p, dt = run(['leanchecker', m], root, env)
            receipt['stages'].append({'name': f'leanchecker {m}', 'seconds': round(dt, 1)})
            if p.returncode:
                done('failed', f'leanchecker {m}: ' + (p.stdout + p.stderr)[-500:])
        # Every theorem declared in the named namespaces, from the sources.
        names = []
        for m in mods:
            src = strip((root / (m.replace('.', '/') + '.lean')).read_text())
            ns = re.findall(r'^namespace\s+(\S+)', src, re.M)
            for t in re.findall(r'^theorem\s+(\S+)', src, re.M):
                full = f'{ns[-1]}.{t}' if ns else t
                if any(full.startswith(s + '.') for s in spaces):
                    names.append(full)
        audit = root / 'Audit.lean'
        audit.write_text(''.join(f'import {m}\n' for m in mods) +
                         ''.join(f'#print axioms {n}\n' for n in names))
        p, dt = run(['lean', 'Audit.lean'], root, env)
        receipt['stages'].append({'name': 'axioms', 'seconds': round(dt, 1)})
        found = re.findall(r"^'(.*)' depends on axioms: \[([^\]]*)\]", p.stdout, re.M)
        nodeps = re.findall(r"^'(.*)' does not depend on any axioms", p.stdout, re.M)
        got = {n: [a.strip() for a in ax.split(',') if a.strip()] for n, ax in found}
        got.update({n: [] for n in nodeps})
        missing = [n for n in names if n not in got]
        if missing or p.returncode:
            done('failed', f'axiom audit incomplete: {missing[:5]} {p.stderr[-300:]}')
        bad = {n: a for n, a in got.items() if set(a) - ALLOWED}
        receipt['theorems'] = [{'name': n, 'axioms': got[n]} for n in names]
        if bad:
            done('failed', f'disallowed axioms {bad}')
        done('proved')
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


if __name__ == '__main__':
    main()
