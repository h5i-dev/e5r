#!/usr/bin/env python3
"""Negative controls for `e5r-verify check`: each must produce the stated
status, and none may report `proved`. Run from the repository root after a
release build of e5r-verify and with the pinned Lean on PATH."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
VERIFY = ROOT / 'verification/rv32'
BIN = Path(os.environ.get('E5R_VERIFY', ROOT / 'target/release/e5r-verify'))
WORK = VERIFY / 'build/controls'


def run(job):
    path = WORK / f'{job["id"]}.json'
    path.write_text(json.dumps(job))
    out = subprocess.run([BIN, 'check', path], capture_output=True, text=True)
    return json.loads(out.stdout), out.returncode


def base():
    job = json.loads((VERIFY / 'jobs/hifive1-clamp32.json').read_text())
    job['root'] = '../..'
    job['build'] = []
    return job


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    proof = VERIFY / 'Projects/hifive1/clamp/Proof.lean'
    false_proof = VERIFY / 'Projects/hifive1/clamp/ControlFalse.lean'
    sorry_proof = VERIFY / 'Projects/hifive1/clamp/ControlSorry.lean'
    false_proof.write_text(proof.read_text().replace(
        'theorem wraps : spec 0xfffffffa = 1 := by decide',
        'theorem wraps : spec 0xfffffffa = 6 := by decide'))
    sorry_proof.write_text(proof.read_text().replace(
        'theorem wraps : spec 0xfffffffa = 1 := by decide',
        'theorem wraps : spec 0xfffffffa = 6 := by sorry'))
    skip = VERIFY / 'Projects/hifive1/clamp/ControlSkip.lean'
    skip.write_text('import Lean\nopen Lean Elab Command\nrun_cmd liftCoreM do\n'
                    '  let decl := Declaration.thmDecl { name := `E5R.bad, levelParams := [], '
                    'type := mkConst ``False, value := mkConst ``True.intro }\n'
                    '  withOptions (fun o => o.setBool (Name.mkStr2 "debug" ("skipKernel" ++ "TC")) true) '
                    '(addDecl decl)\n')
    imp = VERIFY / 'Projects/hifive1/clamp/ControlImport.lean'
    imp.write_text('import Theories.Absint\nnamespace E5R.Hifive1.Clamp\ntheorem ok : True := trivial\n'
                   'end E5R.Hifive1.Clamp\n')
    failures = []
    try:
        cases = []
        j = base(); j['id'] = 'control-identity'; j['elf_sha256'] = '0' * 64
        cases.append((j, 'error', 'a changed ELF identity'))
        j = base(); j['id'] = 'control-false'; j['modules'] = ['Projects/hifive1/clamp/ControlFalse.lean']
        cases.append((j, 'failed', 'a false theorem'))
        j = base(); j['id'] = 'control-sorry'; j['modules'] = ['Projects/hifive1/clamp/ControlSorry.lean']
        cases.append((j, 'error', 'a sorry'))
        j = base(); j['id'] = 'control-memory'; j['limits'] = {'seconds': 600, 'rss_mib': 64}
        cases.append((j, 'resource_exhausted', 'a 64 MiB memory limit'))
        j = base(); j['id'] = 'control-unsupported'; j['elf'] = 'Projects/hifive1/clamp/clamp.rs'
        j['elf_sha256'] = None
        cases.append((j, 'unsupported', 'a file that is not an ELF'))
        j = base(); j['id'] = 'control-theorem'; j['theorems'] = ['E5R.Hifive1.Clamp.no_such_theorem']
        cases.append((j, 'error', 'a theorem that does not exist'))
        # The independent review's bypass: a theorem added with kernel
        # checking switched off through metaprogramming.
        j = base(); j['id'] = 'control-skipkernel'; j['modules'] = ['Projects/hifive1/clamp/ControlSkip.lean']
        j['theorems'] = ['E5R.bad']
        cases.append((j, 'error', 'a theorem added without kernel checking'))
        j = base(); j['id'] = 'control-import'; j['modules'] = ['Projects/hifive1/clamp/ControlImport.lean']
        j['theorems'] = ['E5R.Hifive1.Clamp.ok']
        cases.append((j, 'error', 'an import the job does not check'))
        for job, want, what in cases:
            result, code = run(job)
            ok = result['status'] == want and code != 0
            print(f'{"ok  " if ok else "FAIL"} {what}: {result["status"]} (exit {code})')
            if not ok:
                failures.append(what)
                print('     ', result.get('message', '')[:300])
    finally:
        false_proof.unlink(missing_ok=True)
        sorry_proof.unlink(missing_ok=True)
        skip.unlink(missing_ok=True)
        imp.unlink(missing_ok=True)
        for p in VERIFY.glob('Projects/hifive1/clamp/Control*.olean'):
            p.unlink()
    if failures:
        sys.exit(f'{len(failures)} control(s) did not behave: {failures}')
    print('all controls behaved')


if __name__ == '__main__':
    main()
