#!/usr/bin/env python3
"""Observe SYSTEM candidates; Lean independently proves completeness and safety."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RV = ROOT / 'verification/rv32'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--completeness', action='store_true')
    args = parser.parse_args()
    job = json.loads((RV / 'jobs/thermostat-heater.json').read_text())
    digest = hashlib.sha256((RV / job['elf']).read_bytes()).hexdigest()
    assert digest == job['elf_sha256'], 'ELF differs from the reviewed job pin'
    assert f'ELF sha256 {digest},' in (RV / 'Projects/thermostat/Image.lean').read_text()
    source = '''import Projects.thermostat.Proof
import Projects.thermostat.ControlBytes
#eval IO.println (reprStr (E5R.Thermostat.Control.systemSites E5R.Thermostat.img))
'''
    with tempfile.TemporaryDirectory(prefix='thermostat-sites-', dir=RV / 'build') as tmp:
        path = Path(tmp) / 'Observe.lean'
        path.write_text(source)
        observed = subprocess.check_output(
            ['elan', 'run', 'leanprover/lean4:v4.35.0', 'lean', '-j1', str(path)],
            cwd=RV, env=dict(os.environ, LEAN_PATH='.'), text=True)
    sites = json.loads(observed)
    assert sites == sorted(set(sites)) and all(isinstance(a, int) for a in sites)
    if args.completeness:
        module = 'ControlSiteList.lean'
        code = """-- Observed candidates; both completeness and classification are kernel checked.
import Projects.thermostat.Proof
import Projects.thermostat.ControlBytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E5R.Thermostat.Control
open E5R

def expectedSites : List Nat := """ + json.dumps(sites) + """

theorem sites_checked : systemSites img = expectedSites := by decide +kernel

end E5R.Thermostat.Control
"""
    else:
        module = 'ControlSites.lean'
        code = """-- Each candidate is checked separately to bound kernel replay memory.
import Projects.thermostat.ControlSiteList
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat.Control
open E5R

def safeAt (a : Nat) : Bool := match fetchDecode img (BitVec.ofNat 32 a) with
  | none => true
  | some (i,_) => decide (Safe i)

def classifyFetch (f : Option (Word × Word)) : Bool :=
  match f with
  | none => true
  | some (bits,len) => match decode bits len with
    | none => true
    | some i => decide (Safe i)

theorem safeAt_fetch (a : Nat) : safeAt a = classifyFetch (fetch img (BitVec.ofNat 32 a)) := by
  unfold safeAt fetchDecode classifyFetch
  cases fetch img (BitVec.ofNat 32 a) with
  | none => rfl
  | some v =>
    rcases v with ⟨bits,len⟩
    simp only
    cases h : decode bits len <;> simp [h]

theorem safeAt_fast (a : Nat) (h1 : 0x80000000 ≤ (BitVec.ofNat 32 a).toNat)
    (h2 : (BitVec.ofNat 32 a).toNat+4 ≤ 0x800056a8) :
    safeAt a = classifyFetch (PackedFetch.fetchT PackedFetch.textByte (BitVec.ofNat 32 a)) :=
  (safeAt_fetch a).trans (congrArg classifyFetch (PackedFetch.fetch_text _ h1 h2))

"""
        code += '\n'.join(f'theorem safe{a} : safeAt {a} = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)' for a in sites)
        code += '\n\ntheorem candidates_checked : expectedSites.all safeAt = true := by\n  simp [expectedSites,'
        code += ','.join('safe' + str(a) for a in sites) + ']\nend E5R.Thermostat.Control\n'
    if args.check:
        assert code == (RV / 'Projects/thermostat' / module).read_text()
        print(f'PASS: {len(sites)} SYSTEM candidate addresses match the pinned image')
    else:
        print(code, end='')


if __name__ == '__main__':
    main()
