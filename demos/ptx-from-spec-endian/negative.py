#!/usr/bin/env python3
"""Refuse a stale supplied manifest and replay realistic semantic counterexamples."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--scratch',type=Path,default=Path('/mnt/scratch/e5r-ptx-from-spec'))
    args=parser.parse_args()
    scratch=args.scratch
    e5r=scratch/'cargo-target/release/e5r'
    controls=scratch/'controls'
    controls.mkdir(exist_ok=True)
    evidence=scratch/'evidence'
    evidence.mkdir(exist_ok=True)
    ptx=(HERE/'endian_xor.ptx').read_text()
    sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
    mutations={
        'wrong_byte_order':('shl.b32 %r12, %r11, 16;', 'shl.b32 %r12, %r11, 8;'),
        'wrong_index':('mad.lo.u32 %r5, %r2, %r3, %r4;', 'add.u32 %r5, %r4, 1;'),
        'dropped_tail':('setp.ge.u32 %p, %r5, %r0;', 'sub.u32 %r0, %r0, 1;\n    setp.ge.u32 %p, %r5, %r0;'),
    }
    summary=[]
    def check(name, file, pf=None, timeout=120):
        out=evidence/(name+'.json')
        command=[str(e5r),'ptx','check',str(file),'--spec',str(HERE/'contract.json'),
                 '--project',str(scratch/'lean-project'),'--keep',str(controls/name),
                 '--timeout',str(timeout),'--memory-mb','2500','--out',str(out)]
        if pf: command += ['--proof',str(pf)]
        run=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (controls/(name+'.log')).write_text(run.stdout)
        result=json.loads(out.read_text())
        assert run.returncode != 0 and result['verdict'] != 'proved', (name,result)
        return result
    for name,(old,new) in mutations.items():
        assert ptx.count(old)==1
        changed=ptx.replace(old,new)
        file=controls/(name+'.ptx')
        file.write_text(changed)
        if name=='wrong_byte_order':
            stale=check('stale_hash',file,HERE/'E5rProof.lean')
            assert 'different ptx' in ' '.join(stale['reasons']), stale
            summary.append({'name':'stale_hash','verdict':stale['verdict'],'rejected':True})
        auto=check(name+'_refutation',file)
        assert auto['verdict']=='refuted' and auto['counterexample']['replayed_in_lean'], auto
        summary.append({'name':name,'ptx_sha256':sha(changed),
                        'counterexample_verdict':auto['verdict'],
                        'counterexample_kind':auto['counterexample']['kind'],
                        'replayed_in_lean':True})
        print(json.dumps(summary[-1]),flush=True)
    (evidence/'negative-controls.json').write_text(json.dumps(summary,indent=2)+'\n')

if __name__=='__main__': main()
