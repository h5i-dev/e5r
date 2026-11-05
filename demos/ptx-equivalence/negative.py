"""Prove the checker refuses stale and semantically broken PTX artifacts.
Rebind manifests for semantic mutations, so a stale hash is not the reason
those cases fail. Retain complete machine-readable check results.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess
D=Path(__file__).resolve().parent
W=Path(os.environ.get('E5R_DEMO_SCRATCH','/mnt/scratch/e5r-ptx-demo'))/'negative-equivalence'
exe=os.environ.get('E5R_VERIFY','/mnt/scratch/e5r-ptx-demo/cargo/release/e5r')
sha=lambda b:hashlib.sha256(b).hexdigest()


def main():
    W.mkdir(parents=True,exist_ok=True)
    source=(D/'optimized.ptx').read_text();proof=(D/'equivalence.lean').read_text()
    contract=json.loads((D/'equivalence.json').read_text());contract['original_ptx']=str(D/'original.ptx')
    cases={
        'stale-candidate':source.replace('2113665','2113666'),
        'wrong-multiply':source.replace('2113665','2113666'),
        'wrong-input-index':source.replace('%r6, %r1, 3','%r6, %r1, 2'),
        'wrong-tail-guard':source.replace('setp.ge.u32','setp.gt.u32'),
    }
    summary=[]
    for name,ptx in cases.items():
        if ptx==source:raise RuntimeError('mutation did not apply: '+name)
        out=W/name;out.mkdir(exist_ok=True)
        (out/'kernel.ptx').write_text(ptx)
        (out/'contract.json').write_text(json.dumps(contract,indent=2)+'\n')
        pf=proof
        if name!='stale-candidate':
            pf=re.sub(r'ptx=[0-9a-f]{64}','ptx='+sha(ptx.encode()),pf,count=1)
        pf=re.sub(r'spec=[0-9a-f]{64}','spec='+sha((out/'contract.json').read_bytes()),pf,count=1)
        (out/'proof.lean').write_text(pf)
        result=D/'results'/('negative-'+name+'.json')
        cmd=[exe,'ptx','check',str(out/'kernel.ptx'),'--spec',str(out/'contract.json'),
            '--proof',str(out/'proof.lean'),'--out',str(result),'--keep',str(out/'check'),
            '--timeout','180','--memory-mb','3072']
        run=subprocess.run(cmd,cwd=D.parent.parent,text=True,capture_output=True,timeout=400)
        doc=json.loads(result.read_text())
        if run.returncode==0 or doc['verdict']=='proved':raise AssertionError('accepted mutation '+name)
        if name=='stale-candidate':
            assert 'different ptx' in str(doc['reasons'])
        else:
            # Require failure in the semantic proof, not parsing, hashing or a timeout.
            assert doc['verdict']=='unknown' and 'does not compile' in str(doc['reasons']),doc
            assert not any(x in str(doc['reasons']) for x in ['stopped:', 'different ptx','different spec']),doc
        summary.append(dict(case=name,verdict=doc['verdict'],reasons=doc['reasons']))
        print(name,doc['verdict'],flush=True)
    (D/'results/negative-controls.json').write_text(json.dumps(summary,indent=2)+'\n')
    # Independent executable witnesses establish that seeded changes are real
    # defects, even when proof rejection reports a tactic/recursion limit.
    import fcntl, sys
    import cupy as cp
    import numpy as np
    sys.path.insert(0,str(D.parent/'verified-packing'))
    from benchmark import uncontended
    witnesses=[]
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);uncontended()
        original=cp.RawModule(path=str(D/'original.ptx')).get_function('unpack4')
        # Extra physical storage makes out-of-contract reads/writes diagnostic
        # without deliberately submitting an invalid GPU address.
        x=cp.asarray(np.array([1,2,4,8,16,32,64,128],dtype=np.uint32))
        for name in ['wrong-multiply','wrong-input-index','wrong-tail-guard']:
            bad=cp.RawModule(path=str(W/name/'kernel.ptx')).get_function('unpack4')
            y=cp.full(32,0xa5a5a5a5,dtype=cp.uint32)
            z=cp.full_like(y,0xa5a5a5a5)
            original((1,),(32,),(x,y,np.uint32(16)))
            bad((1,),(32,),(x,z,np.uint32(16)))
            a,b=y.get(),z.get();diff=np.flatnonzero(a!=b)
            assert len(diff),name
            i=int(diff[0]);witnesses.append(dict(case=name,output_word=i,
                original=int(a[i]),mutant=int(b[i]),n=16,
                mutant_sha256=sha((W/name/'kernel.ptx').read_bytes())))
            uncontended()
    (D/'results/negative-gpu-witnesses.json').write_text(json.dumps(witnesses,indent=2)+'\n')

if __name__=='__main__':main()
