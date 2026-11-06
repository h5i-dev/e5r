"""Rebind hashes before semantic negative checks; never reuse stale evidence."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
D=Path(__file__).resolve().parent
W=Path(os.environ.get('E5R_OSS_SCRATCH','/mnt/scratch/e5r-oss-ptx'))/'negatives'
BIN=Path(os.environ.get('CARGO_TARGET_DIR',str(W.parent/'cargo')))/'release/e5r'
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    original=(D/'original.ptx').read_text();edited=(D/'edited.ptx').read_text()
    def change(s,a,b):
        t,n=re.subn(a,b,s);assert n==1,(a,n);return t
    bad_increment=change(edited,r'add.s32 %r23, %r22, 1;', 'add.s32 %r23, %r22, 2;')
    bad_tail=change(edited,r'setp.ge.s32', 'setp.gt.s32')
    bad_input=change(edited,r'cvta.to.global.u64\s+%rd5, %rd4;', 'cvta.to.global.u64 %rd5, %rd3;')
    bad_original=change(original,r'add.s32\s+%r23, %r22, 1;', 'add.s32 %r23, %r22, 2;')
    rows=[]
    for name,o,e,rebind in [('stale_candidate',original,bad_increment,False),
        ('wrong_increment_rebound',original,bad_increment,True),
        ('wrong_tail_rebound',original,bad_tail,True),
        ('wrong_input_rebound',original,bad_input,True),
        ('wrong_original_rebound',bad_original,edited,True)]:
        stage=W/name;stage.mkdir(parents=True,exist_ok=True)
        (stage/'original.ptx').write_text(o);(stage/'edited.ptx').write_text(e)
        spec=json.loads((D/'equivalence.json').read_text());spec['original_sha256']=sha(o.encode())
        spec_bytes=(json.dumps(spec,indent=2)+'\n').encode();(stage/'equivalence.json').write_bytes(spec_bytes)
        proof=(D/'equivalence.lean').read_text()
        if rebind:
            proof=re.sub(r'ptx=[0-9a-f]{64}', 'ptx='+sha(e.encode()),proof,count=1)
            proof=re.sub(r'spec=[0-9a-f]{64}', 'spec='+sha(spec_bytes),proof,count=1)
        (stage/'equivalence.lean').write_text(proof)
        out=D/'results'/f'negative-{name}.json'
        r=subprocess.run([str(BIN),'ptx','check',str(stage/'edited.ptx'),'--spec',str(stage/'equivalence.json'),
            '--proof',str(stage/'equivalence.lean'),'--keep',str(stage/'check'),'--timeout','180','--memory-mb','4096','--out',str(out)],capture_output=True,text=True,timeout=240)
        doc=json.loads(out.read_text())
        assert doc['verdict']=='unknown' and not doc.get('proof',{}).get('accepted',False),(name,doc,r.stdout,r.stderr)
        reason=' '.join(doc['reasons'])
        assert ('different ptx' in reason) if not rebind else ('does not compile' in reason),(name,reason)
        rows.append(dict(name=name,hashes_rebound=rebind,verdict=doc['verdict'],reason=reason))
        print(name,doc['verdict'],flush=True)
    (D/'results/negative-controls.json').write_text(json.dumps(dict(all_refused=True,rows=rows),indent=2)+'\n')

def gpu_witnesses():
    import fcntl
    import numpy as np
    import cupy as cp
    from gpu import uncontended
    witnesses=[]
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);uncontended()
        for name in ('wrong_increment_rebound','wrong_tail_rebound','wrong_input_rebound','wrong_original_rebound'):
            p=W/name/('original.ptx' if name=='wrong_original_rebound' else 'edited.ptx')
            mod=cp.RawModule(path=str(p));fn=mod.get_function('_Z9incKernelPiS_ii')
            x=cp.zeros(33,np.uint32);storage=cp.full(49,np.uint32(42));y=storage[:33]
            fn((2,),(32,),(y,x,np.int32(33),np.int32(5)))
            output=y.get();tail=int(storage[33].get())
            mismatch=not np.array_equal(output,np.ones(33,np.uint32)) or tail!=42
            assert mismatch,name
            witnesses.append(dict(name=name,ptx_sha256=sha(p.read_bytes()),expected_first=1,
                actual_first=int(output[0]),expected_tail=42,actual_tail=tail,mismatch=True))
            uncontended()
    (D/'results/negative-gpu-witnesses.json').write_text(json.dumps(dict(lock='/mnt/scratch/e5r-gpu-benchmark.lock',
        foreign_processes_observed=False,witnesses=witnesses),indent=2)+'\n')

if __name__=='__main__':
    if '--gpu-only' not in sys.argv:main()
    gpu_witnesses()

