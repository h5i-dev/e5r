"""Hash-rebound semantic proof mutation; strict checker must reject actual VCs."""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile
D=Path(__file__).resolve().parent
S=Path(os.environ.get('E5R_OSS_SCRATCH','/mnt/scratch/e5r-oss-ptx'))
original=(D/'edited.ptx').read_text()
assert original.count('st.global.u32 \t[%rd9], %r9;')==1
# r8 is initialized to zero; make the stored value1, preserving pointers/tails.
needle='mov.u32 \t%r9, 0;'
assert original.count(needle)==1
mutant=original.replace(needle,'mov.u32 \t%r9, 1;')
with tempfile.TemporaryDirectory(dir=S/'tmp') as tmp:
 t=Path(tmp)
 for name in ('original.ptx','equivalence.json'):(t/name).write_bytes((D/name).read_bytes())
 (t/'edited.ptx').write_text(mutant)
 proof=(D/'equivalence.lean').read_text().replace(hashlib.sha256(original.encode()).hexdigest(),hashlib.sha256(mutant.encode()).hexdigest())
 (t/'equivalence.lean').write_text(proof)
 cmd=[str(S/'cargo/release/e5r'),'ptx','check',str(t/'edited.ptx'),'--spec',str(t/'equivalence.json'),'--proof',str(t/'equivalence.lean'),'--out',str(t/'result.json'),'--timeout','120','--memory-mb','3072','--no-search']
 r=subprocess.run(cmd,text=True,capture_output=True)
 result=json.loads((t/'result.json').read_text())
 assert r.returncode==3 and not result.get('proof',{}).get('accepted',False),(r.returncode,result)
 assert 'hash mismatch' not in json.dumps(result).lower()
 (D/'negative.json').write_text(json.dumps(dict(exit_code=r.returncode,mutant_sha256=hashlib.sha256(mutant.encode()).hexdigest(),hash_rebound=True,result=result),indent=2)+'\n')
 (D/'negative.log').write_text(r.stdout+r.stderr)
 print('Hash-rebound store-value mutant rejected on semantic proof obligations.')
