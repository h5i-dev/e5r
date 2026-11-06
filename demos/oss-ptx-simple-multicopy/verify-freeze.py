"""Artifact, proof manifest and measurement binding checks (not a proof)."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((D/'freeze.json').read_text())
for path,h in f['hashes'].items():assert sha(D/path)==h,path
spec=json.loads((D/'equivalence.json').read_text())
assert spec['original_sha256']==sha(D/'original.ptx')
proof=(D/'equivalence.lean').read_text()
assert 'ptx='+sha(D/'edited.ptx') in proof
assert 'spec='+sha(D/'equivalence.json') in proof
for name in ('correctness','performance'):
 r=json.loads((D/f'results/{name}.json').read_text())
 for k,h in r['metadata']['ptx_sha256'].items():assert sha(D/f'{k}.ptx')==h,(name,k)
p=json.loads((D/'results/proof.json').read_text())
assert p['verdict']=='proved' and p['proof']['accepted'] is True,p['reasons']
assert p['input']['ptx']['sha256']==sha(D/'edited.ptx')
assert p['input']['spec']['sha256']==sha(D/'equivalence.json')
assert p['input']['original_ptx']['sha256']==sha(D/'original.ptx')
assert p['proof']['sha256']==sha(D/'equivalence.lean')
assert set(p['theorem']['axioms'])<= {'propext','Quot.sound','Classical.choice'}
assert json.loads((D/'results/negative-controls.json').read_text())['all_refused']
assert all(x['mismatch'] for x in json.loads((D/'results/negative-gpu-witnesses.json').read_text())['witnesses'])
for f,h in json.loads((D/'artifacts.json').read_text())['sha256'].items():assert sha(D/f)==h,f
print('frozen source/PTX, accepted proof and raw measurements are bound; negatives refused')
