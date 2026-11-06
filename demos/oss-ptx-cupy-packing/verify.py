"""Verify frozen source/PTX/edit/native bindings and any bound GPU datasets."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((D/'freeze.json').read_text());assert h(D/'packing.py')==f['source_sha256']
for row in f['kernels']:
 p=D/row['id'].split('/')[1]
 for name,value in row['hashes'].items():assert h(p/name)==value,(p,name)
 e=json.loads((p/'edit.json').read_text());assert h(p/'edited.ptx')==e['sha256']
for result in D.glob('results-*.json'):
 data=json.loads(result.read_text())
 assert data['cases']>0
 for name,value in data['hashes'].items():assert h(D/name)==value,(result,name)
print('Frozen and measured artifact hashes match; strict proof NOT accepted.')
