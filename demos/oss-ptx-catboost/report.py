from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
rows=[]
for p in sorted(D.glob('*/gpu.json')):
 d=p.parent;g=json.loads(p.read_text());f=json.loads((d/'freeze.json').read_text());e=json.loads((d/'edit.json').read_text())
 rows.append({'id':'catboost-'+d.name,'project':'CatBoost','repository':f['upstream_repository'],'commit':f['upstream_commit'],'source':f['source'],'function':f['function'],'line':f['function_line'],'license':'Apache-2.0','phase':'edited_gpu_timed_proof_pending','optimization_attempt':True,'completed_optimization_proof_attempt':False,'strict_proof_accepted':False,'normal_path_runtime_check':False,'hashes':g['hashes'],'artifacts':str(d.relative_to(D.parent.parent)),'gpu_cases':g['correctness_cases'],'timing_rows':len(g['rows']),'median_speedup':__import__('statistics').median(r['speedup_original_over_edited'] for r in g['rows']),'min_speedup':min(r['speedup_original_over_edited'] for r in g['rows']),'max_speedup':max(r['speedup_original_over_edited'] for r in g['rows']),'domain':e['domain'],'caveats':['Extracted unchanged upstream body; normal full TU runtime equivalence not validated','No meaningful speedup demonstrated','No accepted universal direct equivalence proof']})
for row in rows:
 d=D/row['id'].removeprefix('catboost-')
 proof=d/'proof-attempt.json'
 if proof.exists():
  v=json.loads(proof.read_text())
  bound=all(hashlib.sha256((d/name).read_bytes()).hexdigest()==v['input'][key]['sha256'] for name,key in [('original.ptx','original_ptx'),('edited.ptx','ptx'),('equivalence.json','spec')])
  bound=bound and hashlib.sha256((d/'equivalence.lean').read_bytes()).hexdigest()==v['proof']['sha256']
  accepted=bound and v.get('verdict')=='proved' and v.get('proof',{}).get('accepted',False)
  row.update(proof_attempt=True,strict_proof_accepted=accepted,phase='strict_direct_proof_accepted_normal_TU_pending' if accepted else 'proof_attempt_unaccepted')
  if accepted:row['caveats'].remove('No accepted universal direct equivalence proof')
(D/'ledger-rows.json').write_text(json.dumps(rows,indent=2)+'\n')
