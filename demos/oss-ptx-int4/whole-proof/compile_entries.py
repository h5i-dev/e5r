#!/usr/bin/env python3
"""Compile the unchanged exact FP32 entry exports and actual-table lemmas.
Does not constitute official checker whole-kernel acceptance.
"""
import hashlib,json,os,resource,signal,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
OUT=Path('/mnt/scratch/e5r-oss-ptx/int4/whole-proof/entries')
E5R=Path(os.environ.get('E5R_VERIFY','/mnt/scratch/e5r-oss-ptx/cargo/release/e5r'))
TOOL=ROOT/'verification/ptx';LEAN=subprocess.check_output(['elan','which','lean'],cwd=TOOL,text=True).strip()
env=dict(os.environ,LEAN_PATH=str(TOOL/'.lake/build/lib/lean')+':'+str(OUT),LEAN_NUM_THREADS='1')
def run(cmd):
 def limits():resource.setrlimit(resource.RLIMIT_CPU,(240,250))
 p=subprocess.Popen(list(map(str,cmd)),env=env,cwd=TOOL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True,preexec_fn=limits)
 try:o,e=p.communicate(timeout=300)
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.communicate();raise
 if p.returncode:raise RuntimeError((cmd,p.returncode,o.decode()[-4000:],e.decode()[-4000:]))
 return o
rows=[]
for variant,namespace in [('original','FP4Original'),('edited','FP4Edited')]:
 ptx=OUT/(variant+'.ptx');dest=OUT/(namespace+'.lean')
 dest.write_bytes(run([E5R,'ptx','export','--namespace',namespace,ptx]))
 run([LEAN,'-j1','-M2048','-R',OUT,dest,'-o',OUT/(namespace+'.olean')])
 rows.append({'variant':variant,'namespace':namespace,'entry_sha256':hashlib.sha256(ptx.read_bytes()).hexdigest(),'export_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'status':'whole entry AST compiled, not equivalence accepted'})
# Reuse the immutable earlier local lemma source, as an imported checked module.
run([LEAN,'-j1','-M2048','-R',HERE.parent/'fp4-sign',HERE.parent/'fp4-sign/TableSign.lean','-o',OUT/'TableSign.olean'])
log=run([LEAN,'-j1','-M2048','-R',HERE,HERE/'ExactTable.lean','-o',OUT/'ExactTable.olean'])
(OUT/'exact-table.log').write_bytes(log)
log+=run([LEAN,'-j1','-M2048','-R',HERE,HERE/'FiniteScale.lean','-o',OUT/'FiniteScale.olean'])
log+=run([LEAN,'-j1','-M2048','-R',HERE,HERE/'FP32Domain.lean','-o',OUT/'FP32Domain.olean'])
log+=run([LEAN,'-j1','-M2048','-R',HERE,HERE/'SharedWarp.lean','-o',OUT/'SharedWarp.olean'])
replay=b''
for module in ['Ptx.Semantics.Warp','Ptx.Logic.WarpSchedule','Ptx.Examples.Warp','FP4Original','FP4Edited','TableSign','FiniteScale','ExactTable','FP32Domain','SharedWarp']:
 # Replay needs up to 3GiB; isolate modules to avoid retaining imported heaps.
 replay+=run([LEAN,'-j1','-M3072','--run',HERE/'ReplayPrerequisites.lean',module])
(OUT/'prerequisite-replay.jsonl').write_bytes(replay)
print(json.dumps({'scope':'exact entry AST and initialized-table bridge, not whole-kernel acceptance','rows':rows},indent=2));print(log.decode())
