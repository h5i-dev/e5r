#!/usr/bin/env python3
"""Compile actual model/checker modules serially with Lean heap/CPU/wall caps.
Updates OLean imports, never model source or checker policy. Native proofcheck
imports only Lean and must already be built using the pinned toolchain.
"""
import os,re,subprocess,sys,signal,resource,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]/'verification/ptx'
SCRATCH=Path(os.environ.get('FP4_PROOF_SCRATCH','/mnt/scratch/e5r-oss-ptx/int4/whole-proof'))
SCRATCH.mkdir(parents=True,exist_ok=True)
OUT=ROOT/'.lake/build/lib/lean'
LEAN=subprocess.check_output(['elan','which','lean'],cwd=ROOT,text=True).strip()
seen=set();order=[]
def visit(name):
 if name in seen:return
 seen.add(name);p=ROOT/(name.replace('.','/')+'.lean')
 if not p.exists():return
 for line in re.findall(r'^import\s+([^\n]+)',p.read_text(),re.M):
  for dep in line.split():visit(dep)
 order.append(name)
for name in ['Ptx','Ptx.Logic.RelationalPhases','Ptx.Examples.RelationalPhases','Checker.ProofCheck']:visit(name)
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(OUT))
record=[]
def limits():resource.setrlimit(resource.RLIMIT_CPU,(480,490))
for i,name in enumerate(order):
 path=ROOT/(name.replace('.','/')+'.lean');dest=OUT/(name.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 print(i+1,len(order),name,flush=True)
 p=subprocess.Popen([LEAN,'-j1','-M2048','-R',str(ROOT),str(path),'-o',str(dest)],cwd=ROOT,env=env,start_new_session=True,preexec_fn=limits)
 try:r=p.wait(timeout=600)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL);p.wait();raise
 if r:sys.exit(r)
 record.append({'module':name,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'olean_sha256':hashlib.sha256(dest.read_bytes()).hexdigest()})
(SCRATCH/'direct-build-modules.json').write_text(json.dumps(record,indent=2)+'\n')
print('all direct serial modules passed',flush=True)
