#!/usr/bin/env python3
"""Semantic regression negative for the new warp release model.
Mutates only an isolated source copy, replacing warp release with CTA release.
Must reach and fail the universal other-thread frame theorem. This is not the
requested exact-hash FP4 whole-kernel semantic negative, still outstanding.
"""
import hashlib,json,os,resource,signal,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];MODEL=ROOT/'verification/ptx'
OUT=Path('/mnt/scratch/e5r-oss-ptx/int4/whole-proof/model-negative');OUT.mkdir(parents=True,exist_ok=True)
source=(MODEL/'Ptx/Semantics/Warp.lean').read_text()
old='ts := fun t => if id L t = w then (c.cfg.ts t).skip else c.cfg.ts t'
new='ts := fun t => if t.ctaid = w.ctaid then (c.cfg.ts t).skip else c.cfg.ts t'
assert source.count(old)==1
bad=source.replace(old,new)
path=OUT/'WarpBad.lean';path.write_text(bad)
lean=subprocess.check_output(['elan','which','lean'],cwd=MODEL,text=True).strip()
def limits():resource.setrlimit(resource.RLIMIT_CPU,(90,100))
p=subprocess.Popen([lean,'-j1','-M2048','-R',str(OUT),str(path),'-o',str(OUT/'WarpBad.olean')],cwd=MODEL,env=dict(os.environ,LEAN_PATH=str(MODEL/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1'),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
try:log=p.communicate(timeout=120)[0]
except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.communicate();raise
(OUT/'negative.log').write_bytes(log)
# Check the actual semantic proof failed, rather than accepting parse/import or
# source-hash rejection as a negative. Lean reports this exact theorem's line.
line=next(i for i,l in enumerate(bad.splitlines(),1) if l.startswith('theorem releaseWarp_other_thread'))
assert p.returncode!=0 and b'unsolved goals' in log
assert f'WarpBad.lean:{line+1}:'.encode() in log or f'WarpBad.lean:{line+2}:'.encode() in log,log.decode()[:2000]
assert b'outside : id L t' in log and b't.ctaid = w.ctaid' in log
report={'scope':'warp-model regression negative, NOT FP4 whole-kernel negative','mutation':'same-CTA threads incorrectly advanced by warp release','original_model_sha256':hashlib.sha256(source.encode()).hexdigest(),'mutated_model_sha256':hashlib.sha256(bad.encode()).hexdigest(),'result':'rejected at actual universal other-thread semantic frame proof','returncode':p.returncode}
(OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
