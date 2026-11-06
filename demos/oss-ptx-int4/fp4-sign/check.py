#!/usr/bin/env python3
"""CPU-only artifact replay, local Lean lemma and meaningful semantic negative."""
import gzip, hashlib, json, os, re, resource, signal, subprocess
from pathlib import Path
import build
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
SCRATCH=build.SCRATCH/'proof'; SCRATCH.mkdir(parents=True,exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
report=json.loads((HERE/'build.json').read_text())
evidence=HERE/'evidence'
original=gzip.decompress((evidence/'original.ptx.gz').read_bytes()).decode()
edited=gzip.decompress((evidence/'edited.ptx.gz').read_bytes()).decode()
assert sha(original.encode())==report['artifacts']['original']['ptx_sha256']
assert sha(edited.encode())==report['artifacts']['edited']['ptx_sha256']
regenerated=original
for row in report['rows']:
 if row['implementation']!='original':continue
 symbol=row['symbol']; a=regenerated.index('.visible .entry '+symbol); b=regenerated.index('\n}',a)+2
 regenerated=regenerated[:a]+build.edit(regenerated[a:b])+regenerated[b:]
assert regenerated==edited
# Connect the finite-table lemma to the exact bytes; no whole-kernel proof claim.
raw=re.search(r'fp4_dequantization_lut\[32\] = \{([^}]+)\}',original).group(1)
table=bytes(map(int,raw.split(',')))
import struct
bits=struct.unpack('<8I',table)
lean=(HERE/'TableSign.lean').read_text()
assert [int(x,16) for x in re.findall(r'⟨\d, _⟩ => (0x[0-9a-f]+)',lean)]==list(bits)
env=dict(os.environ,LEAN_NUM_THREADS='1')
# Invoke the pinned compiler directly; Lake's own runtime need not share its cap.
lean_binary=subprocess.check_output(['elan','which','lean'],cwd=ROOT/'verification/ptx',text=True).strip()
env['LEAN_PATH']=str(ROOT/'verification/ptx/.lake/build/lib/lean')
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(220,230))
def run_lean(path):
 cmd=[lean_binary,'-j1','-M2048',str(path)]
 process=subprocess.Popen(cmd,cwd=ROOT/'verification/ptx',env=env,
     stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
 try:
  output,_=process.communicate(timeout=240)
 except subprocess.TimeoutExpired:
  # Only this invocation's private process group is terminated on timeout.
  try: os.killpg(process.pid,signal.SIGKILL)
  except ProcessLookupError: pass
  output,_=process.communicate()
  raise RuntimeError('local Lean proof timed out: '+output.decode(errors='replace'))
 return subprocess.CompletedProcess(cmd,process.returncode,output)
p=run_lean(HERE/'TableSign.lean'); (evidence/'table-proof.log').write_bytes(p.stdout)
assert p.returncode==0,p.stdout.decode()
assert b'sorryAx' not in p.stdout
for deps in re.findall(rb'depends on axioms: \[([^]]*)\]',p.stdout):
 assert set(deps.decode().replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
# Rebind the candidate expression itself to a wrong sign bit. The proved
# counterexample reaches the FP semantics, rather than an artifact-hash failure.
negative=SCRATCH/'WrongSign.lean'
prefix = lean[:lean.index('-- Kernel reduction')].replace('0x80000000 else 0','0x40000000 else 0')
negative.write_text(prefix + """
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem wrong_sign_counterexample :
    fmul .f32 .rn true false (table ⟨0, by decide⟩) (originalSign true) ≠
      some (inserted ⟨0, by decide⟩ true) := by decide +kernel
#print axioms wrong_sign_counterexample
end FP4Sign
""")
p=run_lean(negative); (evidence/'table-semantic-negative.log').write_bytes(p.stdout)
assert p.returncode==0 and b'sorryAx' not in p.stdout,p.stdout.decode()
exports={}
entry_original=(HERE.parent/'bitsandbytes-screen/fp4-fp32.ptx').read_text()
entry_edited=build.edit(entry_original)
for name,text in [('original',original),('edited',edited),('entry-original',entry_original),('entry-edited',entry_edited)]:
 path=SCRATCH/(name+'.ptx'); path.write_text(text)
 cmd=['/mnt/scratch/e5r-oss-ptx/cargo/release/e5r','ptx','export',str(path)]
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (evidence/(name+'-export.log')).write_bytes(p.stdout)
 assert p.returncode!=0 and (b'unsupported module global declaration' in p.stdout or b"unexpected character '|'" in p.stdout)
 exports[name]={'command':cmd,'returncode':p.returncode,'sha256':sha(text.encode()),'error':p.stdout.decode().strip()}
out={'artifact_replay':'exact hashes and deterministic direct edit pass','table_bits':[hex(x) for x in bits],
 'local_lemma':'kernel-reduced decide +kernel; table_sign and scaled_sign; standard axioms only',
 'local_semantic_negative':'kernel-proved zero-table counterexample to wrong bit30 insertion after candidate expression replacement',
 'exports':exports,'accepted_whole_kernel_proof':False,
 'remaining':['full TU lexer rejects unrelated predicate | syntax; extracted exact FP4 entries reject initialized global data','implicit rounding FP operations require explicit model justification','barrier/shared-memory execution and FP16/BF16 conversions need whole-kernel proof','no whole-kernel hash-rebound semantic negative admitted through parser']}
(HERE/'proof-status.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
