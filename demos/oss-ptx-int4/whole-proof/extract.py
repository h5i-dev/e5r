#!/usr/bin/env python3
"""Exact-entry correspondence and current admission status, CPU only.
Does not rewrite or overwrite any published FP4/sign artifacts.
"""
import gzip,hashlib,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
OUT=Path('/mnt/scratch/e5r-oss-ptx/int4/whole-proof/entries');OUT.mkdir(parents=True,exist_ok=True)
PUBLISHED=HERE.parent/'fp4-sign'
BASE=HERE.parent/'bitsandbytes-screen'
SYMBOL='_Z20kDequantizeBlockwiseIfLi512ELi64ELi8ELi1EEvPfPhS0_PT_ii'
sha=lambda b:hashlib.sha256(b).hexdigest()
freeze=json.loads((PUBLISHED/'build.json').read_text())
rows=[]
for name in ['original','edited']:
 full=gzip.decompress((PUBLISHED/'evidence'/(name+'.ptx.gz')).read_bytes())
 assert sha(full)==freeze['artifacts'][name]['ptx_sha256']
 assert full.isascii()
 text=full.decode();a=text.index('.visible .entry '+SYMBOL);b=text.index('\n}',a)+2
 # Preserve the existing original extraction's entire header/global declarations.
 existing=(BASE/'fp4-fp32.ptx').read_bytes();prefix=existing[:existing.index(b'.visible .entry ')]
 declarations=[line for line in prefix.splitlines() if line.startswith(b'.global ')]
 assert declarations and all(text.splitlines().count(line.decode())==1 for line in declarations)
 entry=prefix+full[a:b]+b'\n'
 if name=='original':assert entry==existing
 expected=json.loads((PUBLISHED/'proof-status.json').read_text())['exports']['entry-'+name]['sha256']
 assert sha(entry)==expected
 path=OUT/(name+'.ptx');path.write_bytes(entry)
 exe=Path(os.environ.get('E5R_VERIFY','/mnt/scratch/e5r-oss-ptx/cargo/release/e5r'))
 result=subprocess.run([str(exe),'ptx','export',str(path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 (OUT/(name+'.lean')).write_bytes(result.stdout)
 (OUT/(name+'.log')).write_bytes(result.stderr)
 rows.append({'variant':name,'full_sha256':sha(full),'entry_sha256':sha(entry),'global_declarations':len(declarations),'byte_correspondence':'entire body and all original module globals; existing frozen extraction hash unchanged','exporter_sha256':sha(exe.read_bytes()),'export_returncode':result.returncode,'error':result.stderr.decode().strip()})
print(json.dumps({'stage':'precise admission status, not whole-kernel acceptance','rows':rows},indent=2))
