#!/usr/bin/env python3
"""CPU-only exact-byte model-admission inventory; no proof/performance claims."""
import gzip,hashlib,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;BASE=HERE.parent
OUT=Path('/mnt/scratch/e5r-oss-ptx/int4/whole-proof/variant-inventory');OUT.mkdir(parents=True,exist_ok=True)
E5R=Path(os.environ.get('E5R_VERIFY','/mnt/scratch/e5r-oss-ptx/cargo/release/e5r'))
build=json.loads((BASE/'fp4-sign/build.json').read_text())
original=(BASE/'bitsandbytes-screen/fp4-fp32.ptx').read_bytes();prefix=original[:original.index(b'.visible .entry ')]
rows=[]
for variant in ['original','edited']:
 full=gzip.decompress((BASE/'fp4-sign/evidence'/(variant+'.ptx.gz')).read_bytes())
 assert hashlib.sha256(full).hexdigest()==build['artifacts'][variant]['ptx_sha256']
 for dtype,ty,ptr in [('fp32','f','S0_'),('fp16','6__half','S1_'),('bf16','13__nv_bfloat16','S1_')]:
  symbol=f'_Z20kDequantizeBlockwiseI{ty}Li512ELi64ELi8ELi1EEvPfPh{ptr}PT_ii'
  a=full.index(('.visible .entry '+symbol).encode());b=full.index(b'\n}',a)+2
  entry=prefix+full[a:b]+b'\n';path=OUT/(variant+'-'+dtype+'.ptx');path.write_bytes(entry)
  p=subprocess.run([str(E5R),'ptx','export',str(path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
  rows.append({'variant':variant,'dtype':dtype,'entry_sha256':hashlib.sha256(entry).hexdigest(),'globals':67,'exact_body_correspondence':True,'export_returncode':p.returncode,'error':p.stderr.decode().strip(),'whole_kernel_accepted':False})
 for dtype in ['full-TU']:
  path=OUT/(variant+'-full.ptx');path.write_bytes(full)
  p=subprocess.run([str(E5R),'ptx','export',str(path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
  rows.append({'variant':variant,'dtype':dtype,'entry_sha256':hashlib.sha256(full).hexdigest(),'export_returncode':p.returncode,'error':p.stderr.decode().strip(),'whole_kernel_accepted':False})
report={'scope':'model admission only, exact-byte extraction not baseline substitution','rows':rows}
(OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
