"""Freeze untouched upstream extraction before authoring candidate PTX."""
from pathlib import Path
import hashlib,json,shutil,subprocess
D=Path(__file__).resolve().parent
S=Path('/mnt/scratch/e5r-oss-ptx/screen/catboost-extract')
R=S.parent/'catboost'
ids=['zero_partitions','reverse','zero_segments','fill_query_end_mask','compute_group_ids']
rows={r['id']:r for r in json.loads((S/'candidates.json').read_text())}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ids:
 d=D/name;d.mkdir(exist_ok=True);r=rows[name];src=S/(name+'-no-unused-cub.cu')
 shutil.copy(src,d/'original.cu')
 shutil.copy(R/r['source'],d/'upstream.cu')
 cmd=['nvcc','-ptx','-O3','-DNDEBUG','-std=c++17','-arch=sm_86','--threads','2','--expt-extended-lambda','--expt-relaxed-constexpr',str(d/'original.cu'),'-o',str(d/'original.ptx')]
 res=subprocess.run(cmd,capture_output=True,text=True);(d/'build.log').write_text(res.stdout+res.stderr);res.check_returncode()
 assert (d/'original.ptx').read_bytes()==(S/(name+'-no-unused-cub.ptx')).read_bytes()
 r.update(phase='source_build_frozen',optimization_attempt=False,freeze={'files':{p.name:sha(p) for p in [d/'original.cu',d/'original.ptx',d/'upstream.cu']},'command':cmd,'compiler':subprocess.check_output(['nvcc','--version'],text=True),'normal_path_runtime_check':False,'adaptation':'Exact unchanged kernel body extracted; upstream host includes replaced by CUDA/stdint typedefs/struct and explicit instantiation. Unused CUB include omitted; prior screen proves emitted entry byte identity. Full normal CatBoost TU runtime equivalence remains unvalidated.'})
 (d/'freeze.json').write_text(json.dumps(r,indent=2)+'\n')
shutil.copy(R/'LICENSE',D/'LICENSE.catboost')
