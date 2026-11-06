"""Competent matching CUDA comparators, separate from direct PTX candidates."""
from pathlib import Path
import subprocess
D=Path(__file__).resolve().parent
for d in D.iterdir():
 if not (d/'original.cu').exists():continue
 s=(d/'original.cu').read_text()
 if d.name=='reverse':s=s.replace('while (i < half)', 'if (i < half)')
 elif d.name=='zero_partitions':
  s=s.replace('while (i < partCount)', 'if (i < partCount)')
  s=s.replace('parts[i].Size = 0;\n            parts[i].Offset = 0;', 'if ((reinterpret_cast<uintptr_t>(parts+i)&7)==0) {\n                *reinterpret_cast<uint2*>(parts+i)=make_uint2(0,0);\n            } else { parts[i].Size=0; parts[i].Offset=0; }')
 elif d.name=='zero_segments':s=s.replace('const ui32* flags','const ui32* __restrict flags').replace('T* output','T* __restrict output')
 elif d.name=='fill_query_end_mask':s=s.replace('const ui32* qids, const ui32* docs, ui32 docCount, ui32* masks','const ui32* __restrict qids, const ui32* __restrict docs, ui32 docCount, ui32* __restrict masks')
 elif d.name=='compute_group_ids':s=s.replace('ui32 writeOffset =', 'if (qid >= qCount) return;\n        ui32 writeOffset =')
 (d/'tuned.cu').write_text(s)
 subprocess.run(['nvcc','-ptx','-O3','-DNDEBUG','-std=c++17','-arch=sm_86','--threads','2',str(d/'tuned.cu'),'-o',str(d/'tuned.ptx')],check=True)
