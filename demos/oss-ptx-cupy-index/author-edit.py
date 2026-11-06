"""Direct PTX edits, never candidate CUDA compilation."""
from pathlib import Path
import re,json,hashlib
D=Path(__file__).resolve().parent
edits={'tri':('u32','%r1','cupy_tri_param_0',256),'resize':('u64','%rd20','cupy_resize_param_1',256),'putmask':('u64',None,'cupy_putmask_kernel_param_2',256),'flatiter_setitem_slice':('u64',None,'cupy_flatiter_setitem_slice_param_0+8',256),'flatiter_getitem_slice':('u64','%rd21','cupy_flatiter_getitem_slice_param_2',1)}
for name,(typ,reg,param,value) in edits.items():
 p=D/name;s=(p/'original.ptx').read_text()
 pattern=r'ld.param.'+typ+r'\s+(%\w+), \['+re.escape(param)+r'\];'
 matches=list(re.finditer(pattern,s));assert len(matches)==1,(name,pattern)
 m=matches[0];dest=m.group(1);s=s[:m.start()]+f'mov.{typ} {dest}, {value};'+s[m.end():]
 # Replace emitted dynamic division CFG directly, retaining frozen original.
 if name!='flatiter_getitem_slice':
  first=s.index('\tor.b64',s.index('$L__BB0_2:'))
  label='$L__BB0_6:' if name=='putmask' else '$L__BB0_5:'
  last=s.index(label,first)+len(label)
  body={'tri':'\tshr.u64 %rd36, %rd35, 8;\n\tand.b64 %rd37, %rd35, 255;',
        'resize':'\tand.b64 %rd39, %rd38, 255;',
        'putmask':'\tand.b64 %rd54, %rd53, 255;',
        'flatiter_setitem_slice':'\tand.b64 %rd41, %rd40, 255;'}[name]
  s=s[:first]+body+s[last:]
 else:
  s=s.replace('mul.lo.s64 \t%rd32, %rd21, %rd42;', 'mov.u64 %rd32, %rd42;')
  s=s.replace('mul.lo.s64 \t%rd36, %rd21, %rd1;', 'mov.u64 %rd36, %rd1;')
 (p/'edited.ptx').write_text(s)
 (p/'edit.json').write_text(json.dumps(dict(kind='direct_ptx_parameter_specialization',parameter=param,value=value,domain='Exact stated parameter value; contiguous int32 arrays, disjoint input/output except putmask destination; nonnegative iteration count <2^29, valid 1D covering launch. Full memory/race/frame/termination proof pending.',sha256=hashlib.sha256(s.encode()).hexdigest(),proof_accepted=False),indent=2)+'\n')
 print(name,dest,param,value)
