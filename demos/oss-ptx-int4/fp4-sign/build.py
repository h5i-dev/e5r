#!/usr/bin/env python3
"""Direct PTX edit plus separate full-TU CUDA bitcast control. CPU only."""
import collections, gzip, hashlib, json, os, re, shutil, subprocess
from pathlib import Path
HERE = Path(__file__).resolve().parent
SCREEN = HERE.parent / 'bitsandbytes-screen'
SCRATCH = Path(os.environ.get('FP4_SCRATCH', '/mnt/scratch/e5r-oss-ptx/int4/fp4-sign'))
UP = Path('/mnt/scratch/e5r-oss-ptx/int4/bitsandbytes/upstream')
TOOLS = Path('/mnt/scratch/e5r-ptx-demo/tools')
NVCC = '/usr/local/cuda/bin/nvcc'
PTXAS = '/usr/local/cuda/bin/ptxas'
DUMP = str(TOOLS / 'cuda_cuobjdump-linux-x86_64-13.2.51-archive/bin/cuobjdump')
os.environ['PATH'] = str(TOOLS / 'cuda_nvdisasm-linux-x86_64-13.2.51-archive/bin') + ':' + os.environ['PATH']
def sha(b): return hashlib.sha256(b).hexdigest()
def run(cmd, cwd=None):
    p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode: raise RuntimeError((cmd, p.stdout.decode()))
    return p.stdout

def edit(text):
    # Each of the 16 sign chains converts 0 or 2 to float, subtracts
    # it from 1, then multiplies one of eight fixed nonnegative values.
    chains = list(re.finditer(r'cvt.rn.f32.u16\s+(%f\d+), (%rs\d+);', text))
    assert len(chains) == 16
    text = text.replace('.reg .pred', '.reg .b32 %sign<16>, %mag<16>;\n\t.reg .pred', 1)
    for i, m in enumerate(chains):
        f, rs = m.groups()
        sub = re.search(r'sub.ftz.f32\s+(%f\d+), (%f\d+), '+f+r';', text)
        assert sub
        sign = sub.group(1)
        one = re.search(r'mov.f32\s+'+sub.group(2)+r', 0f3F800000;', text)
        assert one
        mul = re.search(r'mul.ftz.f32\s+(%f\d+), (%f\d+), '+sign+r';', text)
        assert mul
        dst, mag = mul.groups()
        if i % 2 == 0:
            chain = re.search(r'shr.u16\s+(%rs\d+), (%rs\d+), 6;\n\s*and.b16\s+'+rs+r', \1, 2;', text)
            shift = 24
        else:
            chain = re.search(r'and.b16\s+(%rs\d+), (%rs\d+), 8;\n\s*shr.u16\s+'+rs+r', \1, 2;', text)
            shift = 28
        assert chain
        byte = chain.group(2)
        text = text.replace(chain.group(0), '', 1)
        text = text.replace(m.group(0), f'cvt.u32.u16 %sign{i}, {byte};\n\tshl.b32 %sign{i}, %sign{i}, {shift};\n\tand.b32 %sign{i}, %sign{i}, 0x80000000;', 1)
        text = text.replace(sub.group(0), '', 1)
        text = text.replace(mul.group(0), f'mov.b32 %mag{i}, {mag};\n\tor.b32 %mag{i}, %mag{i}, %sign{i};\n\tmov.b32 {dst}, %mag{i};', 1)
    return text

def main():
    SCRATCH.mkdir(parents=True, exist_ok=True)
    evidence = HERE / 'evidence'; evidence.mkdir(exist_ok=True)
    frozen = json.loads((SCREEN / 'result.json').read_text())
    assert run(['git', 'rev-parse', 'HEAD'], UP).decode().strip() == frozen['commit']
    for p, h in frozen['source_hashes'].items(): assert sha((UP/p).read_bytes()) == h
    base = UP.parent / 'kernels.ptx'
    assert sha(base.read_bytes()) == frozen['full_tu_ptx_sha256']
    # Freeze source (including license) and ordinary full-TU emission before edits.
    (evidence/'source.tar.gz').write_bytes(run(['git', 'archive', '--format=tar.gz', 'HEAD'], UP))
    (evidence/'original.ptx.gz').write_bytes(gzip.compress(base.read_bytes(), mtime=0))
    control = SCRATCH/'control'; control.mkdir(exist_ok=True)
    shutil.copytree(UP/'csrc', control/'csrc', dirs_exist_ok=True)
    source = (UP/'csrc/kernels.cu').read_text()
    old = 'float sign = 1.0f - 2 * ((val & 0b1000) >> 3);\n    return fp4_dequantization_lut[val & 0b111] * sign;'
    new = 'unsigned int magnitude = __float_as_uint(fp4_dequantization_lut[val & 0b111]);\n    return __uint_as_float(magnitude | (static_cast<unsigned int>(val & 8) << 28));'
    assert source.count(old) == 1
    (control/'csrc/kernels.cu').write_text(source.replace(old,new))
    patch = subprocess.run(['diff','-u','--label','a/csrc/kernels.cu','--label','b/csrc/kernels.cu',str(UP/'csrc/kernels.cu'),str(control/'csrc/kernels.cu')],stdout=subprocess.PIPE).stdout
    (HERE/'cuda-bitcast.patch').write_bytes(patch)
    cmd = [NVCC,'-std=c++17','-O3','-DNDEBUG','--use_fast_math','-arch=sm_86','--threads','1','-ptx','-I','csrc','csrc/kernels.cu','-o',str(SCRATCH/'cuda.ptx')]
    if not os.environ.get('FP4_REUSE_CONTROL'):
        (evidence/'cuda-nvcc.log').write_bytes(run(cmd,control))
    original = base.read_text(); edited = original
    variants = frozen['variants']; fp4 = [v for v in variants if v['variant'].startswith('fp4-')]
    for v in fp4:
        symbol = v['symbol']; start = edited.index('.visible .entry '+symbol); end = edited.index('\n}', start)+2
        edited = edited[:start]+edit(edited[start:end])+edited[end:]
    (SCRATCH/'edited.ptx').write_text(edited)
    (evidence/'edited.ptx.gz').write_bytes(gzip.compress(edited.encode(),mtime=0))
    report = {'commit':frozen['commit'],'cuda_command':cmd,'changes':'16 sign chains in each of 3 FP4 output variants; all other full-TU entries unchanged','accepted_proof':False,'rows':[],'artifacts':{}}
    for name, ptx in [('original',base),('edited',SCRATCH/'edited.ptx'),('cuda',SCRATCH/'cuda.ptx')]:
        data=ptx.read_bytes(); (evidence/(name+'.ptx.gz')).write_bytes(gzip.compress(data,mtime=0))
        cubin=SCRATCH/(name+'.cubin'); cmd=[PTXAS,'-O3','-arch=sm_86','-v',str(ptx),'-o',str(cubin)]
        if name == 'edited' or not os.environ.get('FP4_REUSE_CONTROL'):
            log=run(cmd); (evidence/(name+'-ptxas.log')).write_bytes(log)
        (evidence/(name+'.cubin.gz')).write_bytes(gzip.compress(cubin.read_bytes(),mtime=0))
        report['artifacts'][name]={'ptx_sha256':sha(data),'cubin_sha256':sha(cubin.read_bytes()),'ptxas_command':cmd}
        for v in fp4:
            symbol=v['symbol']; label=name+'-'+v['variant']
            sass=run([DUMP,'--dump-sass','--function',symbol,str(cubin)]).decode()
            resources=run([DUMP,'--dump-resource-usage','--function',symbol,str(cubin)]).decode()
            (evidence/(label+'.sass')).write_text(sass); (evidence/(label+'.resources')).write_text(resources)
            counts=collections.Counter(re.findall(r'/\*[0-9a-f]+\*/\s+(?:@!?P\d+\s+)?([A-Z][A-Z0-9_.]*)',sass))
            report['rows'].append({'implementation':name,'variant':v['variant'],'symbol':symbol,'static_sass':sum(counts.values()),'non_nop_sass':sum(counts.values())-counts['NOP'],'opcodes':dict(counts),'resources':resources.strip()})
    (HERE/'build.json').write_text(json.dumps(report,indent=2)+'\n')
    print([(r['implementation'],r['variant'],r['static_sass'],r['non_nop_sass']) for r in report['rows']],flush=True)
if __name__=='__main__': main()
