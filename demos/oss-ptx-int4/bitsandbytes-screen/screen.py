#!/usr/bin/env python3
"""Screen unchanged MIT bitsandbytes CUDA emission; no GPU execution."""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
SCRATCH = Path('/mnt/scratch/e5r-oss-ptx/int4/bitsandbytes')
PIN = 'a616886cacf86701514f0cb1d6be760f967481c0'
TOOLS = Path('/mnt/scratch/e5r-ptx-demo/tools')
NVCC = '/usr/local/cuda/bin/nvcc'
PTXAS = '/usr/local/cuda/bin/ptxas'
CUOBJDUMP = str(TOOLS / 'cuda_cuobjdump-linux-x86_64-13.2.51-archive/bin/cuobjdump')
os.environ['PATH'] = str(TOOLS / 'cuda_nvdisasm-linux-x86_64-13.2.51-archive/bin') + os.pathsep + os.environ['PATH']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(args, cwd=None):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f'{args}: {p.stdout}')
    return p.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reuse-ptx', action='store_true')
    args = parser.parse_args()
    upstream = SCRATCH / 'upstream'
    assert run(['git', 'rev-parse', 'HEAD'], upstream).strip() == PIN
    assert not run(['git', 'status', '--porcelain'], upstream).strip()
    flags = [NVCC, '-std=c++17', '-O3', '-DNDEBUG', '--use_fast_math',
             '-arch=sm_86', '--threads', '1', '-ptx', '-I', 'csrc',
             'csrc/kernels.cu', '-o', str(SCRATCH / 'kernels.ptx')]
    if not args.reuse_ptx:
        (HERE / 'nvcc.log').write_text(run(flags, upstream))
    text = (SCRATCH / 'kernels.ptx').read_text()
    commands = [flags]
    full_cubin = SCRATCH / 'kernels.cubin'
    cmd = [PTXAS, '-O3', '-arch=sm_86', '-v', str(SCRATCH / 'kernels.ptx'), '-o', str(full_cubin)]
    commands.append(cmd)
    log = run(cmd)
    (SCRATCH / 'full-ptxas.log').write_text(log)
    declarations = '\n'.join(re.findall(r'^\.global[^;]+;', text, re.M))
    entries = re.findall(r'^\.visible \.entry (_Z20kDequantizeBlockwise[^\s(]+)', text, re.M)
    selected = [s for s in entries if 'Li8ELi0E' not in s]
    assert len(selected) == 6
    result = []
    for symbol in selected:
        dtype = 'fp16' if 'I6__half' in symbol else 'bf16' if 'I13__nv_bfloat16' in symbol else 'fp32'
        quant = 'fp4' if 'Li8ELi1E' in symbol else 'nf4'
        label = f'{quant}-{dtype}'
        start = text.index('.visible .entry ' + symbol)
        end = text.index('\n}', start) + 2
        entry = text[start:end]
        (HERE / (label + '.ptx')).write_text('.version 9.2\n.target sm_86\n.address_size 64\n' + declarations + '\n' + entry + '\n')
        cmd = [CUOBJDUMP, '--dump-sass', '--function', symbol, str(full_cubin)]
        commands.append(cmd)
        sass = run(cmd)
        (HERE / (label + '.sass')).write_text(sass)
        cmd = [CUOBJDUMP, '--dump-resource-usage', '--function', symbol, str(full_cubin)]
        commands.append(cmd)
        resources = run(cmd)
        (HERE / (label + '.resources')).write_text(resources)
        section = re.search(r"ptxas info    : Compiling entry function '" + re.escape(symbol) + r"'[^\n]*\n(.*?)(?=ptxas info    : Compiling entry function|\Z)", log, re.S)
        assert section
        (HERE / (label + '.ptxas.log')).write_text(section.group(0))
        spills = re.search(r'(\d+) bytes stack frame, (\d+) bytes spill stores, (\d+) bytes spill loads', section.group(0))
        assert spills
        opcodes = collections.Counter(re.findall(r'/\*[0-9a-f]+\*/\s+(?:@!?P\d+\s+)?([A-Z][A-Z0-9_.]*)', sass))
        # Counts include predicated/tail/control paths and are static, not executed counts.
        resource_match = re.search(r'REG:(\d+) STACK:(\d+) SHARED:(\d+) LOCAL:(\d+)', resources)
        assert resource_match, resources
        result.append(dict(variant=label, symbol=symbol, entry_sha256=sha(entry.encode()),
                           ptx_sha256=sha((HERE / (label + '.ptx')).read_bytes()),
                           sass_sha256=sha(sass.encode()), static_sass_instructions=sum(opcodes.values()),
                           sass_opcodes=dict(sorted(opcodes.items())),
                           spill_store_bytes=int(spills.group(2)), spill_load_bytes=int(spills.group(3)),
                           resources=dict(zip(['registers', 'stack_bytes', 'shared_bytes', 'local_bytes'], map(int, resource_match.groups())))))
    source_paths = ['LICENSE', 'CMakeLists.txt', 'csrc/kernels.cu', 'csrc/kernels.cuh', 'csrc/ops.cu',
                    'csrc/common.cuh', 'csrc/compat.cuh', 'csrc/compat_device.cuh',
                    'csrc/pythonInterface.cpp', 'bitsandbytes/backends/cuda/ops.py', 'bitsandbytes/functional.py']
    source_hashes = {p: sha((upstream / p).read_bytes()) for p in source_paths}
    (HERE / 'LICENSE.bitsandbytes').write_bytes((upstream / 'LICENSE').read_bytes())
    report = dict(upstream='https://github.com/bitsandbytes-foundation/bitsandbytes', commit=PIN,
                  source_hashes=source_hashes, compiler=run([NVCC, '--version']),
                  disassembler=run([CUOBJDUMP, '--version']), commands=commands,
                  full_tu_ptx_sha256=sha(text.encode()), full_tu_cubin_sha256=sha(full_cubin.read_bytes()),
                  extraction='Each retained PTX entry is copied byte-for-byte from unchanged full kernels.cu emission. SASS/resources are from the full TU cubin, not the extracted module.',
                  gpu_executed=False, candidate_written=False, accepted_proof=False,
                  variants=result)
    (HERE / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps([dict(variant=x['variant'], instructions=x['static_sass_instructions'], resources=x['resources']) for x in result], indent=2))


if __name__ == '__main__':
    main()
