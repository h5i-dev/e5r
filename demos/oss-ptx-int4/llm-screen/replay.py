#!/usr/bin/env python3
"""Rebuild complete translation units, serially, without launching GPU work."""
import argparse
import json
import pathlib
import shlex
import subprocess


def run(args, log=None, cwd=None):
    if log:
        with log.open('w') as stream:
            subprocess.run(args, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT, check=True)
    else:
        subprocess.run(args, cwd=cwd, check=True)


def clone(root, name, url, pin):
    dest = root / name
    if not dest.exists():
        run(['git', 'clone', '--no-checkout', '--filter=blob:none', url, str(dest)])
    run(['git', '-C', str(dest), 'checkout', '--detach', pin])
    actual = subprocess.check_output(['git', '-C', str(dest), 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == pin
    return dest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scratch', type=pathlib.Path, required=True)
    ap.add_argument('--nvcc', default='/usr/local/cuda/bin/nvcc')
    ap.add_argument('--nvdisasm', required=True)
    opts = ap.parse_args()
    root = opts.scratch.resolve()
    root.mkdir(parents=True, exist_ok=True)
    here = pathlib.Path(__file__).resolve().parent
    llama = clone(root, 'llama.cpp', 'https://github.com/ggml-org/llama.cpp.git',
                  '67107ac34f62882d8b53ea41ad68010ea635b9be')
    marlin = clone(root, 'marlin', 'https://github.com/IST-DASLab/marlin.git',
                   '1f25790bdd49fba53106164a24666dade68d7c90')
    build = root / 'llama-build'
    run(['cmake', '-S', str(llama), '-B', str(build), '-DCMAKE_BUILD_TYPE=Release',
         '-DGGML_CUDA=ON', '-DCMAKE_CUDA_ARCHITECTURES=86',
         '-DCMAKE_EXPORT_COMPILE_COMMANDS=ON', '-DLLAMA_BUILD_TESTS=OFF',
         '-DLLAMA_BUILD_EXAMPLES=OFF', '-DLLAMA_BUILD_TOOLS=OFF',
         '-DCMAKE_CUDA_COMPILER=' + opts.nvcc], root / 'configure.log')
    entry = next(x for x in json.loads((build / 'compile_commands.json').read_text())
                 if x['file'].endswith('/convert.cu'))
    source = llama / 'ggml/src/ggml-cuda'
    adapt = root / 'adapt'
    adapt.mkdir(exist_ok=True)
    (adapt / 'convert.cu').write_bytes((source / 'convert.cu').read_bytes())
    (adapt / 'dequantize.cuh').write_bytes((source / 'dequantize.cuh').read_bytes())
    run(['patch', str(adapt / 'dequantize.cuh'), str(here / 'llama-intrinsic.patch')])
    inline = root / 'adapt-inline'
    inline.mkdir(exist_ok=True)
    (inline / 'convert.cu').write_bytes((source / 'convert.cu').read_bytes())
    (inline / 'dequantize.cuh').write_bytes((source / 'dequantize.cuh').read_bytes())
    run(['patch', str(inline / 'dequantize.cuh'), str(here / 'llama-inline.patch')])
    plain = root / 'marlin_plain.cu'
    plain.write_bytes((marlin / 'marlin/marlin_cuda_kernel.cu').read_bytes())
    run(['patch', str(plain), str(here / 'marlin-plain.patch')])
    for variant in ['llama', 'llama-intrinsic', 'llama-inline', 'marlin', 'marlin-plain']:
        out = root / 'artifacts' / variant
        out.mkdir(parents=True, exist_ok=True)
        if variant.startswith('llama'):
            args = shlex.split(entry['command'])
            args[args.index('-o') + 1] = str(out / 'convert.o')
            if variant in ['llama-intrinsic', 'llama-inline']:
                modified = inline if variant.endswith('inline') else adapt
                args[args.index(str(source / 'convert.cu'))] = str(modified / 'convert.cu')
                args += ['-I' + str(source)]
        else:
            src = plain if variant.endswith('plain') else marlin / 'marlin/marlin_cuda_kernel.cu'
            args = [opts.nvcc, '-O3', '-std=c++17', '--expt-relaxed-constexpr',
                    '-arch=sm_86', '-c', str(src), '-o', str(out / 'marlin.o')]
        args += ['--keep', '--keep-dir', str(out), '-Xptxas=-v']
        (out / 'command.json').write_text(json.dumps(args, indent=2) + '\n')
        run(args, out / 'build.log', cwd=entry['directory'])
        cubin = next(out.glob('*.cubin'))
        run([opts.nvdisasm, '-c', str(cubin)], out / 'kernel.sass')


if __name__ == '__main__':
    main()
