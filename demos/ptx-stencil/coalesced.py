"""New coalesced-ownership measurements, retaining all earlier raw results."""
from pathlib import Path
import fcntl
import hashlib
import json
import subprocess
import sys
import cupy as cp
import numpy as np
import experiment

D = Path(__file__).resolve().parent
PTX = ['original', 'striped', 'staged']
STEM = 'coalesced'
CUDA_SOURCES = ['coalesced.cu', 'matching.cu']
SCOPE = 'block-striped independent accumulators; rolling sums with shared staging/bar.sync; block<=512'


def functions():
    modules = {name: cp.RawModule(path=str(D / (name + '.ptx'))) for name in PTX}
    result = {name: mod.get_function('stencil17') for name, mod in modules.items()}
    mod = cp.RawModule(code=(D / 'coalesced.cu').read_text(), backend='nvcc', options=('-O3', '-arch=sm_86'))
    result['striped_cuda'] = mod.get_function('striped17')
    result['staged_cuda'] = mod.get_function('staged17')
    old = cp.RawModule(code=(D / 'matching.cu').read_text(), backend='nvcc', options=('-O3', '-arch=sm_86'))
    result['matching64_cuda'] = old.get_function('matching64')
    return result


def hashes():
    return {name: hashlib.sha256((D / (name + '.ptx')).read_bytes()).hexdigest() for name in PTX}


def test(independent_offsets=False):
    experiment.functions = functions
    result = experiment.test(independent_offsets=independent_offsets)
    result['ptx_sha256'] = hashes()
    result['cuda_sha256'] = {p: hashlib.sha256((D / p).read_bytes()).hexdigest()
                            for p in CUDA_SOURCES}
    result['scope'] = SCOPE
    (D / f'results/{STEM}-correctness.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


def bench():
    timing = experiment.timing
    timing.uncontended()
    funcs = functions()
    rng = np.random.default_rng(1717)
    rows = []
    for out in [32, 256, 4096, 65536, 1048576, 16777216, 134217728]:
        n = out // 4
        x = cp.asarray(rng.integers(0, 2**32, size=n+16, dtype=np.uint32))
        y = cp.empty(n, dtype=cp.uint32)
        wide = cp.concatenate([cp.zeros(1, dtype=cp.uint64), cp.cumsum(x, dtype=cp.uint64)])
        expected = (wide[17:] - wide[:-17]).astype(cp.uint32)
        for name, kernel in funcs.items():
            count = experiment.launch_items(name,n)
            for block in [128, 256, 512]:
                grid = (count+block-1)//block
                def run():
                    kernel((grid,), (block,), (x, y, np.uint32(n)))
                run()
                cp.testing.assert_array_equal(y, expected)
                for graph in ([True, False] if block == 256 else [True]):
                    result = timing.measure(run, graph)
                    rows.append(dict(output_bytes=out, name=name, block=block, grid=grid,
                                     graph=graph, logical_GBps=(x.nbytes+y.nbytes)/result['median_us']/1000,
                                     **result))
                    print(out, name, block, graph, round(result['median_us'], 4), flush=True)
        metadata = dict(ptx_sha256=hashes(),
                        cuda_sha256={p: hashlib.sha256((D/p).read_bytes()).hexdigest()
                                     for p in CUDA_SOURCES},
                        gpu=subprocess.check_output(['nvidia-smi', '--query-gpu=name,uuid,driver_version',
                                                     '--format=csv,noheader'], text=True).strip(),
                        cupy=cp.__version__, numpy=np.__version__,
                        nvcc=subprocess.check_output(['nvcc', '--version'], text=True),
                        lock='/mnt/scratch/e5r-gpu-benchmark.lock', foreign_processes_observed=False,
                        seed=1717, repeats=7, proof_status='experimental; no changed-candidate acceptance claimed')
        (D / f'results/{STEM}-performance.json').write_text(json.dumps(dict(metadata=metadata, rows=rows), indent=2) + '\n')


if __name__ == '__main__':
    with open('/mnt/scratch/e5r-gpu-benchmark.lock', 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        experiment.await_gpu_idle()
        if len(sys.argv) > 1 and sys.argv[1] == 'benchmark':
            bench()
        else:
            test()
