#!/usr/bin/env python3
"""Correctness and timing. All GPU activity is inside the shared lock."""
import argparse
import contextlib
import fcntl
import hashlib
import json
import os
from pathlib import Path
import random
import statistics
import subprocess
import time

HERE = Path(__file__).resolve().parent
SHAPES = [0, 1, 31, 32, 255, 256, 257, 4096, 65536, 1048576, 4194304, 16777216]
LOCK = '/mnt/scratch/e5r-gpu-benchmark.lock'


def foreign_gpu():
    raw = subprocess.check_output(['nvidia-smi', '--query-compute-apps=pid,process_name,used_memory',
                                   '--format=csv,noheader'], text=True)
    return [s for s in raw.splitlines() if s.strip() and int(s.split(',')[0]) != os.getpid()]


def no_foreign():
    foreign = foreign_gpu()
    if foreign:
        raise RuntimeError('Foreign GPU compute processes; discard this run: ' + repr(foreign))


@contextlib.contextmanager
def exclusive_gpu(wait_seconds):
    with open(LOCK, 'a') as f:
        until = time.monotonic() + wait_seconds
        while True:
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                if not foreign_gpu():
                    break
                fcntl.flock(f, fcntl.LOCK_UN)
            except BlockingIOError:
                pass
            if time.monotonic() >= until:
                raise RuntimeError('GPU busy or shared benchmark lock held')
            print('Waiting for exclusive GPU and no foreign compute processes', flush=True)
            time.sleep(min(15, max(0, until - time.monotonic())))
        print('Acquired shared exclusive GPU lock; no foreign compute processes', flush=True)
        try:
            yield
            no_foreign()
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def run(args):
    # Imports/context creation deliberately occur after the lock is acquired.
    import numpy as np
    import cupy as cp
    def reference(host, mask):
        # Memory-layout definition, independent of candidate arithmetic.
        reversed_bytes = host.view(np.uint8).reshape(-1, 4)[:, ::-1].copy()
        return reversed_bytes.reshape(-1).view(np.uint32) ^ np.uint32(mask)

    rng = np.random.default_rng(20261105)
    order_rng = random.Random(20261105)
    stream = cp.cuda.Stream(non_blocking=True)
    candidate = cp.RawModule(path=str(HERE / 'endian_xor.ptx')).get_function('endian_xor')
    baseline = cp.RawModule(path=str(args.scratch / 'baseline.cubin'))
    cuda = baseline.get_function('fused_cuda')
    cuda_vec = baseline.get_function('fused_cuda_vec4')
    swap = baseline.get_function('swap_cuda')
    masks = [0, 0xffffffff, 0x01020304, 0x80000001, 0xa5a55a5a]
    # Includes asymmetric byte values, every single bit, sign bits, zeros and ones.
    adversarial = np.array([0, 0xffffffff, 0x01020304, 0x80000000, 0x00000080,
                            0x12345678, 0x00ff00ff, 0xff00ff00] + [1 << b for b in range(32)], np.uint32)
    sizes = sorted(set(SHAPES + [2, 3, 4, 5, 7, 8, 9, 33, 511, 512, 513, 1023, 1024, 1025, 65535, 65537]))
    correctness = []
    with stream:
        for n in sizes:
            no_foreign()
            host = rng.integers(0, 2**32, n, dtype=np.uint32)
            host[:min(n, len(adversarial))] = adversarial[:min(n, len(adversarial))]
            # Canaries prove the executable wrapper doesn't overwrite tested tails.
            xguard = cp.full(n + 8, np.uint32(0x6badcafe), dtype=cp.uint32)
            yguard = cp.full(n + 8, np.uint32(0xdeadc0de), dtype=cp.uint32)
            x, y = xguard[4:4+n], yguard[4:4+n]
            x.set(host, stream=stream)
            grid = (max(1, (n + 255)//256),)
            for mask in masks:
                ref = reference(host, mask)
                np.testing.assert_array_equal(ref, host.byteswap() ^ np.uint32(mask))
                for name, kernel, g in [('ptx', candidate, grid), ('cuda', cuda, grid),
                                        ('cuda_vec4', cuda_vec, (max(1, ((n+3)//4+255)//256),))]:
                    kernel(g, (256,), (x, y, np.uint32(n), np.uint32(mask)))
                    stream.synchronize()
                    np.testing.assert_array_equal(cp.asnumpy(y), ref, err_msg=f'{name},n={n},mask={mask}')
                    np.testing.assert_array_equal(cp.asnumpy(x), host)
                    yg = cp.asnumpy(yguard)
                    assert np.all(yg[:4] == 0xdeadc0de) and np.all(yg[-4:] == 0xdeadc0de)
                    xg = cp.asnumpy(xguard)
                    assert np.all(xg[:4] == 0x6badcafe) and np.all(xg[-4:] == 0x6badcafe)
                oss = cp.bitwise_xor(x.byteswap(), np.uint32(mask))
                stream.synchronize()
                np.testing.assert_array_equal(cp.asnumpy(oss), ref)
            correctness.append({'n': n, 'masks': len(masks), 'methods': ['ptx', 'cuda', 'cuda_vec4', 'cupy_api'], 'passed': True})
        # Realistic negative controls on GPU: wrong nibble/byte order, index and tail.
        negative = []
        text = (HERE / 'endian_xor.ptx').read_text()
        mutations = {
            'wrong_byte_order': ('shl.b32 %r12, %r11, 16;', 'shl.b32 %r12, %r11, 8;'),
            'wrong_index': ('mad.lo.u32 %r5, %r2, %r3, %r4;', 'add.u32 %r5, %r4, 1;'),
            'dropped_tail': ('setp.ge.u32 %p, %r5, %r0;', 'sub.u32 %r0, %r0, 1;\n    setp.ge.u32 %p, %r5, %r0;'),
        }
        for name, (old, new) in mutations.items():
            assert old in text
            path = args.scratch / f'{name}.ptx'
            path.write_text(text.replace(old, new))
            bad = cp.RawModule(path=str(path)).get_function('endian_xor')
            host = np.resize(adversarial, 257).astype(np.uint32)
            host[-1] = 0x01020304
            x, y = cp.asarray(host), cp.full(265, np.uint32(0xdeadc0de))
            bad((2,), (256,), (x, y, np.uint32(257), np.uint32(0x01020304)))
            stream.synchronize()
            detected = not np.array_equal(cp.asnumpy(y[:257]), host.byteswap() ^ np.uint32(0x01020304))
            assert detected, name
            negative.append({'name': name, 'detected_on_gpu': detected, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    results = {'schema': 'e5r.ptx-from-spec.gpu.v1', 'date_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
               'device': subprocess.check_output(['nvidia-smi', '--query-gpu=name,driver_version,pstate,clocks.sm,clocks.mem,power.limit', '--format=csv'], text=True),
               'versions': {'numpy': np.__version__, 'cupy': cp.__version__, 'runtime': cp.cuda.runtime.runtimeGetVersion(), 'driver': cp.cuda.runtime.driverGetVersion()},
               'ptx_sha256': hashlib.sha256((HERE/'endian_xor.ptx').read_bytes()).hexdigest(),
               'baseline_source_sha256': hashlib.sha256((HERE/'baseline.cu').read_bytes()).hexdigest(),
               'lock': LOCK, 'foreign_compute_checks': 'before context, each correctness/shape/batch, after all work; abort on foreign PID',
               'correctness': correctness, 'negative_controls': negative,
               'rounds': args.rounds, 'repetitions': args.repetitions, 'timings': []}
    if args.correctness_only:
        return results
    # API byteswap has no out= parameter. This allocator returns a dedicated,
    # already allocated buffer; its size is checked and it is used only during
    # the single byteswap call. tmp is retained for the entire measurement.
    # Thus actual CuPy byteswap()/xor APIs execute without timed allocations.
    for n in SHAPES:
        no_foreign()
        with stream:
            x = cp.asarray(rng.integers(0, 2**32, n, dtype=np.uint32))
            y = cp.empty_like(x)
            tmp = cp.empty(max(1,n), dtype=cp.uint32)
            mask = np.uint32(0x01020304)
            grid = (max(1, (n+255)//256),)
            kernels = {
                'ptx_fused': lambda: candidate(grid, (256,), (x,y,np.uint32(n),mask)),
                'cuda_fused': lambda: cuda(grid, (256,), (x,y,np.uint32(n),mask)),
                'cuda_vec4_fused': lambda: cuda_vec((max(1,((n+3)//4+255)//256),), (256,), (x,y,np.uint32(n),mask)),
                'cuda_byteswap_only': lambda: swap(grid, (256,), (x,y,np.uint32(n),mask)),
            }
            def allocator(size):
                if size > tmp.nbytes:
                    raise RuntimeError(f'CuPy byteswap requests unexpected allocation {size}, reserved {tmp.nbytes}')
                return tmp.data
            def oss(fused=True):
                with cp.cuda.using_allocator(allocator):
                    v = x.byteswap()
                if fused:
                    cp.bitwise_xor(v, mask, out=y)
            kernels['cupy_api_fused'] = oss
            kernels['cupy_byteswap_only'] = lambda: oss(False)
            # Validate actual OSS APIs with the preallocated allocator.
            oss()
            stream.synchronize()
            np.testing.assert_array_equal(cp.asnumpy(y), cp.asnumpy(x).byteswap() ^ mask)
            for f in kernels.values():
                for _ in range(10): f()
            stream.synchronize()
            graphs = {}
            for name, f in kernels.items():
                stream.begin_capture()
                for _ in range(args.repetitions): f()
                graphs[name] = stream.end_capture()
            for graph in graphs.values(): graph.launch(stream)
            stream.synchronize()
            raw = {(mode, name): [] for mode in ['event', 'graph'] for name in kernels}
            for round_index in range(args.rounds):
                no_foreign()
                todo = list(raw)
                order_rng.shuffle(todo)
                for mode, name in todo:
                    start, stop = cp.cuda.Event(), cp.cuda.Event()
                    start.record(stream)
                    if mode == 'event':
                        for _ in range(args.repetitions): kernels[name]()
                    else:
                        graphs[name].launch(stream)
                    stop.record(stream)
                    stop.synchronize()
                    no_foreign()
                    raw[mode, name].append(cp.cuda.get_elapsed_time(start, stop)*1000 / args.repetitions)
            for (mode,name), samples in raw.items():
                med = statistics.median(samples)
                results['timings'].append({'n':n,'mode':mode,'method':name,'latency_us':med,
                    'min_us':min(samples),'max_us':max(samples),'stdev_us':statistics.stdev(samples),
                    'samples_us':samples,'effective_GBps':(8*n/med/1000) if med else 0})
            print(json.dumps({'n':n, 'graph_median_us':{name:statistics.median(raw['graph',name]) for name in kernels}}), flush=True)
        del graphs, kernels, x, y, tmp
        cp.get_default_memory_pool().free_all_blocks()
    return results


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--scratch',type=Path,default=Path('/mnt/scratch/e5r-ptx-from-spec'))
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--rounds',type=int,default=9)
    parser.add_argument('--repetitions',type=int,default=100)
    parser.add_argument('--wait-seconds',type=int,default=3600)
    parser.add_argument('--correctness-only',action='store_true')
    args=parser.parse_args()
    args.scratch.mkdir(parents=True,exist_ok=True)
    with exclusive_gpu(args.wait_seconds):
        data=run(args)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(data,indent=2)+'\n')
    print(f'Saved {args.out}',flush=True)

if __name__ == '__main__':
    main()
