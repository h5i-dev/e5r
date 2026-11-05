#!/usr/bin/env python3
"""Render every predeclared shape and comparison from raw measured batches."""
import argparse
import json
import math
from pathlib import Path

HERE=Path(__file__).resolve().parent


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('input',type=Path,nargs='?',default=HERE/'results/benchmark-run1.json')
    args=parser.parse_args()
    data=json.loads(args.input.read_text())
    rows={(r['n'],r['mode'],r['method']):r for r in data['timings']}
    shapes=sorted({r['n'] for r in data['timings']})
    print('All latencies in microseconds; medians of nine batches, 100 operations/batch. Ratios are baseline / PTX. Effective throughput counts 8*n bytes (one input + one output), including for comparisons with extra traffic. SD and all nine raw samples are in JSON.\n')
    for mode in ['graph','event']:
        print(f'{mode} timing\n')
        print('| n | PTX us | PTX SD | PTX GB/s | CuPy swap+XOR us | CuPy/PTX | CUDA scalar us | CUDA vec4 us | best CUDA/PTX | CuPy swap only us | CUDA swap only us |')
        print('| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |')
        ratios=[]
        for n in shapes:
            get=lambda name:rows[n,mode,name]['latency_us']
            p=get('ptx_fused'); c=get('cupy_api_fused')
            cuda=min(get('cuda_fused'),get('cuda_vec4_fused'))
            row=rows[n,mode,'ptx_fused']
            print(f"| {n} | {p:.4f} | {row['stdev_us']:.4f} | {row['effective_GBps']:.2f} | {c:.4f} | {c/p:.3f} | {get('cuda_fused'):.4f} | {get('cuda_vec4_fused'):.4f} | {cuda/p:.3f} | {get('cupy_byteswap_only'):.4f} | {get('cuda_byteswap_only'):.4f} |")
            if n>=1048576: ratios.append(c/p)
        print(f'\nPredeclared large-shape CuPy/PTX geometric mean: {math.exp(sum(map(math.log,ratios))/len(ratios)):.3f}x.\n')
    print('Graph timing excludes Python per-operation submission gaps; direct event timing includes those gaps. Prefer graph timing when attributing device execution gains. For n=0 CuPy emits no transform kernels, while PTX/CUDA deliberately launch a guarded no-op. Standalone swap-only rows perform less work and are context, not equal-function speedup baselines.')

if __name__=='__main__': main()
