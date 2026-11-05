"""Report the complete frozen sweep; never select a favorable shape subset."""
from pathlib import Path
import csv
import io
import json
import math

D = Path(__file__).resolve().parent
NAMES = ['original', 'edited', 'edited64', 'matching_cuda', 'matching64_cuda']


def main():
    data = json.loads((D / 'results/performance.json').read_text())
    rows = data['rows']
    shapes = sorted({r['output_bytes'] for r in rows})
    sections = []
    summary = {}
    for block in [128, 256, 512]:
        text = [f'### {block} threads/block, graph replay', '',
                '| Output bytes | Original us | Scalar PTX us | Paired PTX us | Scalar CUDA us | Paired CUDA us |',
                '| ---: | ---: | ---: | ---: | ---: | ---: |']
        ratios = {name: [] for name in NAMES[1:]}
        for shape in shapes:
            selected = {r['name']: r for r in rows if r['output_bytes'] == shape
                        and r['block'] == block and r['graph']}
            assert set(selected) == set(NAMES), (block, shape)
            text.append('| ' + str(shape) + ' | ' + ' | '.join(
                f"{selected[name]['median_us']:.3f}" for name in NAMES) + ' |')
            for name in ratios:
                ratios[name].append(selected['original']['median_us'] / selected[name]['median_us'])
        gm = {name: math.exp(sum(map(math.log, values)) / len(values))
              for name, values in ratios.items()}
        summary[str(block)] = gm
        text += ['', 'All seven shapes, geometric mean original/candidate speedup: ' +
                 ', '.join(f'{name} {value:.3f}x' for name, value in gm.items()) + '.', '']
        sections.extend(text)
    profiles = []
    for path in sorted((D / 'results').glob('profile-*.csv')):
        if any(tag in path.stem for tag in ['-coalesced-', '-tiled-', '-paired2-']):
            continue
        records = list(csv.DictReader(io.StringIO(path.read_text())))
        units = records[0]
        row = next(r for r in records if r['ID'])
        metrics = {}
        for key in ['gpu__time_duration.sum', 'dram__bytes_read.sum', 'dram__bytes_write.sum',
                    'dram__throughput.avg.pct_of_peak_sustained_elapsed',
                    'sm__warps_active.avg.pct_of_peak_sustained_active',
                    'l1tex__t_sectors_pipe_lsu_mem_global_op_st.sum',
                    'l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum',
                    'smsp__inst_executed.sum', 'launch__registers_per_thread']:
            factor = {'Kbyte': 1e3, 'Mbyte': 1e6, 'Gbyte': 1e9,
                      'us': 1e3, 'ms': 1e6, 's': 1e9}.get(units.get(key), 1)
            metrics[key] = float(row[key]) * factor
        profiles.append(dict(run=path.stem, metrics=metrics, source_units={k: units[k] for k in metrics}))
    (D / 'results/summary.json').write_text(json.dumps(dict(
        fixed_block_graph_geomeans=summary, profiles=profiles), indent=2) + '\n')
    sections += ['### Large-workload Nsight diagnosis', '',
                 '| Kernel | Profile us | DRAM read MB | DRAM write MB | DRAM sustained % | Occupancy % | Store sectors | Registers/thread |',
                 '| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |']
    for profile in profiles:
        if 'no-restrict' in profile['run']:
            continue
        m = profile['metrics']
        sections.append('| ' + profile['run'] + ' | ' + ' | '.join([
            f"{m['gpu__time_duration.sum']/1e3:.2f}",
            f"{m['dram__bytes_read.sum']/1e6:.2f}",
            f"{m['dram__bytes_write.sum']/1e6:.2f}",
            f"{m['dram__throughput.avg.pct_of_peak_sustained_elapsed']:.2f}",
            f"{m['sm__warps_active.avg.pct_of_peak_sustained_active']:.2f}",
            f"{m['l1tex__t_sectors_pipe_lsu_mem_global_op_st.sum']:.0f}",
            f"{m['launch__registers_per_thread']:.0f}"]) + ' |')
    sections += ['', '''Profiling is a separate single profiled invocation at block=256 and
128 MiB output, with cache control none and clock control none. It is not
a replacement for repeated unprofiled timing. Compared with the original,
the scalar edit reduces executed instructions from 72.35 million to 15.47
million, but four adjacent outputs per thread produce strided warp stores:
store sectors rise from 4.19 million to 16.78 million. Paired-u64 stores reduce
that to 8.39 million. The rolling variants also retain roughly the original
number of load sectors despite fewer load instructions. DRAM traffic rises
from about 301 MB to 350 MB (scalar) or 323 MB (paired). Occupancy remains
above 83% and sustained DRAM throughput is around 90%; this evidence points
to transactions/bandwidth rather than instruction count or occupancy as the
large-workload bottleneck. DRAM bytes include transaction/ECC effects.
Earlier comparator profiles without __restrict__ remain explicitly named
no-restrict; the table and final sweep use the tuned comparators.
''']
    intro = '''# Stencil measurements

The direct scalar and paired-u64 edits regress over the full sweep. A local
1 MiB paired-store improvement does not establish a broad speedup. Competent
CUDA implementations of the same reuse techniques show similar behavior.
The initial 1.5x engineering target was missed.

These tables report fixed launch configurations separately, with no shape
selection. Raw performance.json retains seven CUDA-event repeats, variance,
host times and ordinary event measurements at block=256. Graph replay uses
100 captured launches, replayed ten times per repeat; buffers and compilation
are outside timing. Output bytes range from 32 to 128 MiB. The GPU is an A10G;
exact versions, hashes, grids and lock metadata are in the raw JSON. Input
traffic logically contains n+16 words; output contains n words. Logical
bandwidth counts each unique input once, not all executed overlapping loads.

Correctness tests and timing are empirical. Accepted strict proof replay
applies only to the exact scalar edited.ptx artifact, not edited64.ptx.
NVIDIA ptxas, driver JIT and hardware are outside the formal proof.

'''
    (D / 'RESULTS.md').write_text(intro + '\n'.join(sections))


if __name__ == '__main__':
    main()
