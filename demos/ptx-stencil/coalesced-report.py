"""Complete sweeps, exact source bindings and hardware transaction evidence."""
from pathlib import Path
import csv
import hashlib
import json
import math

D=Path(__file__).resolve().parent
SHAPES=[32,256,4096,65536,1048576,16777216,134217728]


def main():
    freeze=json.loads((D/'freeze.json').read_text())
    for name,expected in freeze['sha256'].items():
        assert hashlib.sha256((D/name).read_bytes()).hexdigest()==expected,name
    text=['# Coalesced stencil edits: experimental results','',
          'All new variants are directly authored PTX. Each needs its own proof;',
          'GPU correspondence and timing are empirical.',
          'All seven predeclared shapes and fixed block sizes are retained;',
          'these tables use graph medians. Raw JSON includes all seven repeats,',
          'variance, host times and ordinary event measurements at block=256.',
          'The original and each matching CUDA comparator are measured again in',
          'each sweep. A ratio above 1 is faster than the frozen original.','']
    summaries={}
    text += ['## Proof acceptance','']
    for name in ['scalar2','paired2']:
        path=D/f'results/{name}-proof.json'
        proof=json.loads(path.read_text()) if path.exists() else None
        if proof and proof['verdict']=='proved':
            assert proof['input']['ptx']['sha256']==hashlib.sha256((D/(name+'.ptx')).read_bytes()).hexdigest()
            assert proof['proof']['sha256']==hashlib.sha256((D/(name+'-equivalence.lean')).read_bytes()).hexdigest()
            check=proof['proof']['check']
            assert set(check['axioms']) <= {'propext','Quot.sound','Classical.choice'}
            text += [f"{name}: strictly accepted, {check['declarations']} declarations; "+
                     'axioms '+', '.join(check['axioms'])+'.','']
        else:
            text += [f'{name}: strict acceptance pending.','']
    for stem in ['coalesced','tiled','paired2','paired2-pointer']:
        path=D/f'results/{stem}-performance.json'
        if not path.exists():continue
        data=json.loads(path.read_text());rows=data['rows']
        for name,expected in data['metadata']['ptx_sha256'].items():
            assert hashlib.sha256((D/(name+'.ptx')).read_bytes()).hexdigest()==expected,name
        for name,expected in data['metadata']['cuda_sha256'].items():
            assert hashlib.sha256((D/name).read_bytes()).hexdigest()==expected,name
        names=list(dict.fromkeys(r['name'] for r in rows))
        assert sorted({r['output_bytes'] for r in rows})==SHAPES
        assert len(rows)==7*len(names)*4,(stem,len(rows))
        text += [f'## {stem} sweep','']
        summaries[stem]={}
        for block in [128,256,512]:
            text += [f'### {block} threads/block','',
                     '| Output bytes | '+' | '.join(name+' us' for name in names)+' |',
                     '| ---: | '+' | '.join('---:' for _ in names)+' |']
            ratios={name:[] for name in names if name!='original'}
            for n in SHAPES:
                selected={r['name']:r for r in rows if r['output_bytes']==n and r['block']==block and r['graph']}
                assert len(selected)==len(names)
                text.append('| '+str(n)+' | '+' | '.join(f"{selected[k]['median_us']:.3f}" for k in names)+' |')
                for k in ratios:ratios[k].append(selected['original']['median_us']/selected[k]['median_us'])
            gm={k:math.exp(sum(map(math.log,v))/len(v)) for k,v in ratios.items()}
            summaries[stem][str(block)]=gm
            text += ['','All-shape geometric mean original/candidate: '+', '.join(f'{k} {v:.3f}x' for k,v in gm.items())+'.','']
    text += ['## Transaction profiles','',
             'Default profiles use 128 MiB output and block=256. Additional sizes',
             'and blocks are explicit in profile filenames (bytes-bBLOCK).',
             'Separate Nsight invocations, cache control none, clock control none.',
             'The profiled single invocation does not replace repeated timing.','',
             '| Profile | Time us | Global load sectors | Global store sectors | Shared store bank conflicts | Shared load bank conflicts |',
             '| --- | ---: | ---: | ---: | ---: | ---: |']
    for stem in ['coalesced','tiled','paired2','pointer2']:
        for path in sorted((D/'results').glob(f'profile-{stem}-*.csv')):
            records=list(csv.DictReader(path.open()));units=records[0]
            r=next(r for r in records if r['ID'])
            def metric(k):
                factor={'us':1e3,'ms':1e6,'s':1e9}.get(units.get(k),1)
                return float(r[k])*factor
            duration=metric('gpu__time_duration.sum')/1e3
            counts=[f"{metric('l1tex__t_sectors_pipe_lsu_mem_global_op_'+op+'.sum'):.0f}" for op in ['ld','st']]
            banks=[r.get('l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_'+op+'.sum','n/a') for op in ['st','ld']]
            text.append('| '+path.stem+' | '+f'{duration:.2f}'+' | '+' | '.join(counts+banks)+' |')
    text += ['', '''Striped independent accumulators restore coalesced stores but lose adjacent
rolling reuse. Output staging retains rolling reuse and restores the original
store-sector count, but leaves global-load sectors roughly unchanged and adds
shared bank conflicts. Input tiling instead loads each input tile cooperatively
once, including its 16-word halo, then reuses it through shared memory after a
barrier. One-output and four-output variants are measured separately.
Two-output rolling isolates scalar versus aligned-u64 global stores; its
dynamic alignment check and scalar/tail paths retain four-byte base alignment.
No unsupported shuffle or vector instruction is assumed successful.

The paired2-pointer sweep strengthens the CUDA comparator by hoisting input
and output pointers before the unrolled loads, avoiding repeated u32 index
address arithmetic. The earlier comparison is retained separately. At one MiB
and block=128 the new sweep measures 3.644 us original, 2.830 us PTX and
2.950 us stronger CUDA. Its all-seven-shape geometric means are 1.017x PTX
and 1.009x CUDA versus original. Block=256 is approximately parity; block=512
regresses. Large workloads still regress; the 1.5x target was missed.

At one MiB/block128 the loaded PTX and stronger CUDA each contain 64 SASS
instructions and use 26 registers. Nsight smsp__inst_executed.sum is 196608
versus 217088, with the same global load/store sectors. This is consistent
with a cache-resident instruction-sequence benefit. It does not establish a
general PTX-only advantage or a large-workload bandwidth improvement. The
initial CUDA comparator's 80 loaded instructions and 31 registers are also
preserved. Profiles are empirical; ptxas/JIT translation is outside Lean.

All benchmark/test commands hold the shared GPU flock and check foreign GPU
processes. coalesced-partial-contended.json retains the excluded first attempt,
aborted when a metric query created another GPU context. Handover waits poll
for the previous process's CUDA teardown before starting; foreign-process
checks remain active during every timing repeat. No result from a refused
attempt is included in the tables.
''']
    (D/'COALESCED.md').write_text('\n'.join(text))
    (D/'results/coalesced-summary.json').write_text(json.dumps(summaries,indent=2)+'\n')


if __name__=='__main__':main()
