"""Rebind mutant hashes and require semantic proof rejection, plus GPU witnesses."""
from pathlib import Path
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys

D = Path(__file__).resolve().parent
PAIR = '--paired2' in sys.argv
WIDE = '--wide-branch' in sys.argv
VARIANT = 'wide-branch' if WIDE else 'paired2' if PAIR else ''
PREFIX = VARIANT+'-' if VARIANT else ''
W = Path(os.environ.get('E5R_DEMO_SCRATCH', '/mnt/scratch/e5r-ptx-demo')) / ('negative-stencil-'+VARIANT if VARIANT else 'negative-stencil')
EXE = os.environ.get('E5R_VERIFY', '/mnt/scratch/e5r-ptx-demo/cargo/release/e5r')


def main():
    source = (D / (VARIANT+'.ptx' if VARIANT else 'edited.ptx')).read_text()
    proof = (D / (VARIANT+'-equivalence.lean' if VARIANT else 'equivalence.lean')).read_text()
    contract = json.loads((D / (VARIANT+'-equivalence.json' if VARIANT else 'equivalence.json')).read_text())
    contract['original_ptx'] = str(D / 'original.ptx')
    mutations = {
        'wrong-window-load': source.replace('ld.global.u32 %r26, [%rd6+64];',
                                            'ld.global.u32 %r26, [%rd6+60];'),
        'wrong-entry-guard': source.replace('setp.ge.u32 %p1, %r1, %r6;',
                                            'setp.gt.u32 %p1, %r1, %r6;'),
    }
    if PAIR:
        mutations = {
            'wrong-packed-shift': source.replace('shl.b64 %rd11, %rd11, 32;',
                                                 'shl.b64 %rd11, %rd11, 31;'),
            'wrong-entry-guard': source.replace('setp.ge.u32 %p1, %r1, %r6;',
                                                'setp.gt.u32 %p1, %r1, %r6;'),
        }
    if WIDE:
        mutations = {
            'wrong-wide-index': source.replace('ld.global.u64 %rd15, [%rd6+64];',
                                               'ld.global.u64 %rd15, [%rd6+72];'),
            'wrong-wide-tail': source.replace('setp.ge.u32 %p1, %r7, %r2;',
                                              'setp.gt.u32 %p1, %r7, %r2;',1),
        }
    summary = []
    for name, text in mutations.items():
        assert text != source, name
        out = W / name
        out.mkdir(parents=True, exist_ok=True)
        (out / 'kernel.ptx').write_text(text)
        spec = json.dumps(contract, indent=2) + '\n'
        (out / 'contract.json').write_text(spec)
        rebound = re.sub(r'ptx=[0-9a-f]{64}',
                         'ptx=' + hashlib.sha256(text.encode()).hexdigest(), proof, count=1)
        rebound = re.sub(r'spec=[0-9a-f]{64}',
                         'spec=' + hashlib.sha256(spec.encode()).hexdigest(), rebound, count=1)
        (out / 'proof.lean').write_text(rebound)
        result = D / 'results' / f'{PREFIX}negative-{name}.json'
        command = [EXE, 'ptx', 'check', str(out / 'kernel.ptx'), '--spec',
                              str(out / 'contract.json'), '--proof', str(out / 'proof.lean'),
                              '--keep', str(out / 'check'), '--out', str(result),
                              '--timeout', '300', '--memory-mb', '5120']
        if '--gpu-only' not in sys.argv:
            run = subprocess.run(command, cwd=D.parent.parent, capture_output=True, text=True, timeout=650)
            assert run.returncode != 0
        doc = json.loads(result.read_text())
        reasons = str(doc['reasons'])
        assert doc['verdict'] == 'unknown', doc
        assert doc['input']['ptx']['sha256'] == hashlib.sha256(text.encode()).hexdigest()
        assert doc['proof']['sha256'] == hashlib.sha256(rebound.encode()).hexdigest()
        assert 'does not compile' in reasons and not any(
            s in reasons for s in ['stopped:', 'different ptx', 'different spec']), doc
        summary.append(dict(case=name, verdict=doc['verdict'], reasons=doc['reasons']))
        print(name, doc['verdict'], flush=True)

    import cupy as cp
    import numpy as np
    sys.path.insert(0, str(D.parent / 'verified-packing'))
    from benchmark import uncontended
    from experiment import await_gpu_idle
    with open('/mnt/scratch/e5r-gpu-benchmark.lock', 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        await_gpu_idle()
        uncontended()
        original = cp.RawModule(path=str(D / 'original.ptx')).get_function('stencil17')
        # Physically overallocate for diagnostics of the deliberately wrong guard.
        x = cp.arange(128, dtype=cp.uint32)
        for row in summary:
            uncontended()
            bad = cp.RawModule(path=str(W / row['case'] / 'kernel.ptx')).get_function('stencil17')
            y = cp.full(128, 0xa5a5a5a5, dtype=cp.uint32)
            z = cp.full_like(y, 0xa5a5a5a5)
            witness_n = 7 if row['case']=='wrong-wide-tail' else 8
            original((1,), (32,), (x, y, np.uint32(witness_n)))
            bad((1,), (32,), (x, z, np.uint32(witness_n)))
            diffs = np.flatnonzero(y.get() != z.get())
            assert len(diffs), row['case']
            row['gpu_witness'] = dict(n=witness_n, differing_word_indices=diffs.tolist())
        uncontended()
    (D / f'results/{PREFIX}negative-controls.json').write_text(json.dumps(summary, indent=2) + '\n')


if __name__ == '__main__':
    main()
