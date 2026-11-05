#!/usr/bin/env python3
"""End-to-end freshness, tamper controls and relocated bundles for both backends.

Use --out on scratch storage. Runs real pinned Lean, serially, without GPU access.
Every modified input belongs to a private bundle, never the original project.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import shutil
import struct

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bin', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--only', action='append', choices=['firmware', 'ram', 'ptx', 'refuted', 'supplied'])
    args = parser.parse_args()
    exe = args.bin.resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, TMPDIR=str(out), CARGO_BUILD_JOBS='2', LEAN_NUM_THREADS='1')

    def run(argv, success=True):
        p = subprocess.run([exe, *map(str, argv)], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=2400)
        detail = p.stdout[-2000:]
        try:
            d = json.loads(p.stdout)
            detail = (d.get('status'), d.get('message'), d.get('reasons'))
        except ValueError:
            pass
        assert (p.returncode == 0) == success, (argv, p.returncode, detail, p.stderr[-2000:])
        return p

    # Private RAM-image project: an independently constructed minimal static ELF
    # exercises the second firmware placement contract without an RMK download.
    ram_parent = out / 'ram-fixture'
    ram_root = ram_parent / 'rv32'
    ram_root.mkdir(parents=True)
    original = ROOT / 'verification/rv32'
    ignore = shutil.ignore_patterns('.lake', '*.olean', '*.ilean', '*.c', '__pycache__')
    shutil.copytree(original / 'Theories', ram_root / 'Theories', ignore=ignore)
    shutil.copytree(original / 'boards', ram_root / 'boards')
    shutil.copytree(ROOT / 'verification/common', ram_parent / 'common', ignore=ignore)
    for rel in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'tools/ProofCheck.lean', 'tools/gen_board.py']:
        dst = ram_root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(original / rel, dst)
    (ram_root / 'Projects/ramtest').mkdir(parents=True)
    (ram_root / 'jobs').mkdir()
    elf = bytearray(128)
    elf[:7] = b'\x7fELF\x01\x01\x01'
    for offset, value in [(16, 2), (18, 243), (40, 52), (42, 32), (44, 1), (46, 40)]:
        struct.pack_into('<H', elf, offset, value)
    for offset, value in [(20, 1), (24, 0x80000000), (28, 52), (52, 1), (56, 124),
                          (60, 0x80000000), (64, 0x80000000), (68, 4), (72, 8), (76, 5), (80, 4),
                          (124, 0x00700513)]:
        struct.pack_into('<I', elf, offset, value)
    (ram_root / 'program.elf').write_bytes(elf)
    ram_job = ram_root / 'jobs/ram-test.json'
    ram_job.write_text(json.dumps({'schema': 'e5r.verify.job.v1', 'id': 'ram-test', 'root': '..',
        'board': 'boards/qemu-virt-rv32.json', 'elf': 'program.elf',
        'image': {'kind': 'ram', 'module': 'Projects.ramtest.Image', 'namespace': 'E5R.TestRam'},
        'modules': [], 'theorems': [], 'limits': {'seconds': 1800, 'rss_mib': 3072}}))
    cases = [
        ('firmware', ['check', ROOT / 'verification/rv32/jobs/hifive1-clamp32.json']),
        ('ram', ['check', ram_job]),
        ('ptx', ['ptx', 'check', ROOT / 'verification/ptx/benchmarks/correct/vadd_nvcc.ptx',
                 '--spec', ROOT / 'verification/ptx/benchmarks/specs/vadd.json', '--memory-mb', '4096']),
        ('refuted', ['ptx', 'check', ROOT / 'verification/ptx/benchmarks/buggy/vadd_sub.ptx',
                     '--spec', ROOT / 'verification/ptx/benchmarks/specs/vadd.json', '--memory-mb', '4096']),
        ('supplied', ['ptx', 'check', ROOT / 'verification/ptx/m5/m4/kernels/a_direct.ptx',
                      '--spec', ROOT / 'verification/ptx/m5/m4/specs/a_direct.json',
                      '--proof', ROOT / 'verification/ptx/proofs/a_direct.lean', '--memory-mb', '8192']),
    ]
    for name, command in cases:
        if args.only and name not in args.only:
            continue
        p = run(command, name != 'refuted')
        doc = json.loads(p.stdout)
        result = out / f'{name}.json'
        result.write_text(json.dumps(doc))
        assert doc['verification']['outcome'] == ('refuted' if name == 'refuted' else 'proved')
        run(['verify-result', result])
        for field in ['evidence_id', 'binding']:
            altered = copy.deepcopy(doc)
            altered['verification'][field] = 'wrong'
            bad = out / f'{name}-bad-{field}.json'
            bad.write_text(json.dumps(altered))
            run(['verify-result', bad], False)
        altered = copy.deepcopy(doc)
        altered['theorem'] = {'name': 'wrong', 'statement': 'True'}
        bad = out / f'{name}-wrong-statement.json'
        bad.write_text(json.dumps(altered))
        run(['verify-result', bad], False)

        altered = copy.deepcopy(doc)
        if name in ['firmware', 'ram']:
            altered['inputs']['elf']['sha256'] = 'wrong'
        else:
            altered['input']['ptx']['sha256'] = 'wrong'
        bad = out / f'{name}-wrong-legacy-input.json'
        bad.write_text(json.dumps(altered))
        run(['verify-result', bad], False)

        bundle = out / f'{name}-bundle'
        run(['bundle-result', result, '--out', bundle])
        moved = out / f'{name}-relocated'
        bundle.rename(moved)
        manifest = json.loads((moved / 'bundle.json').read_text())
        changed_manifest = copy.deepcopy(manifest)
        changed_manifest['outcome'] = 'refuted' if name != 'refuted' else 'proved'
        (moved / 'bundle.json').write_text(json.dumps(changed_manifest))
        run(['replay-bundle', moved], False)
        if name in ['ptx', 'refuted', 'supplied']:
            changed_manifest = copy.deepcopy(manifest)
            previous = changed_manifest['invocation']['program']
            changed_manifest['invocation']['program'] = next(p for p in manifest['identity']['files'] if p.endswith('.ptx') and p != previous)
            (moved / 'bundle.json').write_text(json.dumps(changed_manifest))
            run(['replay-bundle', moved], False)
        (moved / 'bundle.json').write_text(json.dumps(manifest))
        if name in ['firmware', 'ram']:
            patterns = ['.elf', 'Proof.lean'] if name == 'firmware' else ['.elf', 'RamElf.lean']
            targets = [next(p for p in manifest['identity']['files'] if p.endswith(pattern)) for pattern in patterns]
        else:
            targets = [manifest['invocation']['program'], manifest['invocation']['spec'],
                       next(p for p in manifest['identity']['files'] if p.endswith('Syntax.lean'))]
            if name == 'supplied':
                targets.append(manifest['invocation']['proof'])
        for rel in targets:
            path = moved / rel
            original = path.read_bytes()
            path.write_bytes(original + b'\nchanged\n')
            run(['replay-bundle', moved], False)
            path.write_bytes(original)
        replay = run(['replay-bundle', moved])
        (out / f'{name}-replayed.json').write_text(replay.stdout)
        assert json.loads(replay.stdout)['verification']['outcome'] == doc['verification']['outcome']
        if name == 'supplied':
            # A replay must leave the recorded acceptance inputs usable again.
            run(['verify-result', out / f'{name}-replayed.json'])
            run(['replay-bundle', moved])
        if name == 'firmware':
            replay_doc = json.loads(replay.stdout)
            private_job = Path(replay_doc['verification']['request']['invocation']['job'])
            private_root = (private_job.parent / json.loads(private_job.read_text())['root']).resolve()
            compiled = private_root / 'Theories/Hart.olean'
            compiled.write_bytes(b'corrupted cache')
            resumed = json.loads(run(['check', private_job, '--resume']).stdout)
            assert resumed['status'] == 'proved'
            assert 'Theories/Hart.lean' not in resumed['resumed'], resumed['resumed']
        print(f'{name}: fresh identity, altered claim/policy refused, input tampering refused, relocated replay passed', flush=True)

    if args.only and 'firmware' not in args.only:
        return

    # Preserve the original firmware Lean-only bundle contract too.
    legacy = out / 'legacy-firmware'
    run(['bundle', ROOT / 'verification/rv32/jobs/hifive1-clamp32.json', '--out', legacy])
    p = subprocess.run(['bash', legacy / 'recheck.sh'], cwd=ROOT, env=env,
                       capture_output=True, text=True, timeout=300)
    (out / 'legacy-recheck.log').write_text(p.stdout + p.stderr)
    assert p.returncode == 0, p.stdout + p.stderr
    print('legacy firmware: independent Lean-only replay passed', flush=True)


if __name__ == '__main__':
    main()
