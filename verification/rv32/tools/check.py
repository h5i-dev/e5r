#!/usr/bin/env python3
"""Rebuild exact ELF inputs, export with e5r, check Lean and audit assumptions."""
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
VERIFY = ROOT / 'verification/rv32'
BUILD = ROOT / 'fixtures/build/lean-rv32'
CROSS = os.environ.get('CROSS_COMPILE', 'riscv64-linux-gnu-')
QEMU = os.environ.get('QEMU_RISCV32', 'qemu-riscv32')
PINS = json.loads((VERIFY/'toolchain.json').read_text())
IDENTITIES = json.loads((VERIFY/'identities.json').read_text())
ENV = dict(os.environ, LEAN_PATH='.')


def run(args, cwd=ROOT, env=None):
    return subprocess.check_output([str(a) for a in args], cwd=cwd, env=env, stderr=subprocess.STDOUT).decode()


def audit(output):
    # Every printed theorem must have only explicitly allowed logical axioms.
    for line in output.splitlines():
        if re.fullmatch(r"'[^']+' does not depend on any axioms", line):
            continue
        m = re.fullmatch(r"'[^']+' depends on axioms: \[([^]]*)\]", line)
        if not m or set(m[1].split(', ')) - {'propext', 'Quot.sound'}:
            raise RuntimeError(f'Unexpected Lean output/axiom: {line}')
    print(output, end='')


def run_lean(args):
    # -M limits Lean-managed allocation, but kernel diagnostics can exceed it.
    # Enforce a Linux resident-memory ceiling too; never return a partial result.
    with tempfile.TemporaryFile() as output:
        proc = subprocess.Popen(args, cwd=VERIFY, env=ENV,
                                stdout=output, stderr=subprocess.STDOUT)
        try:
            while proc.poll() is None:
                try:
                    status = Path(f'/proc/{proc.pid}/status').read_text()
                    rss = re.search(r'^VmRSS:\s+(\d+) kB$', status, re.M)
                    if rss and int(rss[1]) > 5 * 1024 * 1024:
                        raise RuntimeError('Lean exceeded the 5 GiB resident-memory budget')
                except FileNotFoundError:
                    pass  # Child exited between poll and status read.
                time.sleep(0.25)
        finally:
            if proc.poll() is None:
                proc.kill()
            proc.wait()
        output.seek(0)
        return subprocess.CompletedProcess(args, proc.returncode, output.read().decode())


def lean(path, compile=True):
    args = ['lean', '-j1', '-M4096']
    if compile:
        args += ['-o', str(path.with_suffix('.olean'))]
    args += [str(path)]
    # Lean's allocator reserves more virtual space than its resident memory.
    # Use its own allocation budget and one worker rather than RLIMIT_AS.
    result = run_lean(args)
    if result.returncode:
        raise subprocess.CalledProcessError(result.returncode, args, result.stdout.encode())
    out = result.stdout
    audit(out)
    return out


def export(elf, image, namespace='Exported'):
    raw = elf.read_bytes()
    if hashlib.sha256(raw).hexdigest() != IDENTITIES[elf.stem]:
        raise RuntimeError(f'{elf.name}: image identity changed; review bytes and identities.json')
    source = run([ROOT/'target/release/e5r-verify', elf])
    # This binds the literal in the actual Lean source to every original file
    # byte. A digest alone, or checking a separate JSON sidecar, is insufficient.
    literal = re.search(r'^def elfBytes : List Nat := (\[.*\])$', source, re.M)
    if literal is None or ast.literal_eval(literal[1]) != list(raw):
        raise RuntimeError('exported original-byte literal differs from ELF')
    source = source.replace('namespace Exported', f'namespace {namespace}')
    source = source.replace('end Exported', f'end {namespace}')
    image.write_text(source)
    # Compare fresh exports as a determinism check.
    again = run([ROOT/'target/release/e5r-verify', elf])
    assert again.replace('namespace Exported', f'namespace {namespace}').replace(
        'end Exported', f'end {namespace}') == source
    return {'elf_sha256': hashlib.sha256(raw).hexdigest(),
            'lean_image_sha256': hashlib.sha256(source.encode()).hexdigest(),
            'elf_bytes': len(raw)}


def main():
    BUILD.mkdir(parents=True, exist_ok=True)
    versions = {
        'lean': run(['lean', '--version'], cwd=VERIFY).strip(),
        'as': run([CROSS+'as', '--version']).splitlines()[0],
        'ld': run([CROSS+'ld', '--version']).splitlines()[0],
        'qemu': run([QEMU, '--version']).splitlines()[0],
        'rust': run(['rustup', 'run', PINS['rust'], 'rustc', '-vV']).strip(),
    }
    for key, pin in [('lean', PINS['lean']), ('as', PINS['binutils']),
                     ('ld', PINS['binutils']), ('qemu', PINS['qemu'])]:
        if not re.search(r'(?<![\d.])'+re.escape(pin)+r'(?![\d.])', versions[key]):
            raise RuntimeError(f'{key}: expected {pin}, found {versions[key]}')
    records = {'versions': versions, 'images': {}, 'commands': []}
    def build(args):
        records['commands'].append([str(a.relative_to(ROOT)) if isinstance(a, Path)
                                    and a.is_relative_to(ROOT) else str(a) for a in args])
        run(args)
    asm = VERIFY/'Projects/clamp'
    build([CROSS+'as', '-march=rv32i', '-mabi=ilp32', '-o', BUILD/'clamp.o', asm/'clamp.S'])
    build([CROSS+'ld', '-m', 'elf32lriscv', '--no-relax', '-n', '-T', asm/'link.ld',
           '-o', BUILD/'clamp.elf', BUILD/'clamp.o'])
    records['images']['assembly'] = export(BUILD/'clamp.elf', asm/'Image.lean')
    for opt in [1, 2]:
        elf = BUILD/f'rust-O{opt}.elf'
        args = ['rustup', 'run', PINS['rust'], 'rustc', '--target', 'riscv32i-unknown-none-elf',
                '--crate-type', 'bin', '--edition', '2024', '-C', f'opt-level={opt}',
                '-C', 'panic=abort', '-C', 'relocation-model=static',
                '-C', 'link-arg=--no-relax', '-C', 'link-arg=-n',
                '-C', 'link-arg=-Tverification/rv32/Projects/clamp/link.ld',
                '-C', 'strip=none', '-o', elf, VERIFY/'Projects/rust_clamp/clamp.rs']
        build(args)
        records['images'][f'rust-O{opt}'] = export(
            elf, VERIFY/f'Projects/rust_clamp/ImageO{opt}.lean', f'RustO{opt}.Exported')
    # Rebuild from source every time. Never accept an existing proof olean.
    for path in ['Theories/RV32.lean', 'Theories/ELF.lean', 'Projects/ClampSpec.lean',
                 'Projects/clamp/Image.lean', 'Projects/clamp/Proof.lean',
                 'Projects/rust_clamp/ImageO1.lean', 'Projects/rust_clamp/ProofO1.lean',
                 'Projects/rust_clamp/ImageO2.lean', 'Projects/rust_clamp/ProofO2.lean',
                 'Negative.lean']:
        print(f'Checking {path}', flush=True)
        lean(Path(path))
    print(run(['python3', VERIFY/'tools/oracle.py']), end='')
    lean(Path('Oracle.lean'))
    # A negative end-to-end control: the kernel must reject claiming that an
    # instruction-mutated image still meets the original exact specification.
    control = VERIFY/'RejectControl.lean'
    control.write_text('import Negative\nexample : Clamp.check Negative.wrongImage '
                       'Exported.entry 0x101c 7 0 = true := by\n'
                       '  rw [Negative.changed_clamp_rejected]\n'
                       '  decide +kernel\n')
    try:
        rejected = run_lean(['lean', '-j1', '-M4096', 'RejectControl.lean'])
        if rejected.returncode == 0 or 'is false' not in rejected.stdout:
            raise RuntimeError('Lean failed negative mutation control: '+rejected.stdout)
        print('Lean rejected the instruction-mutated clamp proof as required')
    finally:
        control.unlink()
    # Audit every theorem, including those without a local #print directive.
    paths = [VERIFY/'Projects/clamp/Proof.lean', VERIFY/'Projects/ClampSpec.lean',
             VERIFY/'Projects/rust_clamp/ProofO1.lean', VERIFY/'Projects/rust_clamp/ProofO2.lean',
             VERIFY/'Negative.lean', VERIFY/'Oracle.lean']
    modules = ['Projects.clamp.Proof', 'Projects.ClampSpec', 'Projects.rust_clamp.ProofO1',
               'Projects.rust_clamp.ProofO2', 'Negative', 'Oracle']
    lines = ['import '+m for m in modules]
    count = 0
    for p in paths:
        s = p.read_text()
        namespace = re.search(r'^namespace (\w+)', s, re.M)[1]
        for name in re.findall(r'^theorem (\w+)', s, re.M):
            lines.append(f'#print axioms {namespace}.{name}')
            count += 1
    (VERIFY/'Audit.lean').write_text('\n'.join(lines)+'\n')
    output = lean(Path('Audit.lean'), compile=False)
    if len(output.splitlines()) != count:
        raise RuntimeError('incomplete theorem axiom audit')
    for p in VERIFY.rglob('*.lean'):
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', p.read_text()):
            raise RuntimeError(f'disallowed proof escape in {p}')
    (BUILD/'provenance.json').write_text(json.dumps(records, indent=2)+'\n')
    (BUILD/'axioms.txt').write_text(output)
    print(f'Checked {count} theorem declarations. Provenance: {BUILD}/provenance.json')


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as exc:
        if exc.output:
            print(exc.output.decode(), end='')
        raise
