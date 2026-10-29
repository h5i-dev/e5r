#!/usr/bin/env python3
"""Instruction-level differential test of the Lean model against QEMU.

For each seed: generate a random RV32IMAC program (tools/gen_isa_test.py),
assemble and link it, run it under qemu-riscv32 with one instruction per
translation block, and replay QEMU's register trace in the model
(`lake build replay_isa`). Then check that every supported instruction kind
was executed, and that a corrupted trace is rejected.

Agreement is evidence about the model, not a proof: QEMU is a second
implementation of the specification, and user mode exercises no CSR,
interrupt or device behavior (the firmware replay covers those).

Environment: CROSS_COMPILE (default riscv64-linux-gnu-), QEMU_RISCV32
(default qemu-riscv32), LLVM_OBJDUMP (default: the pinned rustup toolchain's).
"""
import os
from pathlib import Path
import subprocess
import sys

VERIFY = Path(__file__).resolve().parents[1]
WORK = VERIFY / 'build/isa'
CROSS = os.environ.get('CROSS_COMPILE', 'riscv64-linux-gnu-')
QEMU = os.environ.get('QEMU_RISCV32', 'qemu-riscv32')
OBJDUMP = os.environ.get('LLVM_OBJDUMP', str(Path.home() /
    '.rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump'))
REPLAY = VERIFY / '.lake/build/bin/replay_isa'


def run(args, **kw):
    return subprocess.run([str(a) for a in args], check=True, **kw)


def trace(seed, count):
    stem = WORK / f'seed{seed}'
    run(['python3', VERIFY / 'tools/gen_isa_test.py', seed, count, f'{stem}.S'])
    run([CROSS + 'as', '-march=rv32imac', '-mabi=ilp32', '-o', f'{stem}.o', f'{stem}.S'])
    run([CROSS + 'ld', '-m', 'elf32lriscv', '-T', VERIFY / 'tools/isa_test.ld',
         '-o', f'{stem}.elf', f'{stem}.o'])
    log = WORK / f'seed{seed}.log'
    run([QEMU, '-one-insn-per-tb', '-d', 'cpu,int,nochain', '-D', log, f'{stem}.elf'])
    run(['python3', VERIFY / 'tools/qemu_trace.py', '--user', '--start', '0x10000', log,
         f'{stem}.txt', '10000000'])
    log.unlink()
    return Path(f'{stem}.elf'), Path(f'{stem}.txt')


def main():
    seeds = [int(s) for s in (sys.argv[1:] or ['1', '2', '3', '4'])]
    WORK.mkdir(parents=True, exist_ok=True)
    run(['lake', 'build', 'replay_isa'], cwd=VERIFY, stdout=subprocess.DEVNULL)
    traces = []
    for seed in seeds:
        elf, txt = trace(seed, 3000)
        out = subprocess.run([REPLAY, elf, txt], capture_output=True, text=True)
        print(f'seed {seed}: {out.stdout.splitlines()[0] if out.stdout else out.stderr.strip()}')
        if out.returncode != 0:
            sys.exit(f'seed {seed}: model and QEMU disagree:\n{out.stderr}')
        traces.append(txt)
    run(['python3', VERIFY / 'tools/isa_coverage.py', OBJDUMP, WORK / f'seed{seeds[0]}.elf', traces[0]])
    # Negative control: change one register value in the middle of a trace.
    lines = traces[0].read_text().splitlines()
    k = len(lines) // 2
    fields = lines[k].split()
    fields[11] = format(int(fields[11], 16) ^ 1, 'x')  # x10 (a0), flipped low bit
    bad = WORK / 'corrupted.txt'
    bad.write_text('\n'.join(lines[:k] + [' '.join(fields)] + lines[k + 1:]) + '\n')
    out = subprocess.run([REPLAY, WORK / f'seed{seeds[0]}.elf', bad], capture_output=True, text=True)
    if out.returncode == 0:
        sys.exit('the replay accepted a corrupted trace')
    print(f'corrupted trace rejected: {out.stderr.strip()[:120]}')


if __name__ == '__main__':
    main()
