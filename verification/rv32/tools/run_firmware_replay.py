#!/usr/bin/env python3
"""Whole-firmware differential test: run the Embassy firmware on QEMU's
sifive_e (HiFive1 Rev B) machine with a fixed UART input, trace every
instruction and interrupt, and replay the trace in the Lean model
(`lake exe replay`), comparing every register and modeled CSR after every
transition and the model's device traffic with QEMU's MMIO log. The PWM duty
values are checked against the values the input implies, and the replay's
negative controls (tools/test_replay_controls.py) run on the trace.

Environment: QEMU_SYSTEM_RISCV32 (default qemu-system-riscv32), QEMU_DATA
(directory with QEMU's firmware files, if not the default).
"""
import os
from pathlib import Path
import subprocess
import sys

VERIFY = Path(__file__).resolve().parents[1]
WORK = VERIFY / 'build/replay'
QEMU = os.environ.get('QEMU_SYSTEM_RISCV32', 'qemu-system-riscv32')
ELF = VERIFY / 'firmware/hifive1-embassy/target/riscv32imac-unknown-none-elf/release/hifive1-embassy'
INPUT = b'AzB\xff\x00Q'


def expected(data):
    window, out = [0] * 8, []
    for i, b in enumerate(data):
        window[i % 8] = b
        out.append(min(sum(window) // 8 + 7, 100))
    return out


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    log = WORK / 'qemu.log'
    args = [QEMU, '-M', 'sifive_e,revb=true', '-nographic', '-bios', 'none', '-kernel', ELF,
            '-accel', 'tcg,one-insn-per-tb=on', '-icount', 'shift=4', '-d', 'cpu,int,nochain',
            '-trace', 'memory_region_ops_read', '-trace', 'memory_region_ops_write', '-D', log]
    if 'QEMU_DATA' in os.environ:
        args += ['-L', os.environ['QEMU_DATA']]
    # Feed the input, then let the firmware run for two seconds of host time.
    proc = subprocess.Popen([str(a) for a in args], stdin=subprocess.PIPE,
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    proc.stdin.write(INPUT)
    proc.stdin.flush()
    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
    trace = WORK / 'trace.txt'
    subprocess.run(['python3', VERIFY / 'tools/qemu_trace.py', log, trace, '200000'], check=True)
    log.unlink()
    subprocess.run(['lake', 'build', 'replay'], cwd=VERIFY, check=True, stdout=subprocess.DEVNULL)
    out = subprocess.run([VERIFY / '.lake/build/bin/replay', trace], capture_output=True, text=True)
    print(out.stdout.strip())
    if out.returncode != 0:
        sys.exit(f'model and QEMU disagree:\n{out.stderr}')
    writes = [int(x) for x in out.stdout.split('[')[-1].rstrip(']\n').split(',') if x.strip()]
    want = expected(INPUT)
    if writes != want[:len(writes)] or not writes:
        sys.exit(f'duty writes {writes} do not match the input, expected a prefix of {want}')
    print(f'duty writes match the input: {writes}')
    subprocess.run(['python3', VERIFY / 'tools/test_replay_controls.py', trace], check=True)


if __name__ == '__main__':
    main()
