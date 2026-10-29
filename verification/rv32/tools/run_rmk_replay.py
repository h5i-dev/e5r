#!/usr/bin/env python3
"""Whole-program differential test of the RMK qemu-riscv-rynk example on
QEMU virt (R1): run the pinned release ELF on `-M virt -cpu rv32
-semihosting -bios none`, feed a fixed UART input, trace every instruction
and every MMIO access, and replay the trace in the Lean model
(`lake exe replay_virt`): every register and modeled CSR after every
transition, and every UART register access (address, width, value, order)
against QEMU's MMIO log.

Initial conditions and exclusions (also in tools/ReplayVirt.lean and
boards/qemu-virt-rv32.json):
* the model starts at QEMU's first state at the ELF entry, after QEMU's
  reset ROM (not modeled), with QEMU's registers and CSRs there, and RAM as
  QEMU loads the image (writable segments' bytes, zero elsewhere);
* the image is RamElf.imageOf of the packed ELF (tools/pack_elf.py);
* the semihosting calls (ebreak sites found in the ELF by their
  slli/ebreak/srai sequence) are QEMU's steps, accepted only for
  operations that write no guest memory, with every register but a0 kept.

Environment: RMK_ELF (the pinned release ELF; its sha256 is checked),
QEMU_SYSTEM_RISCV32, QEMU_DATA, RMK_STATES (trace length, default 300000).
Scratch goes to RMK_WORK (default /dev/shm/e5r-rmk-replay)."""
import hashlib
import os
from pathlib import Path
import socket
import struct
import subprocess
import sys
import time

VERIFY = Path(__file__).resolve().parents[1]
PIN = 'f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30'
ELF = Path(os.environ.get('RMK_ELF', ''))
WORK = Path(os.environ.get('RMK_WORK', '/dev/shm/e5r-rmk-replay'))
QEMU = os.environ.get('QEMU_SYSTEM_RISCV32', 'qemu-system-riscv32')
STATES = int(os.environ.get('RMK_STATES', '300000'))
# A Rynk-like COBS frame, a malformed one, and stray bytes: host input is
# arbitrary for the property, so the replay covers both.
INPUT = bytes([0x03, 0x01, 0x02, 0x00]) + bytes([0x05, 0xff, 0x00]) + b'\x00\x00rmk\x00'
PORT = 9700 + os.getpid() % 200


def semihost_sites(elf):
    """Addresses of `ebreak` in `slli x0,x0,0x1f; ebreak; srai x0,x0,7`."""
    b = elf.read_bytes()
    phoff, = struct.unpack_from('<I', b, 28)
    count, = struct.unpack_from('<H', b, 44)
    sites = []
    for i in range(count):
        kind, off, vaddr, _, filesz, _, flags, _ = struct.unpack_from('<8I', b, phoff + 32 * i)
        if kind != 1 or not flags & 1:
            continue
        seg = b[off:off + filesz]
        for k in range(0, len(seg) - 11, 2):
            if struct.unpack_from('<3I', seg, k) == (0x01f01013, 0x00100073, 0x40705013):
                sites.append(vaddr + k + 4)
    return sites


def main():
    if not ELF.is_file():
        sys.exit('set RMK_ELF to the pinned qemu-riscv-rynk release ELF')
    sha = hashlib.sha256(ELF.read_bytes()).hexdigest()
    if sha != PIN:
        sys.exit(f'{ELF}: sha256 {sha}, expected the pinned {PIN}')
    WORK.mkdir(parents=True, exist_ok=True)
    log = WORK / 'qemu.log'
    args = [QEMU, '-M', 'virt', '-cpu', 'rv32', '-semihosting', '-nographic', '-bios', 'none',
            '-kernel', ELF, '-serial', f'tcp:127.0.0.1:{PORT},server,nowait',
            '-accel', 'tcg,one-insn-per-tb=on', '-icount', 'shift=4', '-d', 'cpu,int,nochain',
            '-trace', 'memory_region_ops_read', '-trace', 'memory_region_ops_write', '-D', log]
    if 'QEMU_DATA' in os.environ:
        args += ['-L', os.environ['QEMU_DATA']]
    proc = subprocess.Popen([str(a) for a in args], stdin=subprocess.DEVNULL,
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        # Connect once the firmware is up, then send the input byte by byte.
        time.sleep(1.5)
        with socket.create_connection(('127.0.0.1', PORT), timeout=5) as s:
            for x in INPUT:
                s.sendall(bytes([x]))
                time.sleep(0.05)
            time.sleep(1.5)
    finally:
        proc.kill()
        proc.wait()
    trace = WORK / 'trace.txt'
    subprocess.run(['python3', VERIFY / 'tools/qemu_trace.py', log, trace, str(STATES),
                    '--start', '0x80000000'], check=True)
    log.unlink()
    subprocess.run(['python3', VERIFY / 'tools/pack_elf.py', ELF,
                    VERIFY / 'Projects/rmk/QemuRiscvRynk/Image.lean', 'Rmk.QemuRiscvRynk'], check=True)
    subprocess.run(['lake', 'build', 'replay_virt'], cwd=VERIFY, check=True, stdout=subprocess.DEVNULL)
    sites = semihost_sites(ELF)
    print(f'semihosting sites: {[hex(a) for a in sites]}')
    out = subprocess.run([VERIFY / '.lake/build/bin/replay_virt', trace] + [str(a) for a in sites],
                         capture_output=True, text=True)
    print(out.stdout.strip())
    if out.returncode != 0:
        sys.exit(f'model and QEMU disagree:\n{out.stderr}')
    tx = [int(x) for x in out.stdout.split('[')[-1].rstrip(']\n').split(',') if x.strip()]
    rx = sum(1 for line in trace.read_text().splitlines() if line.startswith('R 10000000 '))
    print(f'UART: {rx} receive-register reads, {len(tx)} transmit-register writes {tx}')
    if rx == 0:
        sys.exit('the firmware never read the UART receive register: the input was not consumed')


if __name__ == '__main__':
    main()
