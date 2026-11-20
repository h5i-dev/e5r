#!/usr/bin/env python3
"""Run the hand-written memset (examples/elf/memset.elf, assembled from
examples/asm/memset.s) under qemu-riscv64 on random payloads: the payload
must come back as copies of its first byte, and the 16 bytes after it zero.

    python3 -I examples/asm/test.py [ELF] [N]
"""
import os, random, subprocess, sys

QEMU = os.environ.get("QEMU_RISCV64", "qemu-riscv64-static")
here = os.path.dirname(os.path.abspath(__file__))
elf = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "../elf/memset.elf")
n = int(sys.argv[2]) if len(sys.argv) > 2 else 300
rng = random.Random(7)
bad = 0
for k in range(n):
    size = rng.choice([1, 2, 3, 8, 9, rng.randrange(1, 2048)])
    data = bytes(rng.randrange(256) for _ in range(size))
    out = subprocess.run([QEMU, elf], input=data, capture_output=True, check=True).stdout
    want = bytes([data[0]]) * size + bytes(16)
    if out != want:
        bad += 1
        if bad <= 3:
            print(f"FAIL size {size}: got {out[:32].hex()}..., want {want[:32].hex()}...")
print(f"{'ok  ' if not bad else 'FAIL'} memset under qemu: {n - bad}/{n}")
sys.exit(1 if bad else 0)
