#!/usr/bin/env python3
"""The extension's semantics (lean/NoCompiler/Ext/Rvc.lean) against qemu-riscv64, on
the compressed cobs_decode the proof is about.

    python3 -I examples/demo/test/rvc_exec.py RVC_RUN TEST_ELF PROOF_ELF ENTRY [N]

RVC_RUN is the `rvc-run` executable (lean/RvcRun.lean): it runs PROOF_ELF's
function at ENTRY with CCode.instr and execC. TEST_ELF links the same
cobs_decode (same bytes, checked by examples/demo/test/cobs_test.py) with a driver,
run under qemu. Both get the same N buffers; the 24-byte result slot and the
buffer afterwards must be equal byte for byte."""
import os, random, struct, subprocess, sys

QEMU = os.environ.get("QEMU_RISCV64", "qemu-riscv64-static")


def encode(data):
    out, block = bytearray(), bytearray()
    for x in data:
        if x == 0:
            out += bytes([len(block) + 1]) + block
            block = bytearray()
        else:
            block.append(x)
            if len(block) == 254:
                out += bytes([255]) + block
                block = bytearray()
    return bytes(out + bytes([len(block) + 1]) + block)


def inputs(rng, n):
    out = [b"", b"\0", b"\1", b"\2\x05", bytes([255] + [7] * 254) * 2]
    while len(out) < n:
        k, m = rng.random(), rng.choice([rng.randrange(16), rng.randrange(300), rng.randrange(1200)])
        if k < 0.4:
            out.append(encode(bytes(rng.choice([0, rng.randrange(256)]) for _ in range(m))) + b"\0")
        elif k < 0.7:
            f = bytearray(encode(bytes(rng.randrange(256) for _ in range(m + 1))))
            f[rng.randrange(len(f))] = rng.randrange(256)
            out.append(bytes(f))
        else:
            out.append(bytes(rng.choice([rng.randrange(1, 256)] * 9 + [0]) for _ in range(m)))
    return out


def main():
    run, test_elf, proof_elf, entry = sys.argv[1:5]
    n = int(sys.argv[5]) if len(sys.argv) > 5 else 3000
    xs = inputs(random.Random(0xC0DE), n)
    stdin = b"".join(struct.pack("<Q", len(x)) + x for x in xs)
    q = subprocess.run([QEMU, test_elf], input=stdin, capture_output=True, timeout=600)
    l = subprocess.run([run, proof_elf, str(int(entry, 0))], input=stdin, capture_output=True, timeout=1800)
    if q.returncode or l.returncode:
        raise SystemExit(f"FAIL qemu {q.returncode}, lean {l.returncode}: {l.stderr.decode()[:200]}")
    pos = 0
    for x in xs:
        a, b = q.stdout[pos:pos + 24 + len(x)], l.stdout[pos:pos + 24 + len(x)]
        if a != b:
            raise SystemExit(f"FAIL on {x.hex()[:80]}: qemu {a.hex()[:80]}, lean {b.hex()[:80]}")
        pos += 24 + len(x)
    assert pos == len(q.stdout) == len(l.stdout)
    print(f"ok   execC and qemu agree on the compressed cobs_decode for {n} buffers")


main()
