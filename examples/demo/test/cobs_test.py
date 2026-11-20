#!/usr/bin/env python3
"""Differential test of cobs_decode (examples/demo/cobs/cobs.c) under qemu-riscv64.

    python3 -I examples/demo/test/cobs_test.py TEST_ELF PROOF_ELF [N]

TEST_ELF links cobs.c with cobs_test_main.c; PROOF_ELF is examples/demo/elf/cobs.{a,b}.elf.
First checks that cobs_decode has the same bytes in both, so what is tested
is what is proved. Then feeds N random and edge-case buffers through the
binary and compares the report and the whole buffer afterwards with an
independent reference decoder, and checks round trips with an encoder."""
import os, random, struct, subprocess, sys

QEMU = os.environ.get("QEMU_RISCV64", "qemu-riscv64-static")


def func_bytes(elf, name):
    b = open(elf, "rb").read()
    shoff, = struct.unpack_from("<Q", b, 40)
    shentsize, shnum, _ = struct.unpack_from("<HHH", b, 58)
    secs = [struct.unpack_from("<IIQQQQIIQQ", b, shoff + i * shentsize) for i in range(shnum)]
    for nm, typ, _, _, off, size, link, _, _, ent in secs:
        if typ != 2:  # SHT_SYMTAB
            continue
        stroff = secs[link][4]
        for k in range(size // ent):
            st_name, info, _, shndx, value, sz = struct.unpack_from("<IBBHQQ", b, off + k * ent)
            if b[stroff + st_name:].split(b"\0")[0] == name.encode():
                t = secs[shndx]
                return b[t[4] + value - t[3]: t[4] + value - t[3] + sz]
    raise SystemExit(f"{name} not in {elf}")


def encode(data):
    """Standard COBS encoding of `data` (no delimiter)."""
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
    out += bytes([len(block) + 1]) + block
    return bytes(out)


def reference(buf):
    """The crate's decode_in_place_report: (tag, a, b), and the buffer after."""
    if not buf:
        return (1, 0, None), buf
    n = buf.index(0) if 0 in buf else len(buf)
    out, i = bytearray(), 0
    while i < n:
        code = buf[i]
        if i + code > n:
            return (1, 1, len(out)), bytes(out) + buf[len(out):]
        out += buf[i + 1:i + code]
        i += code
        if code != 0xFF and i < n:
            out.append(0)
    return (0, n, len(out)), bytes(out) + buf[len(out):]


def cases(rng, count):
    yield b""
    for n in range(0, 8):
        for _ in range(40):
            yield bytes(rng.choice([0, 1, 2, 3, 255, rng.randrange(256)]) for _ in range(n))
    for n in [253, 254, 255, 256, 507, 508, 509, 1000]:
        yield bytes([255] + [7] * 254) * 2
        yield encode(bytes(rng.randrange(1, 256) for _ in range(n)))
        yield encode(bytes(n))
    while True:
        k = rng.random()
        n = rng.choice([rng.randrange(20), rng.randrange(600), rng.randrange(3000)])
        if k < 0.4:  # a valid frame, maybe delimited, maybe followed by junk
            data = bytes(rng.choice([0, rng.randrange(256)]) for _ in range(n))
            f = encode(data)
            if rng.random() < 0.5:
                f += b"\0" + bytes(rng.randrange(256) for _ in range(rng.randrange(10)))
            yield f
        elif k < 0.6:  # a valid frame with one byte changed
            f = bytearray(encode(bytes(rng.randrange(256) for _ in range(n + 1))))
            f[rng.randrange(len(f))] = rng.randrange(256)
            yield bytes(f)
        else:  # junk with few zeros
            yield bytes(rng.choice([rng.randrange(1, 256)] * 9 + [0]) for _ in range(n))


def main():
    test_elf, proof_elf = sys.argv[1], sys.argv[2]
    count = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    a, b = func_bytes(test_elf, "cobs_decode"), func_bytes(proof_elf, "cobs_decode")
    if a != b:
        raise SystemExit("FAIL cobs_decode differs between the test and the proof binary")
    rng = random.Random(0xC0B5)
    inputs, gen = [], cases(rng, count)
    while len(inputs) < count:
        inputs.append(next(gen))
    stdin = b"".join(struct.pack("<Q", len(x)) + x for x in inputs)
    p = subprocess.run([QEMU, test_elf], input=stdin, capture_output=True, timeout=600)
    if p.returncode != 0:
        raise SystemExit(f"FAIL qemu exit {p.returncode}")
    out, pos, stats = p.stdout, 0, {"empty": 0, "invalid": 0, "ok": 0, "roundtrip": 0}
    for x in inputs:
        tag, ra, rb = struct.unpack_from("<QQQ", out, pos)
        got = out[pos + 24: pos + 24 + len(x)]
        pos += 24 + len(x)
        (etag, ea, eb), ebuf = reference(x)
        if eb is None:
            eb = 0xCCCCCCCCCCCCCCCC  # untouched
        if (tag, ra, rb) != (etag, ea, eb) or got != ebuf:
            raise SystemExit(f"FAIL on {x.hex()}: got {(tag, ra, rb)} {got.hex()}, "
                             f"want {(etag, ea, eb)} {ebuf.hex()}")
        stats["empty" if not x else "ok" if tag == 0 else "invalid"] += 1
    assert pos == len(out)
    # Round trips: decode(encode(d)) = d for data with no delimiter issue.
    datas = [bytes(rng.choice([0, rng.randrange(256)]) for _ in range(rng.randrange(1500)))
             for _ in range(2000)]
    stdin = b"".join(struct.pack("<Q", len(encode(d))) + encode(d) for d in datas)
    p = subprocess.run([QEMU, test_elf], input=stdin, capture_output=True, timeout=600)
    pos = 0
    for d in datas:
        e = encode(d)
        tag, ra, rb = struct.unpack_from("<QQQ", p.stdout, pos)
        got = p.stdout[pos + 24: pos + 24 + len(e)]
        pos += 24 + len(e)
        if (tag, ra, rb) != (0, len(e), len(d)) or got[:len(d)] != d:
            raise SystemExit(f"FAIL round trip of {d.hex()}")
        stats["roundtrip"] += 1
    print(f"ok   cobs_decode matches the reference on {len(inputs)} buffers "
          f"({stats['ok']} valid, {stats['invalid']} invalid, {stats['empty']} empty) "
          f"and {stats['roundtrip']} encode/decode round trips")


main()
