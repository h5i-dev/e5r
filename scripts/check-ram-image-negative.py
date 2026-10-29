#!/usr/bin/env python3
"""Negative controls: malformed variants of a RAM-resident ELF must be refused
by both the Rust exporter and the checker's Lean reader.

Usage: python3 -I scripts/check-ram-image-negative.py E5R_VERIFY IMAGE.elf RV32_DIR [BASE SIZE]

Each mutation edits header fields of IMAGE.elf. For each: `E5R_VERIFY
ram-image` must exit non-zero and create nothing; the mutated file, packed
here (64-byte little-endian words, independently of the Rust packer), must
make the kernel decide `E5R.RamElf.accepts BASE SIZE f = false`. The
unmutated file is the positive control (`accepts = true`). Exit status 0
only if every expectation holds.
"""
import os
import struct
import subprocess
import sys
import tempfile


def u32(b, off, v):
    struct.pack_into("<I", b, off, v)


def get(b, off):
    return struct.unpack_from("<I", b, off)[0]


def ph(i, n):
    return 52 + 32 * i + n


def loads(b):
    return [i for i in range(struct.unpack_from("<H", b, 44)[0]) if get(b, ph(i, 0)) == 1]


def mutations(orig):
    L = loads(orig)
    first, second, last = L[0], L[1], L[-1]
    out = []

    def m(name, *edits, cut=None):
        b = bytearray(orig)
        for off, f in edits:
            u32(b, off, f(get(b, off)))
        out.append((name, bytes(b[:cut]) if cut else bytes(b)))

    m("load address != run address", (ph(second, 12), lambda v: v + 0x1000))
    m("writable and executable code", (ph(first, 24), lambda v: 7))
    m("read-only memsz overlaps the next segment", (ph(second, 20), lambda v: v + 0x100))
    m("odd entry", (24, lambda v: v | 1))
    m("entry outside every segment", (24, lambda v: 0x7ffffff0))
    m("segment past the end of RAM", (ph(last, 8), lambda v: v + 0x1000),
      (ph(last, 12), lambda v: v + 0x1000))
    m("file bytes past EOF", cut=get(orig, ph(first, 4)) + get(orig, ph(first, 16)) - 1)
    m("float ABI e_flags", (36, lambda v: 3))
    m("dynamic program header", (ph(L[-1] + 1, 0), lambda v: 2))
    m("p_filesz > p_memsz", (ph(second, 16), lambda v: get(orig, ph(second, 20)) + 4))
    m("writable segment below a read-only one", (ph(second, 24), lambda v: 6),
      (ph(L[2], 24), lambda v: 4))
    return out


def main():
    tool, elf, rv32 = sys.argv[1:4]
    base, size = (int(x, 0) for x in (sys.argv[4:6] or ["0x80000000", "0x1000000"]))
    orig = open(elf, "rb").read()
    toolchain = open(os.path.join(rv32, "lean-toolchain")).read().strip()
    cases = [("positive control (unmutated)", orig, True)] + \
            [(n, b, False) for n, b in mutations(orig)]
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "Theories"))
        env = {**os.environ, "LEAN_PATH": d}
        for mod in ["Hart", "Platform", "RamElf"]:
            subprocess.run(["elan", "run", toolchain, "lean", "-o",
                            os.path.join(d, "Theories", f"{mod}.olean"),
                            os.path.join(rv32, "Theories", f"{mod}.lean")], check=True, env=env)
        bad = 0
        for k, (name, b, want) in enumerate(cases):
            path = os.path.join(d, f"m{k}.elf")
            open(path, "wb").write(b)
            outdir = os.path.join(d, f"out{k}")
            r = subprocess.run([tool, "ram-image", "--ram", f"{base:#x}:{size:#x}", "--mapping",
                                "paddr=vaddr", "--out", outdir, path], capture_output=True,
                               text=True)
            rust_ok = r.returncode == 0
            if not rust_ok and os.path.exists(outdir):
                rust_ok = None  # refused but wrote output
            words = [str(int.from_bytes(b[i:i + 64], "little")) for i in range(0, len(b), 64)]
            src = os.path.join(d, f"M{k}.lean")
            open(src, "w").write(
                "import Theories.RamElf\nset_option maxRecDepth 100000\n"
                f"def f : E5R.RamElf.File := ⟨{len(b)}, [{', '.join(words)}]⟩\n"
                f"theorem t : E5R.RamElf.accepts {base} {size} f = {str(want).lower()} := "
                "by decide +kernel\n")
            lr = subprocess.run(["elan", "run", toolchain, "lean", src], capture_output=True,
                                text=True, env=env)
            lean_ok = lr.returncode == 0
            ok = rust_ok == want and lean_ok
            bad += not ok
            why = r.stderr.strip().removeprefix("e5r-verify: ") if not rust_ok else "accepted"
            print(f"{'ok' if ok else 'FAIL'} {name}: rust {why!r}; "
                  f"lean kernel accepts = {str(want).lower()} {'proved' if lean_ok else 'NOT proved'}")
            if not lean_ok:
                print(lr.stdout[-600:])
    sys.exit(1 if bad else 0)


main()
