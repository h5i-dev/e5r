#!/usr/bin/env python3
"""decodeC (lean/NoCompiler/Ext/Rvc.lean) against llvm-mc, on every 16-bit word.

    python3 -I examples/demo/test/rvc_decode.py TABLE

TABLE is examples/demo/tools/RvcTable.lean's output: for each halfword h (low bits
not 11), `h none` or `h w`, w the 32-bit word of the instruction decodeC
gives (checked there to decode to it). For each h, llvm-mc disassembles h
with the C extension and w without it; the texts must be equal. Where
decodeC gives none, llvm-mc must reject h or decode it to something the
extension leaves out on purpose (floating point, c.ebreak, unimp)."""
import re, subprocess, sys

EXCLUDED = ("fld", "fsd", "flw", "fsw", "ebreak", "c.ebreak", "unimp", "c.unimp", "fldsp", "fsdsp")


def canon(t):
    """llvm prints some compressed instructions (aliases, HINTs) in forms that
    differ from how it prints their 32-bit expansions; spell them out."""
    if t is None:
        return t
    op, _, rest = t.partition(" ")
    a = [x.strip() for x in rest.split(",")] if rest else []
    if op in ("mv", "c.mv"):
        return f"add {a[0]}, zero, {a[1]}"
    if op == "c.add":
        return f"add {a[0]}, {a[0]}, {a[1]}"
    if op in ("c.slli", "c.srli", "c.srai"):
        return f"{op[2:]} {a[0]}, {a[0]}, {a[1]}"
    if op in ("c.slli64", "c.srli64", "c.srai64"):
        return f"{op[2:-2]} {a[0]}, {a[0]}, 0"
    if op == "c.nop":
        return f"li zero, {a[0]}" if a else "nop"
    if op == "c.li":
        return "nop" if a == ["zero", "0"] else f"li {a[0]}, {a[1]}"
    if op == "c.lui":
        return f"lui {a[0]}, {int(a[1]) % (1 << 20)}"
    return t


# Reserved encodings llvm-mc decodes anyway and decodeC rejects (the
# conservative side: code using them cannot be proved): C.LUI with nzimm = 0.
def reserved(h):
    return (h & 0xE003) == 0x6001 and ((h >> 7) & 31) != 2 and (h & 0x107C) == 0


def mc(words, nbytes, attrs):
    """Disassemble each word on its own; returns one text (or None) per word."""
    lines = []
    for w in words:
        lines.append(" ".join(f"0x{(w >> (8 * k)) & 0xff:02x}" for k in range(nbytes)))
    src = "\n".join(lines) + "\n"
    p = subprocess.run(["llvm-mc", "--disassemble", "-triple=riscv64", f"-mattr={attrs}"],
                       input=src, capture_output=True, text=True)
    bad = {int(m.group(1)) for m in re.finditer(r"<stdin>:(\d+):", p.stderr)}
    out = [l.strip() for l in p.stdout.splitlines() if l.startswith("\t") and not l.strip().startswith(".")]
    res, k = [], 0
    for i in range(len(words)):
        if i + 1 in bad:
            res.append(None)
        else:
            res.append(re.sub(r"\s+", " ", out[k]))
            k += 1
    assert k == len(out), (k, len(out))
    return res


def main():
    rows = [l.split(maxsplit=1) for l in open(sys.argv[1])]
    hs = [int(h) for h, _ in rows]
    c16 = mc(hs, 2, "+c,+d,+f,+zca")
    ok = mismatch = 0
    words = [int(v) for _, v in rows if v.strip().isdigit()]
    c32 = iter(mc(words, 4, "+m"))
    for (h, v), t16 in zip(rows, c16):
        h = int(h)
        v = v.strip()
        if v.isdigit():
            t32 = next(c32)
            if canon(t16) != canon(t32):
                print(f"MISMATCH {h:#06x}: llvm {t16!r}, decodeC {t32!r}")
                mismatch += 1
            else:
                ok += 1
        elif v == "none":
            if t16 is not None and t16.split()[0] not in EXCLUDED and not reserved(h):
                print(f"MISSING {h:#06x}: llvm decodes {t16!r}, decodeC gives none")
                mismatch += 1
            else:
                ok += 1
        else:
            print(f"BAD {h:#06x}: {v}")
            mismatch += 1
    print(f"{'ok  ' if mismatch == 0 else 'FAIL'} decodeC agrees with llvm-mc on {ok} of {len(rows)} halfwords")
    sys.exit(1 if mismatch else 0)


main()
