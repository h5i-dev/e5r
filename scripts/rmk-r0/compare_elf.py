#!/usr/bin/env python3
"""Compare two builds of the same RISC-V firmware: what differs, and where.

Usage: python3 -I scripts/rmk-r0/compare_elf.py OLD.elf NEW.elf [--json OUT] [--focus NAME ...]

Uses llvm-nm and llvm-objdump from the pinned Rust toolchain
(RUSTUP_TOOLCHAIN=1.98.1, llvm-tools). Reports:
  * ELF header fields, program headers, and per allocated section: address,
    size, sha256, and the number of differing bytes when sizes agree;
  * functions matched by demangled name (crate disambiguator hashes, which
    follow the build path, are not part of llvm-nm's demangling; several
    instances with one name are paired in address order), each classified
      same-bytes        identical bytes (it may have moved),
      same-up-to-imm    same size and the same instruction sequence with
                        numeric immediates/offsets removed (address-dependent
                        constants: pc-relative offsets, absolute addresses),
      different         anything else,
    plus functions present in only one build;
  * for each --focus name, its address, size and class in both builds.
It describes differences; it proves nothing about either binary.
"""
import collections
import hashlib
import json
import os
import re
import struct
import subprocess
import sys

TOOLS = os.path.join(
    subprocess.run(["rustc", "--print", "sysroot"], capture_output=True, text=True,
                   env={**os.environ, "RUSTUP_TOOLCHAIN": "1.98.1"}, check=True).stdout.strip(),
    "lib/rustlib/x86_64-unknown-linux-gnu/bin")


def sections(data):
    shoff, = struct.unpack_from("<I", data, 32)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 46)
    hdrs = [struct.unpack_from("<10I", data, shoff + i * shentsize) for i in range(shnum)]
    stroff = hdrs[shstrndx][4]
    out = {}
    for h in hdrs:
        name = data[stroff + h[0]:data.index(b"\0", stroff + h[0])].decode()
        if h[2] & 2:  # SHF_ALLOC
            body = data[h[4]:h[4] + h[5]] if h[1] != 8 else b""  # SHT_NOBITS has no bytes
            out[name] = {"addr": h[3], "size": h[5], "nobits": h[1] == 8, "bytes": body}
    return out


def phdrs(data):
    phoff, = struct.unpack_from("<I", data, 28)
    n, = struct.unpack_from("<H", data, 44)
    return [struct.unpack_from("<8I", data, phoff + 32 * i) for i in range(n)]


LLVM_SUFFIX = re.compile(r" \(\.llvm\.\d+\)$")


def functions(path):
    out = subprocess.run([f"{TOOLS}/llvm-nm", "--demangle", "-S", "--defined-only", path],
                         capture_output=True, text=True, check=True).stdout
    funcs = collections.defaultdict(list)
    for line in out.splitlines():
        parts = line.split(" ", 3)
        if len(parts) == 4 and parts[2].lower() == "t":
            # `.llvm.<hash>` marks a promoted local; the hash follows the module
            # (and so the build path), not the code.
            name = LLVM_SUFFIX.sub("", parts[3])
            funcs[name].append((int(parts[0], 16), int(parts[1], 16)))
    for v in funcs.values():
        v.sort()
    return funcs


def text_bytes(data, secs, addr, size):
    for s in secs.values():
        if not s["nobits"] and s["addr"] <= addr and addr + size <= s["addr"] + s["size"]:
            off = addr - s["addr"]
            return s["bytes"][off:off + size]
    return None


JALR0 = re.compile(r"^jalr\t(\w+)((?: #)?)$")
IMM = re.compile(r"(-?0x[0-9a-f]+|-?\b\d+\b|<[^>]*>)")


def insns(path, addr, size):
    """Instructions as text, labels removed (they carry crate hashes)."""
    out = subprocess.run([f"{TOOLS}/llvm-objdump", "-d", "--no-show-raw-insn",
                          f"--start-address={addr:#x}", f"--stop-address={addr + size:#x}", path],
                         capture_output=True, text=True, check=True).stdout
    return [re.sub(r"\s*<[^>]*>", "", l).strip() for l in out.splitlines()
            if re.match(r"^\s*[0-9a-f]+:\s", l)]


def shape(path, addr, size):
    out = subprocess.run([f"{TOOLS}/llvm-objdump", "-d", "--no-show-raw-insn", "--no-leading-addr",
                          f"--start-address={addr:#x}", f"--stop-address={addr + size:#x}", path],
                         capture_output=True, text=True, check=True).stdout
    lines = [l.strip() for l in out.splitlines() if l.startswith("\t") or l.startswith("  ")]
    # objdump prints a zero-offset `jalr rs` without the offset.
    norm = [JALR0.sub(r"jalr\t#(\1)\2", IMM.sub("#", l.split("#")[0]).strip()) for l in lines if l]
    return norm


def main():
    a_path, b_path = sys.argv[1], sys.argv[2]
    args = sys.argv[3:]
    json_out = args[args.index("--json") + 1] if "--json" in args else None
    focus = [args[i + 1] for i, x in enumerate(args) if x == "--focus"]
    A, B = open(a_path, "rb").read(), open(b_path, "rb").read()
    report = {"old": {"path": a_path, "sha256": hashlib.sha256(A).hexdigest(), "size": len(A)},
              "new": {"path": b_path, "sha256": hashlib.sha256(B).hexdigest(), "size": len(B)}}
    print(f"old {report['old']['sha256']} {len(A)} B\nnew {report['new']['sha256']} {len(B)} B")
    ea, eb = struct.unpack_from("<I", A, 24)[0], struct.unpack_from("<I", B, 24)[0]
    print(f"entry {ea:#x} / {eb:#x}")
    report["phdrs"] = {"old": phdrs(A), "new": phdrs(B)}
    for pa, pb in zip(*report["phdrs"].values()):
        if pa != pb:
            print(f"PT diff: old {[hex(x) for x in pa]}\n         new {[hex(x) for x in pb]}")
    sa, sb = sections(A), sections(B)
    report["sections"] = {}
    print(f"{'section':12} {'old addr':>10} {'old size':>9} {'new addr':>10} {'new size':>9}  diff")
    for name in sorted(set(sa) | set(sb), key=lambda n: (sa.get(n) or sb.get(n))["addr"]):
        x, y = sa.get(name), sb.get(name)
        diff = None
        if x and y and x["size"] == y["size"] and not x["nobits"]:
            diff = sum(p != q for p, q in zip(x["bytes"], y["bytes"]))
        report["sections"][name] = {
            "old": x and {"addr": x["addr"], "size": x["size"],
                          "sha256": hashlib.sha256(x["bytes"]).hexdigest()},
            "new": y and {"addr": y["addr"], "size": y["size"],
                          "sha256": hashlib.sha256(y["bytes"]).hexdigest()},
            "differing_bytes": diff}
        f = lambda s, k: f"{s[k]:#x}" if s else "-"
        print(f"{name:12} {f(x, 'addr'):>10} {f(x, 'size'):>9} {f(y, 'addr'):>10} {f(y, 'size'):>9}  "
              f"{'same' if x and y and x['bytes'] == y['bytes'] else (diff if diff is not None else 'size/addr')}")
    fa, fb = functions(a_path), functions(b_path)
    classes = collections.Counter()
    rows = {}
    for name in sorted(set(fa) | set(fb)):
        xs, ys = fa.get(name, []), fb.get(name, [])
        if len(xs) != len(ys):
            classes["only-or-count-differs"] += max(len(xs), len(ys))
            rows[name] = {"old": xs, "new": ys, "class": "only-or-count-differs"}
            continue
        for k, ((xa, xn), (ya, yn)) in enumerate(zip(xs, ys)):
            bx, by = text_bytes(A, sa, xa, xn), text_bytes(B, sb, ya, yn)
            if bx is not None and bx == by:
                c = "same-bytes"
            elif xn == yn and shape(a_path, xa, xn) == shape(b_path, ya, yn):
                c = "same-up-to-imm"
            else:
                c = "different"
            classes[c] += 1
            rows[f"{name}#{k}" if len(xs) > 1 else name] = {
                "old": [xa, xn], "new": [ya, yn], "class": c, "moved": xa != ya}
    moved = sum(1 for r in rows.values() if r.get("moved"))
    print(f"functions: {dict(classes)}; moved: {moved}")
    report["function_classes"] = dict(classes)
    report["functions_moved"] = moved
    for name in focus:
        for k, r in rows.items():
            if k == name or k.startswith(name + "#"):
                fmt = lambda v: f"{v[0]:#x}+{v[1]:#x}" if v and isinstance(v[0], int) else str(v)
                line = f"focus {k}: old {fmt(r['old'])} new {fmt(r['new'])} {r['class']}"
                if r["class"] == "same-up-to-imm":
                    xi, yi = insns(a_path, *r["old"]), insns(b_path, *r["new"])
                    d = [(x, y) for x, y in zip(xi, yi) if x.split(":", 1)[1] != y.split(":", 1)[1]]
                    r["differing_insns"] = d
                    line += f", {len(d)} of {len(xi)} instructions differ"
                print(line)
                for x, y in r.get("differing_insns", [])[:int(os.environ.get("SHOW", "0"))]:
                    print(f"    {x}  |  {y}")
    report["focus"] = {k: r for k, r in rows.items() if any(k == n or k.startswith(n + "#") for n in focus)}
    report["different"] = sorted(k for k, r in rows.items() if r["class"] != "same-bytes"
                                 and r["class"] != "same-up-to-imm")
    if json_out:
        json.dump(report, open(json_out, "w"), indent=1, default=str)


main()
