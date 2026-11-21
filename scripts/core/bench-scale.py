#!/usr/bin/env python3
"""The scale benchmark (docs/isa/v1-results.md, criterion 7'): a real rustc-built
artifact, checked and refined function by function.

    python3 -I scripts/core/bench-scale.py A.elf B.elf [--json OUT]

A and B are two builds of the same artifact (examples/refine/conformance.sh
builds one): B an identical rebuild, or B with a small edit. Reports
  checker   `nocompiler check --json A` over every function: wall time,
            functions, instructions, levels;
  bytes     per function, whether its words are the same in A and B (what a
            function-granularity discharge needs: one comparison per function);
  refine    per function at L1 or above in A, `nocompiler refine A B f`
            (the tree diff and certificate, Rust): wall time, instructions
            paired in lockstep, changed intervals; totals split into functions
            whose bytes are equal and those that changed.
NOCOMPILER names the binary (default target/release/nocompiler).
"""
import json, os, subprocess, sys, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
NOCOMPILER = os.environ.get("NOCOMPILER", os.path.join(ROOT, "target", "release", "nocompiler"))


def run(args):
    t0 = time.monotonic()
    r = subprocess.run(args, capture_output=True, text=True)
    return r, time.monotonic() - t0


def text_and_symbols(elf):
    """.text bytes and its address, and every function symbol (name, address, size)."""
    sec = subprocess.run(["llvm-readelf", "-S", "-W", elf], check=True, capture_output=True, text=True).stdout
    line = next(l for l in sec.splitlines() if " .text " in l)
    f = line.split("]", 1)[1].split()
    addr, off, size = int(f[2], 16), int(f[3], 16), int(f[4], 16)
    data = open(elf, "rb").read()[off:off + size]
    nm = subprocess.run(["llvm-nm", "--print-size", "--defined-only", elf], check=True, capture_output=True,
                        text=True).stdout
    syms = {}
    for l in nm.splitlines():
        p = l.split()
        if len(p) == 4 and p[2] in "Tt":
            syms[p[3]] = (int(p[0], 16), int(p[1], 16))
    return addr, data, syms


def words(text, sym):
    base, data = text
    a, n = sym
    return data[a - base:a - base + n]


def main():
    a_elf, b_elf = sys.argv[1], sys.argv[2]
    out = {}
    r, t = run([NOCOMPILER, "check", "--json", a_elf])
    funcs = json.loads(r.stdout)["functions"]
    ta, sa = (lambda x: ((x[0], x[1]), x[2]))(text_and_symbols(a_elf))
    tb, sb = (lambda x: ((x[0], x[1]), x[2]))(text_and_symbols(b_elf))
    instrs = len(ta[1]) // 4
    levels = {}
    for f in funcs:
        levels[str(f.get("level"))] = levels.get(str(f.get("level")), 0) + 1
    out["checker"] = {"seconds": round(t, 3), "functions": len(funcs), "instructions": instrs, "levels": levels,
                      "us_per_instr": round(1e6 * t / instrs, 2)}
    t0 = time.monotonic()
    same = {n: (n in sb and words(ta, sa[n]) == words(tb, sb[n])) for n in sa}
    out["bytes"] = {"seconds": round(time.monotonic() - t0, 4), "functions": len(sa),
                    "equal": sum(same.values()), "changed_or_missing": [n for n, v in same.items() if not v]}
    rows = []
    for f in funcs:
        if f.get("level") not in ("L1", "L2"):
            continue
        n = f["name"]
        r, t = run([NOCOMPILER, "refine", a_elf, b_elf, n])
        msg = (r.stdout + r.stderr).strip().splitlines()
        head = next((l for l in msg if "instructions paired" in l), "")
        paired = int(head.split()[0]) if head else None
        changed = int(head.split(";")[1].split()[0]) if "changed interval" in head else None
        differs = sum(1 for l in msg if "DIFFERS" in l)
        rows.append({"name": n, "seconds": round(t, 3), "rc": r.returncode, "paired": paired, "changed": changed,
                     "bytes_equal": same.get(n, False), "instructions": sa.get(n, (0, 0))[1] // 4,
                     "regions_differ": differs, "error": msg[-1] if r.returncode != 0 and msg else None})
    eq = [x for x in rows if x["bytes_equal"]]
    ne = [x for x in rows if not x["bytes_equal"]]
    def summ(xs):
        return {"functions": len(xs), "instructions": sum(x["instructions"] for x in xs),
                "seconds": round(sum(x["seconds"] for x in xs), 2),
                "failed": [x["name"] for x in xs if x["rc"] != 0],
                "with_changed_intervals": [x["name"] for x in xs if x["changed"]],
                "with_differing_regions": [x["name"] for x in xs if x["regions_differ"]],
                "paired_instructions": sum(x["paired"] or 0 for x in xs)}
    out["refine"] = {"bytes_equal": summ(eq), "changed": summ(ne)}
    out["refine_changed_rows"] = ne
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)
    c = out["checker"]
    print(f"checker: {c['functions']} functions, {c['instructions']} instructions, {c['seconds']} s "
          f"({c['us_per_instr']} us/instr), levels {c['levels']}")
    b = out["bytes"]
    print(f"bytes: {b['equal']} of {b['functions']} functions byte-equal in A and B; compared in {b['seconds']} s; "
          f"changed or missing: {b['changed_or_missing'][:10]}")
    for k, v in out["refine"].items():
        print(f"refine ({k}): {v['functions']} functions, {v['instructions']} instructions, {v['seconds']} s; "
              f"failed {len(v['failed'])}; with changed intervals {len(v['with_changed_intervals'])}; "
              f"with a region that differs {len(v['with_differing_regions'])}; "
              f"instructions paired {v['paired_instructions']}")
    return 0


sys.exit(main())
