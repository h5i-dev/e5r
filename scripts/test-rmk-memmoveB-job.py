#!/usr/bin/env python3
"""Targeted mutations of the RMK memmove contractB job (jobs/rmk/rmk-memmove-contractB.json).

Usage: python3 -I scripts/test-rmk-memmoveB-job.py E5R_VERIFY

Proof mutations edit a COPY of Projects/rmk/MemmoveContract.lean (written to
verification/rv32/build/testjobs/MutContract.lean; the peer's file is not
touched) and run the job with the copy in its place. Each must end `failed`
(exit 10: Lean rejected the proof), with the first error inside the theorem
the mutation should break; `error` (exit 13) would be a tool or job problem,
not a rejection, and counts as a test failure. The unmutated copy, run the
same way, must be `proved` (so the copy mechanism itself is sound). One
mutation changes an instruction of the aligned word loop in the ELF.

  control        the unmodified copy                         -> proved
  no-residue     PreB without src ≡ dst (mod 4)              -> failed in contractB
  no-direction   PreB without "forward" (dst - src ≥ n)      -> failed in contractB
  no-stack-sep   PreB.dstSep weakened to True                -> failed in contractB
  wrong-post     PostB claims a1 is preserved                -> failed in finishB
  loop-insn      ELF: 0x80020ec4 `sw a2,0(t5)` -> `sw a3,0(t5)`, unpinned
                                                             -> failed at that instruction fact
  tool-error     a job module that does not exist            -> error (not a rejection)
Runs use one job id and `--resume`, so unchanged modules are not recompiled.
"""
import json
import os
import re
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verification", "rv32")
T = os.path.join(ROOT, "build", "testjobs")
JOB = json.load(open(os.path.join(ROOT, "jobs", "rmk", "rmk-memmove-contractB.json")))
SRC = open(os.path.join(ROOT, "Projects", "rmk", "MemmoveContract.lean"), encoding="utf-8").read()
MUT = "build/testjobs/MutContract.lean"
failures = 0


def enclosing(text, line):
    """The theorem/def whose body contains `line` (1-based)."""
    for l in reversed(text.splitlines()[:line]):
        m = re.match(r"(?:theorem|def|structure) (\S+)", l)
        if m:
            return m.group(1)
    return "?"


def run(name, src=None, elf=None, modules=None):
    j = json.loads(json.dumps(JOB))
    j["id"], j["root"] = "rmk-memmoveB-neg", "../.."
    mods = [m for m in j["modules"] if not m.startswith("Projects/ramimage/")]
    if src is not None:
        open(os.path.join(ROOT, MUT), "w", encoding="utf-8").write(src)
        mods = [MUT if m == "Projects/rmk/MemmoveContract.lean" else m for m in mods]
    j["modules"] = modules or mods
    j["theorems"] = ["E5R.Rmk.Memmove.contractB"]
    if elf:
        j["elf"] = elf
        j.pop("elf_sha256")
    path = os.path.join(T, f"memmoveB-{name}.json")
    json.dump(j, open(path, "w"), indent=1)
    r = subprocess.run([TOOL, "check", "--resume", path], capture_output=True, text=True, cwd=ROOT)
    doc = json.loads(r.stdout) if r.stdout.strip().startswith("{") else {}
    return r.returncode, doc.get("status"), doc.get("message", r.stderr)


def expect(name, got, code, where=None, text=None, file=None):
    global failures
    rc, status, msg = got
    loc = re.search(rf"{re.escape(file or MUT)}:(\d+):\d+: error", msg or "") if code == 10 else None
    found = enclosing(text, int(loc.group(1))) if loc and text else None
    ok = rc == code and (where is None or found == where)
    failures += not ok
    first = next((l for l in (msg or "").splitlines() if "error" in l), (msg or "").splitlines()[0] if msg else "")
    print(f"{'ok' if ok else 'FAIL'} {name}: exit {rc} {status}"
          + (f", first error in {found}" if found else "") + f" | {first.strip()[:160]}")
    if not ok:
        print(f"   wanted exit {code}" + (f" with the error in {where}" if where else "") + f"\n{(msg or '')[-1500:]}")


def mutate(old, new):
    assert SRC.count(old) == 1, old
    return SRC.replace(old, new)


def main():
    global TOOL
    TOOL = os.path.abspath(sys.argv[1])
    os.makedirs(T, exist_ok=True)
    expect("control: unmodified copy", run("control", src=SRC), 0)
    cases = [
        ("no-residue", mutate(" ∧\n      (m.core.get 11).toNat % 4 = (m.core.get 10).toNat % 4)", ")"),
         "contractB"),
        ("no-direction", mutate("((m.core.get 10 - m.core.get 11).ult (m.core.get 12) = false ∧\n      ", "("),
         "contractB"),
        ("no-stack-sep", mutate("  dstSep : (m.core.get 2).toNat ≤ (m.core.get 10).toNat ∨\n"
                                "    (m.core.get 10).toNat + (m.core.get 12).toNat + 12 ≤ (m.core.get 2).toNat\n",
                                "  dstSep : True\n"), "contractB"),
        ("wrong-post", mutate("r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] →",
                              "r.val ∉ [5, 6, 7, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] →"), "finishB"),
    ]
    for name, src, where in cases:
        expect(name, run(name, src=src), 10, where, src)
    elf = bytearray(open(os.path.join(ROOT, JOB["elf"]), "rb").read())
    off = 0x1000 + (0x80020ec4 - 0x80000000)
    assert elf[off:off + 4] == bytes.fromhex("2320cf00"), elf[off:off + 4].hex()  # sw a2,0(t5)
    elf[off + 2] = 0xdf  # rs2 12 -> 13: sw a3,0(t5)
    open(os.path.join(T, "memmoveB-loop.elf"), "wb").write(elf)
    fetch = open(os.path.join(ROOT, "Projects/rmk/MemmoveFetch.lean"), encoding="utf-8").read()
    expect("loop-insn", run("loop", elf="build/testjobs/memmoveB-loop.elf"), 10, "f80020ec4", fetch,
           "Projects/rmk/MemmoveFetch.lean")
    expect("tool-error: missing module", run("missing", modules=JOB["modules"][:-1] + ["build/testjobs/Nope.lean"]),
           13)
    print("all contractB mutations behaved as stated" if not failures else f"{failures} FAILED")
    sys.exit(1 if failures else 0)


main()
