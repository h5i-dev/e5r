#!/usr/bin/env python3
"""Negative controls for the COBS decoder job (jobs/rmk/rmk-cobs-decode.json): both
contracts, `E5R.Rmk.Cobs.decode` (decode_in_place_report) and `decode_in_place`.

Usage: python3 -I scripts/test-rmk-cobs-job.py E5R_VERIFY

Proof mutations edit COPIES of Projects/rmk/Cobs/{Basic,Empty,Scan,Copy,Spec,Loop,Decode,
Wrapper}.lean, written to verification/rv32/build/testjobs/cobsmut/ with their imports
renamed (the originals are untouched), and run the job with the copies in place of the
originals (same id, --resume, so the shared Fetch modules are not rebuilt). A mutation is
REJECTED only if the run ends `failed` (exit 10: Lean rejected a proof) and its first error
is inside a theorem of a mutated-chain file, not an import/unknown-identifier error. `error`
(exit 13) is a tool or job problem and counts as a test failure, except for the tool-error
control, which must be exactly that.

  control         unmodified copies                                     -> proved
  read-guard      Spec.block: invalid iff n <= src + code (was n <)      -> rejected
  tag             Res: success tag word 1, failure 0 (swapped)          -> rejected
  length          Res: [a0+8] = decoded length + 1                      -> rejected
  separation      CobsEnv.bufFrame := True (buffer may overlap frame)   -> rejected
  wrapper-ok      WRes: success word 0xfffffffe (was 0xffffffff)       -> rejected
  wrapper-frame   WEnv.outFrame := True (result may overlap frame)      -> rejected
  opcode          ELF: 0x8001e0b2 sb a5,0(s1) -> sb a4,0(s1), unpinned  -> rejected at that fact
  tool-error      a job module that does not exist                      -> error
"""
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verification", "rv32")
T = os.path.join(ROOT, "build", "testjobs")
MUT = os.path.join(T, "cobsmut")
JOB = json.load(open(os.path.join(ROOT, "jobs", "rmk", "rmk-cobs-decode.json")))
CHAIN = ["Basic", "Empty", "Scan", "Copy", "Spec", "Loop", "Decode", "Wrapper"]
SRC = {m: open(os.path.join(ROOT, "Projects/rmk/Cobs", m + ".lean"), encoding="utf-8").read() for m in CHAIN}
failures = 0


def write_chain(edits):
    """Copies of the chain with imports renamed, `edits` = {module: (old, new)} applied."""
    shutil.rmtree(MUT, ignore_errors=True)
    os.makedirs(MUT)
    for m in CHAIN:
        s = SRC[m]
        for o in CHAIN:
            s = s.replace(f"import Projects.rmk.Cobs.{o}\n", f"import build.testjobs.cobsmut.{o}\n")
        if m in edits:
            old, new = edits[m]
            assert s.count(old) == 1, (m, old)
            s = s.replace(old, new)
        open(os.path.join(MUT, m + ".lean"), "w", encoding="utf-8").write(s)


def run(name, chain=True, elf=None, modules=None):
    j = json.loads(json.dumps(JOB))
    j["id"], j["root"] = "rmk-cobs-neg", "../.."
    mods = [m for m in j["modules"] if not m.startswith("Projects/ramimage/")]
    if chain:
        mods = [f"build/testjobs/cobsmut/{m[len('Projects/rmk/Cobs/'):]}"
                if m[len("Projects/rmk/Cobs/"):-5] in CHAIN and m.startswith("Projects/rmk/Cobs/") else m
                for m in mods]
    j["modules"] = modules or mods
    j["theorems"] = ["E5R.Rmk.Cobs.decode", "E5R.Rmk.Cobs.decode_in_place"]
    if elf:
        j["elf"] = elf
        j.pop("elf_sha256")
    path = os.path.join(T, f"cobs-{name}.json")
    json.dump(j, open(path, "w"), indent=1)
    r = subprocess.run([TOOL, "check", "--resume", path], capture_output=True, text=True, cwd=ROOT)
    doc = json.loads(r.stdout) if r.stdout.strip().startswith("{") else {}
    return r.returncode, doc.get("status"), doc.get("message", r.stderr)


def first_error(msg):
    m = re.search(r"((?:build/testjobs/cobsmut|Projects/rmk/Cobs)/\w+\.lean):(\d+):\d+: error[^\n]*", msg or "")
    if not m:
        return None, None, None
    path, line = m.group(1), int(m.group(2))
    text = open(os.path.join(ROOT, path), encoding="utf-8").read().splitlines()
    thm = next((re.match(r"(?:theorem|def|structure) (\S+)", l).group(1) for l in reversed(text[:line])
                if re.match(r"(?:theorem|def|structure) \S+", l)), "?")
    return path, thm, m.group(0)


def full_errors(msg):
    """The runner keeps only the tail of Lean's output; for a failed module, rerun Lean on it
    (its imports are the job's, already built) and keep only error lines."""
    m = re.search(r"((?:build/testjobs/cobsmut|Projects/rmk/Cobs)/\w+\.lean): exited with", msg or "")
    if not m:
        return msg
    r = subprocess.run(["lean", "-j1", m.group(1)], cwd=ROOT, capture_output=True, text=True,
                       env={**os.environ, "LEAN_PATH": "."})
    out = r.stdout + r.stderr
    return "\n".join(l for l in out.splitlines() if ": error" in l) or msg


def expect(name, got, code):
    global failures
    rc, status, msg = got
    if code == 10 and rc == 10:
        msg = full_errors(msg)
    path, thm, line = first_error(msg) if code == 10 else (None, None, None)
    bad_kind = code == 10 and (line is None or re.search(r"unknown (identifier|module|constant)|import", line or ""))
    ok = rc == code and not bad_kind
    failures += not ok
    where = f" first error in {path} ({thm})" if path else ""
    print(f"{'ok' if ok else 'FAIL'} {name}: exit {rc} {status}{where} | {(line or (msg or '').strip().splitlines()[0] if msg else '')[:150]}")
    if not ok:
        print((msg or "")[-1500:])


def main():
    global TOOL
    TOOL = os.path.abspath(sys.argv[1])
    os.makedirs(T, exist_ok=True)
    write_chain({})
    expect("control: unmodified copies", run("control"), 0)
    cases = [
        ("read-guard", {"Spec": ("  if n < src + code then none", "  if n ≤ src + code then none")}),
        ("tag", {"Decode": ("ramRead m.ram a0 .w = (if r.1 = .ok then 0 else 1) ∧",
                            "ramRead m.ram a0 .w = (if r.1 = .ok then 1 else 0) ∧")}),
        ("length", {"Decode": ("ramRead m.ram (a0 + 8) .w = BitVec.ofNat 32 r.2.length ∧",
                               "ramRead m.ram (a0 + 8) .w = BitVec.ofNat 32 (r.2.length + 1) ∧")}),
        ("separation", {"Basic": ("  bufFrame : (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - 16 ∨\n"
                                  "    (m.core.get 2).toNat ≤ (m.core.get 11).toNat\n", "  bufFrame : True\n")}),
        ("wrapper-ok", {"Wrapper": ("(if r.1 = .ok then 0xffffffff#32 else 1)", "(if r.1 = .ok then 0xfffffffe#32 else 1)")}),
        ("wrapper-frame", {"Wrapper": ("  outFrame : (m.core.get 10).toNat + 8 ≤ (m.core.get 2).toNat - 48 ∨\n"
                                       "    (m.core.get 2).toNat ≤ (m.core.get 10).toNat\n", "  outFrame : True\n")}),
    ]
    for name, edits in cases:
        write_chain(edits)
        expect(name, run(name), 10)
    # one actual opcode: sb a5,0(s1) -> sb a4,0(s1) in the copy loop
    elf = bytearray(open(os.path.join(ROOT, JOB["elf"]), "rb").read())
    off = 0x1000 + (0x8001e0b2 - 0x80000000)
    w = int.from_bytes(elf[off:off + 4], "little")
    assert w == 0x00f48023, hex(w)
    elf[off:off + 4] = (w ^ (1 << 20)).to_bytes(4, "little")  # rs2 15 -> 14
    open(os.path.join(T, "cobs-opcode.elf"), "wb").write(elf)
    write_chain({})
    expect("opcode", run("opcode", elf="build/testjobs/cobs-opcode.elf"), 10)
    expect("tool-error: missing module", run("missing", chain=False,
           modules=JOB["modules"][:-1] + ["build/testjobs/Nope.lean"]), 13)
    print("all COBS controls behaved as stated" if not failures else f"{failures} FAILED")
    sys.exit(1 if failures else 0)


main()
