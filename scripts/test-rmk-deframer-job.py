#!/usr/bin/env python3
"""Baseline and negative controls for the CONDITIONAL Deframer job
(jobs/rmk/rmk-deframer-conditional.json: tail/park/unpark from CopyContract, next from
CopyContract and CobsReportContract; main's proofs, my runner wrapper).

Usage: python3 -I scripts/test-rmk-deframer-job.py E5R_VERIFY [JOB_ID] [--copies|--official]

JOB_ID defaults to rmk-deframer-conditional; rmk-session-conditional (main's recv_step and
unpark_step, CopyContract explicit) adds the session cases below. --official (default once
main's files contain no `macro`) runs the controls on UNEXPANDED copies; --copies expands
`csr_chain` (a stopgap while main's files still define it).

Every run uses COPIES of Projects/rmk/Deframer/*.lean and Projects/ramimage/Deframer.lean in
verification/rv32/build/testjobs/defmut/ (imports renamed; main's files are not touched), with
main's tactic macro `csr_chain` expanded inline: the runner forbids `macro` in checked modules,
so main's files themselves cannot be checked until that is inlined (reported to main). The
expansion is the macro's own right-hand side, nothing else changes.

A mutation is REJECTED only if the run ends `failed` (a Lean proof does not check) with its
first error inside a theorem of the copied chain, not an import/unknown-identifier error;
`error` (exit 13) is a tool/job problem. The 'probe' line is informative, not required.

  control       expanded copies, no mutation                                   -> proved
  frame         tailStack := 0x20 + 12 (no room for memmove's 48-byte frame)   -> rejected
  panic-bound   Inv admits filled = len + 1 (tail's entry check panics)        -> rejected
  tail-result   TailPost: filled' = filled - consumed + 1                      -> rejected
  next-result   NextPost: Some(k) with 3 < k (was 2 < k)                       -> rejected
  opcode        ELF 0x8001d58e bltu s2,s1 -> bgeu s2,s1 (tail's bound check)   -> rejected at its fact
  probe         CobsPost.ok := True (next not told the decoded length <= n)    -> reported either way
  tool-error    a job module that does not exist                               -> error
"""
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verification", "rv32")
T = os.path.join(ROOT, "build", "testjobs")
MUT = os.path.join(T, "defmut")
ARGS = [a for a in sys.argv[1:] if not a.startswith("--")]
JOBID = ARGS[1] if len(ARGS) > 1 else "rmk-deframer-conditional"
JOB = json.load(open(os.path.join(ROOT, "jobs", "rmk", JOBID + ".json")))
CHAIN = [m.split("/")[-1][:-5] for m in JOB["modules"] if m.startswith("Projects/rmk/Deframer/")]
SRC = {m: open(os.path.join(ROOT, "Projects/rmk/Deframer", m + ".lean"), encoding="utf-8").read() for m in CHAIN}
# runner wrappers that import the chain: Projects/ramimage/X.lean -> defmut/WrapX.lean
WRAPS = [m.split("/")[-1][:-5] for m in JOB["modules"] if m.startswith("Projects/ramimage/")]
WRAP = {w: open(os.path.join(ROOT, "Projects/ramimage", w + ".lean"), encoding="utf-8").read() for w in WRAPS}
# other job modules that import the chain (e.g. Cobs/Bridge imports Deframer.Spec): copied too, as
# defmut/ExtX.lean, so no module sees both the original and the mutated chain
EXT = {m: open(os.path.join(ROOT, m), encoding="utf-8").read() for m in JOB["modules"]
       if not m.startswith(("Projects/rmk/Deframer/", "Projects/ramimage/"))
       and "import Projects.rmk.Deframer." in open(os.path.join(ROOT, m), encoding="utf-8").read()}
EXTN = {m: "Ext" + m.split("/")[-1][:-5] for m in EXT}
MACRO = re.compile(r'^macro "csr_chain" : tactic => `\(tactic\| (.*)\)\s*$', re.M)
HAS_MACRO = any(re.search(r"^\s*(macro|syntax|macro_rules|elab)\b", t, re.M) for t in SRC.values())
EXPAND = "--copies" in sys.argv or ("--official" not in sys.argv and HAS_MACRO)
EXP = next((MACRO.search(t).group(1) for t in SRC.values() if MACRO.search(t)), None)
assert not EXPAND or EXP, "--copies but no csr_chain macro to expand"
failures = 0


def write_chain(edits):
    shutil.rmtree(MUT, ignore_errors=True)
    os.makedirs(MUT)
    files = dict(SRC, **{"Wrap" + w: t for w, t in WRAP.items()}, **{EXTN[m]: t for m, t in EXT.items()})
    for m, s in files.items():
        if EXPAND:
            s = MACRO.sub("", s)
            s = re.sub(r"\bcsr_chain\b", f"({EXP})", s)
        for o in CHAIN:
            s = s.replace(f"import Projects.rmk.Deframer.{o}\n", f"import build.testjobs.defmut.{o}\n")
        for w in WRAPS:
            s = s.replace(f"import Projects.ramimage.{w}\n", f"import build.testjobs.defmut.Wrap{w}\n")
        for e, n in EXTN.items():
            s = s.replace(f"import {e[:-5].replace('/', '.')}\n", f"import build.testjobs.defmut.{n}\n")
        if m in edits:
            old, new = edits[m]
            assert s.count(old) == 1, (m, old)
            s = s.replace(old, new)
        open(os.path.join(MUT, m + ".lean"), "w", encoding="utf-8").write(s)


def run(name, elf=None, modules=None):
    j = json.loads(json.dumps(JOB))
    j["id"], j["root"] = "rmk-deframer-neg", "../.."
    mods = []
    for m in j["modules"]:
        if m.startswith("Projects/rmk/Deframer/"):
            mods.append("build/testjobs/defmut/" + m.split("/")[-1])
        elif m in EXTN:
            mods.append(f"build/testjobs/defmut/{EXTN[m]}.lean")
        elif m.startswith("Projects/ramimage/"):
            mods.append("build/testjobs/defmut/Wrap" + m.split("/")[-1])
        else:
            mods.append(m)
    j["modules"] = mods[:-1] + ["build/testjobs/Nope.lean"] if modules == "missing" else mods
    if elf:
        j["elf"] = elf
        j.pop("elf_sha256")
    path = os.path.join(T, f"{JOBID}-{name}.json")
    json.dump(j, open(path, "w"), indent=1)
    r = subprocess.run([TOOL, "check", "--resume", path], capture_output=True, text=True, cwd=ROOT)
    doc = json.loads(r.stdout) if r.stdout.strip().startswith("{") else {}
    return r.returncode, doc.get("status"), doc.get("message", r.stderr)


def full_errors(msg):
    m = re.search(r"((?:build/testjobs/defmut|Projects/rmk)/\w+\.lean): exited with", msg or "")
    if not m:
        return msg
    r = subprocess.run(["lean", "-j1", m.group(1)], cwd=ROOT, capture_output=True, text=True,
                       env={**os.environ, "LEAN_PATH": "."})
    return "\n".join(l for l in (r.stdout + r.stderr).splitlines() if ": error" in l) or msg


def first_error(msg):
    m = re.search(r"((?:build/testjobs/defmut|Projects/rmk)/\w+\.lean):(\d+):\d+: error[^\n]*", msg or "")
    if not m:
        return None, None, None
    text = open(os.path.join(ROOT, m.group(1)), encoding="utf-8").read().splitlines()
    thm = next((re.match(r"(?:private )?(?:theorem|def|structure|lemma) (\S+)", l).group(1)
                for l in reversed(text[:int(m.group(2))])
                if re.match(r"(?:private )?(?:theorem|def|structure|lemma) \S+", l)), "?")
    return m.group(1), thm, m.group(0)


def expect(name, got, code, required=True):
    global failures
    rc, status, msg = got
    if rc == 10:
        msg = full_errors(msg)
    path, thm, line = first_error(msg) if rc == 10 else (None, None, None)
    bad_kind = code == 10 and (line is None or re.search(r"unknown (identifier|module|constant)|import", line or ""))
    ok = rc == code and not bad_kind
    if required:
        failures += not ok
    tag = ("ok" if ok else "FAIL") if required else "probe"
    where = f" first error in {path} ({thm})" if path else ""
    first = line or ((msg or "").strip().splitlines() or [""])[0]
    print(f"{tag} {name}: exit {rc} {status}{where} | {first[:160]}", flush=True)
    if required and not ok:
        print((msg or "")[-1500:], flush=True)


def main():
    global TOOL
    TOOL = os.path.abspath(ARGS[0])
    os.makedirs(T, exist_ok=True)
    print(f"job {JOBID}; copies {'with csr_chain EXPANDED (stopgap)' if EXPAND else 'unexpanded (main files as committed)'}", flush=True)
    write_chain({})
    expect("control: copies, no mutation", run("control"), 0)
    cases = [
        ("frame", {"Spec": ("def tailStack : Nat := 0x20 + memmoveFrame", "def tailStack : Nat := 0x20 + 12")}),
        ("panic-bound", {"Spec": ("  consumed ram p ≤ filled ram p ∧ filled ram p ≤ len\n",
                                  "  consumed ram p ≤ filled ram p ∧ filled ram p ≤ len + 1\n")}),
        ("tail-result", {"Spec": ("    filled m₀.ram (m₀.core.get 10) - consumed m₀.ram (m₀.core.get 10)\n  ret :",
                                  "    filled m₀.ram (m₀.core.get 10) - consumed m₀.ram (m₀.core.get 10) + 1\n  ret :")}),
        ("next-result", {"Spec": ("val : (m.core.get 10).toNat = 1 → 2 < (m.core.get 11).toNat",
                                  "val : (m.core.get 10).toNat = 1 → 3 < (m.core.get 11).toNat")}),
    ]
    if JOBID == "rmk-session-conditional":
        cases += [
            ("recv-msg-len", {"Session": ("          3 ≤ (ramRead m.ram (msgA + 4) .w).toNat ∧",
                                          "          4 ≤ (ramRead m.ram (msgA + 4) .w).toNat ∧")}),
            ("recv-frame", {"Session": ("(sp.toNat - 0x70 ≤ x.toNat ∧ x.toNat < sp.toNat)",
                                        "(sp.toNat - 0x6c ≤ x.toNat ∧ x.toNat < sp.toNat)")}),
            ("unpark-parked", {"SessionLoop": ("  parked : (ramRead m.ram 0x8002a798 .w).toNat ≤ bufLen\n",
                                               "  parked : (ramRead m.ram 0x8002a798 .w).toNat ≤ bufLen + 1\n")}),
        ]
    if JOBID == "rmk-session-discharged":
        cases += [
            # the deframer's calls may pass a destination reaching into memmove's frame: the
            # discharge (copy_contract, from the peer's PreM) must no longer check
            ("copy-dstsep", {"Spec": ("  dstSep : (m.core.get 10).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - memmoveFrame\n",
                                      "  dstSep : (m.core.get 10).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat\n")}),
        ]
    for name, edits in cases:
        write_chain(edits)
        expect(name, run(name), 10)
    elf = bytearray(open(os.path.join(ROOT, JOB["elf"]), "rb").read())
    off = 0x1000 + (0x8001d58e - 0x80000000)
    w = int.from_bytes(elf[off:off + 4], "little")
    assert w == 0x04996863, hex(w)
    elf[off:off + 4] = (w ^ (1 << 12)).to_bytes(4, "little")  # funct3 110 (bltu) -> 111 (bgeu)
    open(os.path.join(T, "deframer-opcode.elf"), "wb").write(elf)
    write_chain({})
    expect("opcode", run("opcode", elf="build/testjobs/deframer-opcode.elf"), 10)
    if JOBID == "rmk-session-discharged":
        # memmove's forward/backward dispatch 0x80020c3a bgeu a0,t5 -> bltu: the discharge must fail
        elf = bytearray(open(os.path.join(ROOT, JOB["elf"]), "rb").read())
        off = 0x1000 + (0x80020c3a - 0x80000000)
        w = int.from_bytes(elf[off:off + 4], "little")
        assert w & 0x707f == 0x7063, hex(w)  # BRANCH, funct3 111 (bgeu)
        elf[off:off + 4] = (w ^ (1 << 12)).to_bytes(4, "little")  # -> 110 (bltu)
        open(os.path.join(T, "memmove-opcode.elf"), "wb").write(elf)
        write_chain({})
        expect("memmove-opcode", run("memmove-opcode", elf="build/testjobs/memmove-opcode.elf"), 10)
    i = SRC["Spec"].index("  ok : (ramRead m.ram (m₀.core.get 10) .w - 1)")
    j = SRC["Spec"].index("def CobsReportContract")
    write_chain({"Spec": (SRC["Spec"][i:j], "  ok : True\n\n")})
    expect("probe: CobsPost.ok := True", run("probe"), 10, required=False)
    write_chain({})
    expect("tool-error: missing module", run("missing", modules="missing"), 13)
    print("all Deframer controls behaved as stated" if not failures else f"{failures} FAILED", flush=True)
    sys.exit(1 if failures else 0)


main()
