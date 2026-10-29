#!/usr/bin/env python3
"""End-to-end lifecycle tests of RAM-image verification jobs (`image.kind: ram`).

Usage: python3 -I scripts/test-ram-image-job.py E5R_VERIFY IMAGE.elf

IMAGE.elf is a RAM-resident ELF the qemu-virt-rv32 board accepts (the pinned
RMK example). Jobs, modules and copies of the ELF are written under
verification/rv32/build/testjobs (ignored by git), so the committed job and
its generated files are not touched. Needs elan; the run takes a few minutes.

Each case runs `E5R_VERIFY check` (or `verify-result`) and checks the exit
status (0 proved, 10 failed, 11 unsupported, 13 error) and a message
substring. The positive case is a real `proved` run; a statement about the
image, not about the program.
"""
import json
import os
import shutil
import struct
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verification", "rv32")
T = os.path.join(ROOT, "build", "testjobs")
NS = "E5R.TestRamImage"
MOD = "build.testjobs.Image"
failures = 0


def job(name, **over):
    j = {
        "schema": "e5r.verify.job.v1", "id": f"test-{name}", "root": "../..",
        "board": "boards/qemu-virt-rv32.json", "elf": "build/testjobs/image.elf",
        "image": {"kind": "ram", "module": MOD, "namespace": NS},
        "modules": ["build/testjobs/Ok.lean"], "theorems": [f"{NS}.T.*"],
        "limits": {"seconds": 900, "rss_mib": 3072},
    }
    for k, v in over.items():
        if v is None:
            j.pop(k, None)
        else:
            j[k] = v
    path = os.path.join(T, f"{name}.json")
    json.dump(j, open(path, "w"), indent=1)
    return path


def run(argv):
    r = subprocess.run(argv, capture_output=True, text=True, cwd=ROOT)
    try:
        doc = json.loads(r.stdout)
    except ValueError:
        doc = {}
    return r.returncode, doc.get("status", ""), doc.get("message", "") + r.stderr + r.stdout


def expect(name, got, code, needle):
    global failures
    rc, status, text = got
    ok = rc == code and needle in text
    failures += not ok
    first = text.strip().splitlines()[0][:150] if text.strip() else ""
    print(f"{'ok' if ok else 'FAIL'} {name}: exit {rc} {status} | {first}")
    if not ok:
        print(f"   wanted exit {code} and {needle!r}\n{text[-1500:]}")


def main():
    global failures
    tool, elf = os.path.abspath(sys.argv[1]), sys.argv[2]
    shutil.rmtree(T, ignore_errors=True)
    os.makedirs(T)
    data = open(elf, "rb").read()
    open(os.path.join(T, "image.elf"), "wb").write(data)
    sha = __import__("hashlib").sha256(data).hexdigest()
    open(os.path.join(T, "Ok.lean"), "w").write(
        f"import build.testjobs.ImageFidelity\nnamespace {NS}.T\n"
        f"theorem entry : {NS}.image.entry = {struct.unpack_from('<I', data, 24)[0]} := "
        "by decide +kernel\nend " + f"{NS}.T\n")
    check = lambda path: run([tool, "check", path])

    # Positive: a fresh proved run, then a current result.
    pos = job("positive", elf_sha256=sha)
    res = os.path.join(T, "positive.result.json")
    expect("proved RAM-image job", run([tool, "check", pos, "--out", res]), 0, "proved")
    expect("result is current", run([tool, "verify-result", res]), 0, "current")

    # The cross-check discriminates: the fidelity theorems with a wrong
    # entry, rwBase or permission do not check against these oleans.
    fid = open(os.path.join(T, "ImageFidelity.lean")).read()
    entry = struct.unpack_from("<I", data, 24)[0]
    man = json.load(open(os.path.join(ROOT, "build/jobs/test-positive/ram-image.json")))
    rw = man["rw_base"]
    memsz0 = man["segments"][0]["p_memsz"]
    cases = [("unmodified control", "", ""),
             ("wrong entry", f"entry == {entry} &&", f"entry == {entry + 2} &&"),
             ("wrong rwBase", f"rwBase == {rw} &&", f"rwBase == {rw + 4} &&"),
             ("wrong exec bit", f"{memsz0}, false, true,", f"{memsz0}, false, false,")]
    for what, a, b in cases:
        assert a in fid, a
        bad = fid.replace(f"namespace {NS}\n", f"namespace {NS}.Bad\n").replace(
            f"end {NS}\n", f"end {NS}.Bad\n").replace(a, b, 1)
        path = os.path.join(T, "BadFidelity.lean")
        open(path, "w").write(bad)
        r = subprocess.run(["lean", "-j1", path], cwd=ROOT, capture_output=True, text=True,
                           env={**os.environ, "LEAN_PATH": "."})
        out = r.stdout + r.stderr
        if not a:
            expect("fidelity copy checks unmodified", (r.returncode, "", out + "x"), 0, "x")
            continue
        # Only the cross-check line may fail: the error is reported inside image_agrees.
        line = next((n + 1 for n, l in enumerate(bad.splitlines()) if b in l), None)
        expect(f"fidelity with a {what} does not check", (r.returncode, "", out), 1,
               f"BadFidelity.lean:")
        errs = [l for l in out.splitlines() if "error" in l]
        agree = bad.splitlines().index("theorem image_agrees :") + 1
        entry_line = next(n + 1 for n, l in enumerate(bad.splitlines())
                          if l.startswith("theorem image_entry"))
        if not all(agree <= int(e.split(":")[1]) < entry_line for e in errs if ".lean:" in e):
            print(f"FAIL   errors outside image_agrees (line {line}): {errs}")
            failures += 1

    # Generated files are pinned: editing either after the run makes it stale.
    for rel, label in [(MOD.replace(".", "/") + ".lean", "packed module"),
                       ("build/jobs/test-positive/ram-image.json", "manifest")]:
        p = os.path.join(ROOT, rel)
        keep = open(p, "rb").read()
        open(p, "ab").write(b"\n-- edited\n")
        expect(f"edited {label} makes the result stale",
               run([tool, "verify-result", res]), 1, "generated image")
        open(p, "wb").write(keep)
    expect("restored files are current again", run([tool, "verify-result", res]), 0, "current")

    # A bogus pre-existing packed module is replaced, never checked.
    open(os.path.join(ROOT, MOD.replace(".", "/") + ".lean"), "w").write("-- stale\n")
    mutated = bytearray(data)
    struct.pack_into("<I", mutated, 52 + 32 + 12, struct.unpack_from("<I", data, 52 + 32 + 8)[0]
                     + 0x1000)  # PT_LOAD 1: p_paddr != p_vaddr
    open(os.path.join(T, "bad.elf"), "wb").write(mutated)
    expect("changed ELF against its pin", check(job("pin", elf_sha256=sha,
                                                    elf="build/testjobs/bad.elf")),
           13, "ELF identity changed")
    expect("exporter refusal is unsupported", check(job("refused", elf="build/testjobs/bad.elf")),
           11, "paddr=vaddr")
    expect("no stale packed module left after a refusal",
           (int(os.path.exists(os.path.join(ROOT, MOD.replace(".", "/") + ".lean"))), "", "x"),
           0, "x")
    expect("RAM job on a flash board", check(job("flashboard",
                                                 board="boards/hifive1-revb.json")),
           13, "does not place images in RAM")
    expect("flash job on a RAM board", check(job("flashkind", image={
        "kind": "flash", "module": MOD, "namespace": NS})), 13, "places images in ram")
    expect("unknown image kind", check(job("rom", image={
        "kind": "rom", "module": MOD, "namespace": NS})), 13, "unknown variant")
    expect("missing ELF", check(job("noelf", elf="build/testjobs/missing.elf")), 13, "elf")
    expect("missing proof module", check(job("nomod", modules=["build/testjobs/Missing.lean"])),
           13, "Missing.lean")
    open(os.path.join(T, "Sorry.lean"), "w").write(
        f"import build.testjobs.ImageFidelity\ntheorem {NS}.T.x : False := by sorry\n")
    expect("forbidden command", check(job("sorry", modules=["build/testjobs/Sorry.lean"])),
           13, "forbidden sorry")
    open(os.path.join(T, "False.lean"), "w").write(
        f"import build.testjobs.ImageFidelity\nnamespace {NS}.T\n"
        f"theorem wrong : {NS}.image.entry = {entry + 2} := by decide +kernel\nend {NS}.T\n")
    expect("proof that does not check is failed",
           check(job("false", modules=["build/testjobs/False.lean"])), 10, "False.lean")
    print("all RAM-image job tests passed" if not failures else f"{failures} FAILED")
    sys.exit(1 if failures else 0)


main()
