#!/usr/bin/env python3
"""Negative controls for the RMK memmove job (jobs/rmk/rmk-memmove-small.json).

Usage: python3 -I scripts/test-rmk-memmove-job.py E5R_VERIFY [BUNDLE_DIR]

Runs variants of the job (written under verification/rv32/build/testjobs,
id `rmk-memmove-neg`, `--resume` so unchanged modules are not recompiled)
against the pinned ELF at verification/rv32/build/rmk-qemu-riscv-rynk.elf,
and expects each to be refused for its own reason:

  * the ELF with one instruction of memmove changed (0x80020da6
    `sub a3,a0,a1` -> `sub a5,a0,a1`): `error` against the pin; without the
    pin the image is exported and accepted by the reader, and the proof of
    the emitted code no longer checks (`failed`);
  * a proof address no longer at the named symbol: `error`;
  * a module claiming the board's model RAM starts 4 bytes later: `failed`;
  * the image declared as flash on the RAM board: `error`.
With BUNDLE_DIR (from `e5r-verify bundle` of the job), a copy of it with the
packed module changed by one word fails `recheck.sh` at the checksums, and
with the checksum forged as well, at the packing check.
Exit status 0 only if every case behaves as stated.
"""
import json
import os
import shutil
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verification", "rv32")
T = os.path.join(ROOT, "build", "testjobs")
JOB = json.load(open(os.path.join(ROOT, "jobs", "rmk", "rmk-memmove-small.json")))
failures = 0


def variant(name, **over):
    j = json.loads(json.dumps(JOB))
    j["id"], j["root"] = "rmk-memmove-neg", "../.."
    for k, v in over.items():
        if v is None:
            j.pop(k, None)
        else:
            j[k] = v
    path = os.path.join(T, f"memmove-{name}.json")
    json.dump(j, open(path, "w"), indent=1)
    return path


def expect(name, argv, code, needle, cwd=ROOT):
    global failures
    r = subprocess.run(argv, capture_output=True, text=True, cwd=cwd)
    try:
        doc = json.loads(r.stdout)
        text = f"{doc.get('status')} {doc.get('message', '')}"
    except ValueError:
        text = r.stdout + r.stderr
    ok = r.returncode == code and needle in text
    failures += not ok
    print(f"{'ok' if ok else 'FAIL'} {name}: exit {r.returncode} | {text.strip()[:220]}")
    if not ok:
        print(f"   wanted exit {code} and {needle!r}\n{text[-2000:]}")


def main():
    tool = os.path.abspath(sys.argv[1])
    os.makedirs(T, exist_ok=True)
    elf = bytearray(open(os.path.join(ROOT, JOB["elf"]), "rb").read())
    off = 0x1000 + 0x20da6
    assert int.from_bytes(elf[off:off + 4], "little") == 0x40b506b3
    elf[off + 1] ^= 0x01  # rd 13 -> 15
    open(os.path.join(T, "memmove-wrong.elf"), "wb").write(elf)
    wrong = "build/testjobs/memmove-wrong.elf"
    check = [tool, "check", "--resume"]

    expect("changed memmove instruction against the pin",
           check + [variant("pinned", elf=wrong)], 13, "ELF identity changed")
    expect("stale proof address",
           check + [variant("symbol", symbols={"0x80020c20": "memmove"})], 13,
           "no symbol containing")
    expect("image declared as flash on the RAM board",
           check + [variant("flash", image={**JOB["image"], "kind": "flash"})], 13,
           "places images in ram")
    open(os.path.join(T, "MemmoveWrongBoard.lean"), "w").write(
        "import Projects.ramimage.Memmove\n"
        "theorem E5R.RmkMemmoveNeg.board : E5R.Rmk.B = "
        "E5R.QemuVirtRv32.board (E5R.Rmk.Image.image.rwBase + 4) := by\n"
        "  rw [E5R.Rmk.Image.image_rwBase]\n")
    expect("false claim about the board",
           check + [variant("board", modules=JOB["modules"] + ["build/testjobs/MemmoveWrongBoard.lean"],
                            theorems=JOB["theorems"] + ["E5R.RmkMemmoveNeg.board"])],
           10, "MemmoveWrongBoard.lean")
    expect("changed memmove instruction, unpinned: the proof fails",
           check + [variant("unpinned", elf=wrong, elf_sha256=None)], 10, "MemmoveFetch.lean")

    if len(sys.argv) > 2:
        b = os.path.join(T, "bundle-copy")
        shutil.rmtree(b, ignore_errors=True)
        shutil.copytree(sys.argv[2], b)
        p = os.path.join(b, "Projects/rmk/Elf.lean")
        src = open(p, encoding="utf-8").read()
        i = src.index("⟨454024, [") + len("⟨454024, [")
        src = src[:i] + str((int(src[i]) + 1) % 10) + src[i + 1:]
        open(p, "w", encoding="utf-8").write(src)
        expect("bundle with a changed packed word", ["./recheck.sh"], 1, "FAILED", cwd=b)
        import hashlib
        sums = os.path.join(b, "SHA256SUMS")
        lines = [f"{hashlib.sha256(src.encode()).hexdigest()}  Projects/rmk/Elf.lean"
                 if l.endswith("  Projects/rmk/Elf.lean") else l
                 for l in open(sums).read().splitlines()]
        open(sums, "w").write("\n".join(lines) + "\n")
        expect("same, checksum forged: the packing check refuses", ["./recheck.sh"], 1,
               "bytes differ", cwd=b)
        shutil.rmtree(b)
    print("all memmove job controls passed" if not failures else f"{failures} FAILED")
    sys.exit(1 if failures else 0)


main()
