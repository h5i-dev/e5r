#!/usr/bin/env python3
"""Check an `e5r-verify ram-image` image.lean against the ELF and the checker's reader.

Usage: python3 -I scripts/check-ram-image-lean.py IMAGE.elf OUT_DIR RV32_DIR [BASE SIZE]

RV32_DIR is a verification/rv32 tree whose Theories contain RamElf.lean (the
checker's independent reader); BASE SIZE default to 0x80000000 0x1000000.
Needs `elan` with the toolchain in RV32_DIR/lean-toolchain.

1. Whole-file fidelity, outside the Rust packer: parse the `File` literal from
   image.lean, unpack every word (64-byte little-endian) and compare all bytes
   and the sha256 with IMAGE.elf.
2. Compile Theories.{Hart,Platform,RamElf} and the image module with plain
   `lean` into a scratch directory, then a check module whose theorems the
   kernel decides (`decide +kernel`): the reader accepts the file, and its
   `check` yields exactly the manifest's entry, PT_LOAD table and rwBase.
   The theorems are statements about the reader's output on these bytes;
   they say nothing about the program's behaviour.
Exit status 0 only if all of it holds.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time


def fail(msg):
    print(f"MISMATCH: {msg}")
    sys.exit(1)


def lean(toolchain, lean_path, src, out=None):
    argv = ["elan", "run", toolchain, "lean"] + (["-o", out] if out else []) + [src]
    t = time.time()
    r = subprocess.run(["/usr/bin/time", "-f", "%M"] + argv, capture_output=True, text=True,
                       env={**os.environ, "LEAN_PATH": lean_path})
    if r.returncode != 0:
        fail(f"lean {src}:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    kb = int(r.stderr.strip().splitlines()[-1])
    return time.time() - t, kb


def main():
    elf, out, rv32 = sys.argv[1:4]
    base, size = (int(x, 0) for x in (sys.argv[4:6] or ["0x80000000", "0x1000000"]))
    data = open(elf, "rb").read()
    man = json.load(open(os.path.join(out, "manifest.json")))
    src = open(os.path.join(out, "image.lean"), encoding="utf-8").read()

    m = re.search(r"^namespace (\S+)\n", src, re.M)
    lit = re.search(r"def elf : E5R\.RamElf\.File := ⟨(\d+), \[([0-9,\s]*)\]⟩\nend ", src)
    if not m or not lit:
        fail("image.lean is not `def elf : E5R.RamElf.File := ⟨len, [...]⟩`")
    ns = m.group(1)
    n = int(lit.group(1))
    words = [int(w) for w in lit.group(2).replace("\n", "").split(",") if w.strip()]
    if n != len(data) or len(words) != (n + 63) // 64:
        fail(f"len {n} / {len(words)} words for a {len(data)}-byte file")
    unpacked = b"".join(w.to_bytes(64, "little") for w in words)
    if any(unpacked[n:]) or unpacked[:n] != data:
        fail("unpacked words differ from the ELF")
    if hashlib.sha256(unpacked[:n]).hexdigest() != man["elf"]["sha256"]:
        fail("sha256")
    print(f"ok image.lean unpacks to all {n} ELF bytes ({len(words)} words), "
          f"sha256 {man['elf']['sha256']}")

    toolchain = open(os.path.join(rv32, "lean-toolchain")).read().strip()
    loads = ", ".join(
        f"({s['p_vaddr']}, {s['p_memsz']}, {str(s['w']).lower()}, {str(s['x']).lower()}, "
        f"{s['p_offset']}, {s['p_filesz']})" for s in man["segments"])
    check = f"""import {ns}
open E5R.RamElf
namespace {ns}.Check
theorem accepted : accepts {base} {size} {ns}.elf = true := by decide +kernel
/-- The reader's parse equals the exporter's manifest (entry, loads, rwBase). -/
theorem agrees :
    (match check {base} {size} {ns}.elf with
     | .ok (entry, ls, rwBase) =>
       entry == {man['entry']} && rwBase == {man['rw_base']} &&
       ls.map (fun l => (l.vaddr, l.memsz, l.write, l.exec, l.off, l.filesz)) == [{loads}]
     | .error _ => false) = true := by decide +kernel
end {ns}.Check
"""
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "Theories"))
        for mod in ["Hart", "Platform", "RamElf"]:
            lean(toolchain, d, os.path.join(rv32, "Theories", f"{mod}.lean"),
                 os.path.join(d, "Theories", f"{mod}.olean"))
        parts = ns.split(".")
        os.makedirs(os.path.join(d, *parts[:-1]), exist_ok=True)
        olean = os.path.join(d, *parts) + ".olean"
        secs, kb = lean(toolchain, d, os.path.join(out, "image.lean"), olean)
        print(f"ok image module {ns} elaborates: {secs:.1f} s, {kb // 1024} MB")
        path = os.path.join(d, "Check.lean")
        open(path, "w").write(check)
        secs, kb = lean(toolchain, d, path)
        print(f"ok kernel: accepts = true and check = manifest "
              f"(entry {man['entry']:#x}, {len(man['segments'])} PT_LOADs, "
              f"rwBase {man['rw_base']:#x}): {secs:.1f} s, {kb // 1024} MB")
    print(f"lean toolchain {toolchain}")


main()
