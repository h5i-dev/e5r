#!/usr/bin/env python3
"""Independent oracle for `e5r-verify ram-image` output.

Usage: python3 -I scripts/check-ram-image.py IMAGE.elf OUT_DIR

Compares OUT_DIR/manifest.json and its blobs against GNU binutils, which share
no code with the Rust exporter:
  * `readelf -hlW` for the entry and every PT_LOAD header field;
  * `objcopy -I elf32-little -O binary`, which writes the file-backed contents
    at their load (physical) addresses, for the bytes;
  * hashlib for every digest.
Exit status 0 only if everything agrees. Nothing here is a proof; it is a
cross-check of the exporter's byte/address correspondence.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile


def fail(msg):
    print(f"MISMATCH: {msg}")
    sys.exit(1)


def readelf(elf):
    out = subprocess.run(["readelf", "-hlW", elf], check=True, capture_output=True,
                         text=True, env={"LC_ALL": "C", "PATH": os.environ["PATH"]}).stdout
    entry = int(re.search(r"Entry point address:\s+(0x[0-9a-f]+)", out).group(1), 16)
    loads = []
    for m in re.finditer(r"^\s*LOAD\s+(0x\S+)\s+(0x\S+)\s+(0x\S+)\s+(0x\S+)\s+(0x\S+)"
                         r"\s+([RWE ]+?)\s+(0x\S+)\s*$", out, re.M):
        off, va, pa, fs, ms = (int(m.group(k), 16) for k in range(1, 6))
        fl = m.group(6)
        loads.append(dict(p_offset=off, p_vaddr=va, p_paddr=pa, p_filesz=fs, p_memsz=ms,
                          r="R" in fl, w="W" in fl, x="E" in fl, p_align=int(m.group(7), 16)))
    return entry, loads


def main():
    elf, out = sys.argv[1], sys.argv[2]
    data = open(elf, "rb").read()
    man = json.load(open(os.path.join(out, "manifest.json")))
    if man["schema"] != "e5r.ram-image.v1" or man["mapping"] != "paddr=vaddr":
        fail("schema or mapping")
    if man["elf"] != {"sha256": hashlib.sha256(data).hexdigest(), "size": len(data)}:
        fail("ELF hash/size")
    entry, loads = readelf(elf)
    if man["entry"] != entry:
        fail(f"entry {man['entry']:#x} != readelf {entry:#x}")
    segs = man["segments"]
    if len(segs) != len(loads):
        fail(f"{len(segs)} segments, readelf has {len(loads)} PT_LOADs")
    with tempfile.TemporaryDirectory() as d:
        flat_path = os.path.join(d, "flat.bin")
        subprocess.run(["objcopy", "-I", "elf32-little", "-O", "binary", elf, flat_path],
                       check=True)
        flat = open(flat_path, "rb").read()
    lma0 = min(l["p_paddr"] for l in loads if l["p_filesz"] > 0)
    blobs = set()
    for s, l in zip(segs, loads):
        for k, v in l.items():
            if s[k] != v:
                fail(f"PT_LOAD {s['index']}: {k} {s[k]} != readelf {v}")
        fs, ms, va = l["p_filesz"], l["p_memsz"], l["p_vaddr"]
        blob = open(os.path.join(out, s["blob"]), "rb").read()
        blobs.add(s["blob"])
        if blob != data[l["p_offset"]:l["p_offset"] + fs]:
            fail(f"PT_LOAD {s['index']}: blob != ELF file slice")
        if blob != flat[l["p_paddr"] - lma0:l["p_paddr"] - lma0 + fs]:
            fail(f"PT_LOAD {s['index']}: blob != objcopy image at its load address")
        if s["file_sha256"] != hashlib.sha256(blob).hexdigest():
            fail(f"PT_LOAD {s['index']}: file_sha256")
        if s["file"] != {"start": va, "end": va + fs}:
            fail(f"PT_LOAD {s['index']}: file range")
        zero = {"start": va + fs, "end": va + ms} if ms > fs else None
        if s["zero"] != zero:
            fail(f"PT_LOAD {s['index']}: zero range {s['zero']} != {zero}")
        print(f"ok PT_LOAD {s['index']}: [{va:#x}, {va + fs:#x}) {fs} bytes "
              f"sha256 {s['file_sha256'][:16]}..., zero {ms - fs}")
    extra = set(os.listdir(out)) - blobs - {"manifest.json", "image.lean"}
    if extra:
        fail(f"unexpected files {sorted(extra)}")
    if man["totals"] != {"file_bytes": sum(l["p_filesz"] for l in loads),
                         "zero_bytes": sum(l["p_memsz"] - l["p_filesz"] for l in loads)}:
        fail("totals")
    print(f"ok entry {entry:#x}, ELF sha256 {man['elf']['sha256']}")


main()
