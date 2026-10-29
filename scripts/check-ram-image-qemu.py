#!/usr/bin/env python3
"""Compare an `e5r-verify ram-image` export with the RAM QEMU actually loads.

Usage: QEMU=/path/qemu-system-riscv32 python3 -I scripts/check-ram-image-qemu.py \
           IMAGE.elf OUT_DIR [extra QEMU args, e.g. -m 16M]

Starts `qemu-system-riscv32 -M virt -cpu rv32 -bios none -kernel IMAGE.elf -S`
(halted before the first instruction, after QEMU's loader and reset have run),
then through the monitor:
  * `info roms`: every blob QEMU placed; the ELF segments must be exactly the
    manifest's [p_vaddr, p_vaddr + p_memsz), and nothing else (FDT, reset ROM)
    may overlap them;
  * `pmemsave` of each segment: file bytes equal the blob, zero-fill is zero;
  * the reset ROM's jump target (word at 0x1018) equals the manifest entry.
Exit status 0 only if all agree. Evidence for assumptions A1, A3 and A4 of the
manifest under these QEMU arguments; not a proof of anything.
"""
import json
import os
import re
import subprocess
import sys
import tempfile


def fail(msg):
    print(f"MISMATCH: {msg}")
    sys.exit(1)


class Monitor:
    def __init__(self, argv):
        self.p = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT)
        self.read_prompt()

    def read_prompt(self):
        buf = b""
        while not buf.endswith(b"(qemu) "):
            c = self.p.stdout.read(1)
            if not c:
                fail(f"QEMU exited: {buf.decode(errors='replace')[-400:]}")
            buf += c
        # The monitor echoes with terminal escapes; keep plain lines only.
        text = re.sub(rb"\x1b\[[0-9;]*[A-Za-z]", b"", buf).decode(errors="replace")
        return text

    def cmd(self, line):
        self.p.stdin.write(line.encode() + b"\n")
        self.p.stdin.flush()
        return self.read_prompt()

    def quit(self):
        self.p.stdin.write(b"quit\n")
        self.p.stdin.flush()
        self.p.wait(timeout=30)


def main():
    elf, out, extra = sys.argv[1], sys.argv[2], sys.argv[3:]
    qemu = os.environ.get("QEMU", "qemu-system-riscv32")
    man = json.load(open(os.path.join(out, "manifest.json")))
    argv = [qemu, "-M", "virt", "-cpu", "rv32", "-smp", "1", "-bios", "none", "-kernel", elf,
            "-S", "-display", "none", "-serial", "null", "-monitor", "stdio", *extra]
    mon = Monitor(argv)
    roms = []
    for m in re.finditer(r"addr=([0-9a-f]+) size=0x([0-9a-f]+) mem=(\w+) name=\"([^\"]*)\"",
                         mon.cmd("info roms")):
        roms.append((int(m.group(1), 16), int(m.group(2), 16), m.group(3), m.group(4)))
    seg_roms = [r for r in roms if "ELF program header segment" in r[3]]
    other = [r for r in roms if r not in seg_roms]
    want = [(s["p_vaddr"], s["p_memsz"]) for s in man["segments"]]
    if [(a, n) for a, n, _, _ in seg_roms] != want:
        fail(f"QEMU placed segments {[(hex(a), hex(n)) for a, n, _, _ in seg_roms]}")
    for a, n, _, name in other:
        for v, m in want:
            if a < v + m and v < a + n:
                fail(f"QEMU blob {name!r} [{a:#x}, +{n:#x}) overlaps segment at {v:#x}")
    print("ok QEMU roms:", ", ".join(f"{name.split('/')[-1]}@{a:#x}+{n:#x}"
                                    for a, n, _, name in roms))
    m = re.search(r"00001018: (0x[0-9a-f]+)", mon.cmd("xp /1xw 0x1018"))
    if not m or int(m.group(1), 16) != man["entry"]:
        fail(f"reset ROM jumps to {m and m.group(1)}, manifest entry {man['entry']:#x}")
    print(f"ok reset ROM at 0x1000 jumps to entry {man['entry']:#x}")
    with tempfile.TemporaryDirectory() as d:
        for s in man["segments"]:
            path = os.path.join(d, f"{s['index']}.bin")
            mon.cmd(f'pmemsave {s["p_vaddr"]:#x} {s["p_memsz"]:#x} "{path}"')
            ram = open(path, "rb").read()
            blob = open(os.path.join(out, s["blob"]), "rb").read()
            fs = s["p_filesz"]
            if len(ram) != s["p_memsz"] or ram[:fs] != blob:
                fail(f"PT_LOAD {s['index']}: QEMU RAM != blob")
            if ram[fs:].count(0) != len(ram) - fs:
                fail(f"PT_LOAD {s['index']}: QEMU zero-fill range has non-zero bytes")
            print(f"ok PT_LOAD {s['index']}: QEMU RAM [{s['p_vaddr']:#x}, +{s['p_memsz']:#x}) "
                  f"= {fs} blob bytes + {s['p_memsz'] - fs} zeros")
    mon.quit()


main()
