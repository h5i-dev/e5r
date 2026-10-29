#!/usr/bin/env python3
"""Independent check of an `e5r-verify ram-image` export against its ELF.

Original e5r code, Apache-2.0. Untrusted review tooling, not part of any
proof. It shares no code with the exporter: the ELF header, program headers
and section headers are parsed here with `struct`, and every claim of
manifest.json is recomputed:

- ELF sha256/size, entry, e_flags;
- each PT_LOAD: offset, vaddr, paddr (= vaddr), filesz, memsz, align, R/W/X,
  blob = ELF[p_offset, p_offset+filesz) byte for byte, blob sha256, the file
  and zero ranges, and that no PT_LOAD is missing or extra;
- every SHF_ALLOC section with contents (PROGBITS) lies inside the file part
  of one segment and its bytes there equal the section bytes; every NOBITS
  ALLOC section lies inside a zero range;
- the entry point is inside an executable segment's file bytes.

`--self-test` also runs negative controls: one flipped blob byte, a shifted
segment address, a dropped segment, a wrong hash; each must be detected.

Usage: check_ram_image.py ELF EXPORT_DIR [--self-test]
"""
import hashlib
import json
import shutil
import struct
import sys
import tempfile
from pathlib import Path

PT_LOAD = 1
SHT_NOBITS = 8
SHF_ALLOC = 2


def parse(elf):
    if elf[:4] != b'\x7fELF' or elf[4] != 1 or elf[5] != 1:
        raise ValueError('not ELF32 little-endian')
    (e_type, e_machine, e_version, e_entry, e_phoff, e_shoff, e_flags, e_ehsize, e_phentsize, e_phnum,
     e_shentsize, e_shnum, e_shstrndx) = struct.unpack_from('<HHIIIIIHHHHHH', elf, 16)
    if e_machine != 243:
        raise ValueError('not RISC-V')
    phs = [struct.unpack_from('<IIIIIIII', elf, e_phoff + i * e_phentsize) for i in range(e_phnum)]
    shs = [struct.unpack_from('<IIIIIIIIII', elf, e_shoff + i * e_shentsize) for i in range(e_shnum)]
    strtab = shs[e_shstrndx]
    def name(off):
        b = elf[strtab[4] + off:]
        return b[:b.index(0)].decode()
    secs = [dict(name=name(s[0]), type=s[1], flags=s[2], addr=s[3], off=s[4], size=s[5]) for s in shs]
    loads = [dict(type=p[0], off=p[1], vaddr=p[2], paddr=p[3], filesz=p[4], memsz=p[5], flags=p[6], align=p[7])
             for p in phs if p[0] == PT_LOAD]
    return dict(entry=e_entry, flags=e_flags, loads=loads, secs=secs)


def check(elf_path, out):
    errs = []
    elf = Path(elf_path).read_bytes()
    m = json.loads((out / 'manifest.json').read_text())
    e = parse(elf)
    want = lambda c, msg: c or errs.append(msg)
    want(m['elf']['sha256'] == hashlib.sha256(elf).hexdigest(), 'elf sha256')
    want(m['elf']['size'] == len(elf), 'elf size')
    want(m['entry'] == e['entry'], 'entry')
    want(m['e_flags'] == e['flags'], 'e_flags')
    segs = m['segments']
    want(len(segs) == len(e['loads']), f'segment count {len(segs)} vs {len(e["loads"])} PT_LOAD')
    for s, p in zip(segs, e['loads']):
        i = s['index']
        for k, pk in [('p_offset', 'off'), ('p_vaddr', 'vaddr'), ('p_paddr', 'paddr'), ('p_filesz', 'filesz'),
                      ('p_memsz', 'memsz'), ('p_align', 'align')]:
            want(s[k] == p[pk], f'seg {i} {k}')
        want(p['paddr'] == p['vaddr'], f'seg {i} paddr != vaddr')
        want((s['r'], s['w'], s['x']) == (bool(p['flags'] & 4), bool(p['flags'] & 2), bool(p['flags'] & 1)),
             f'seg {i} flags')
        blob = (out / s['blob']).read_bytes()
        want(blob == elf[p['off']:p['off'] + p['filesz']], f'seg {i} blob bytes')
        want(s['file_sha256'] == hashlib.sha256(blob).hexdigest(), f'seg {i} blob sha256')
        want(s['file'] == {'start': p['vaddr'], 'end': p['vaddr'] + p['filesz']}, f'seg {i} file range')
        z = {'start': p['vaddr'] + p['filesz'], 'end': p['vaddr'] + p['memsz']} if p['memsz'] > p['filesz'] else None
        want(s['zero'] == z, f'seg {i} zero range')
    loads = e['loads']
    for sec in e['secs']:
        if not sec['flags'] & SHF_ALLOC or sec['size'] == 0:
            continue
        a, n = sec['addr'], sec['size']
        if sec['type'] == SHT_NOBITS:
            ok = any(p['vaddr'] + p['filesz'] <= a and a + n <= p['vaddr'] + p['memsz'] for p in loads)
            want(ok, f'section {sec["name"]} not in a zero range')
        else:
            hit = [p for p in loads if p['vaddr'] <= a and a + n <= p['vaddr'] + p['filesz']]
            if not hit:
                errs.append(f'section {sec["name"]} not in a file range')
                continue
            p = hit[0]
            s = next((s for s in segs if s['p_vaddr'] == p['vaddr']), None)
            if s is None:
                errs.append(f'section {sec["name"]}: no manifest segment at {p["vaddr"]:#x}')
                continue
            blob = (out / s['blob']).read_bytes()
            want(blob[a - p['vaddr']:a - p['vaddr'] + n] == elf[sec['off']:sec['off'] + n],
                 f'section {sec["name"]} bytes')
    want(any(p['flags'] & 1 and p['vaddr'] <= e['entry'] and e['entry'] + 2 <= p['vaddr'] + p['filesz']
             for p in loads), 'entry not in executable file bytes')
    return errs


def self_test(elf_path, out):
    def mutate(f):
        d = Path(tempfile.mkdtemp(dir='/dev/shm'))
        try:
            shutil.copytree(out, d / 'x')
            f(d / 'x')
            return check(elf_path, d / 'x')
        finally:
            shutil.rmtree(d)
    def flip(d):
        b = bytearray((d / 'seg-0.bin').read_bytes()); b[1000] ^= 1; (d / 'seg-0.bin').write_bytes(bytes(b))
    def edit(f):
        def g(d):
            m = json.loads((d / 'manifest.json').read_text()); f(m); (d / 'manifest.json').write_text(json.dumps(m))
        return g
    controls = [
        ('flipped byte in seg-0.bin', flip),
        ('segment 1 shifted by 4', edit(lambda m: m['segments'][1].update(p_vaddr=m['segments'][1]['p_vaddr'] + 4))),
        ('last segment dropped', edit(lambda m: m['segments'].pop())),
        ('wrong blob hash', edit(lambda m: m['segments'][2].update(file_sha256='0' * 64))),
        ('zero range removed', edit(lambda m: m['segments'][-1].update(zero=None))),
    ]
    bad = 0
    for name, f in controls:
        errs = mutate(f)
        print(f'{"ok  " if errs else "FAIL"} control {name}: {"detected: " + errs[0] if errs else "NOT detected"}')
        bad += not errs
    return bad


def main():
    elf, out = sys.argv[1], Path(sys.argv[2])
    errs = check(elf, out)
    for x in errs:
        print('MISMATCH', x)
    print(f'{"ok  " if not errs else "FAIL"} export {out} matches {elf}')
    bad = self_test(elf, out) if '--self-test' in sys.argv else 0
    sys.exit(1 if errs or bad else 0)


if __name__ == '__main__':
    main()
