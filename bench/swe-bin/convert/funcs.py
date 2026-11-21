"""Per-function canonical forms of a linked RISC-V ELF (linked with --emit-relocs).

A function's key is its relocatable form:
  * its bytes, with every relocated field zeroed (by relocation type);
  * each relocation as (offset in the function, type, target).
The target is the named symbol that holds the target address, plus the offset into it. For a
PCREL_LO12 relocation, which points at its auipc, it is the auipc's offset in the function.
The key does not depend on where the function or its targets are linked, so two builds of the
same source agree on every function that did not change. That is the same idea as nocompiler's
`module::canonical`. This file is independent of it because `nocompiler ledger` refuses whole
Linux binaries: on jq, "__cos: the auipc at 0xda18c has no low part" (an fld's low part, which
is outside the profile).

Only the dataset converter uses this, to say which functions the gold patch changes. Nothing in
it is an input to a reward.
"""

from __future__ import annotations

import bisect
import hashlib
import struct
import sys
from dataclasses import dataclass

from elftools.elf.elffile import ELFFile
from elftools.elf.relocation import RelocationSection

# Field masks of the instruction word(s) each relocation type writes.
U = 0xFFFFF000  # U-type imm[31:12]
I = 0xFFF00000  # I-type imm[11:0]
S = 0xFE000F80  # S-type imm (also B-type)
J = 0xFFFFF000  # J-type
MASKS = {
    16: [S],  # BRANCH
    17: [J],  # JAL
    18: [U, I],  # CALL (auipc + jalr)
    19: [U, I],  # CALL_PLT
    20: [U], 21: [U], 22: [U], 23: [U], 26: [U], 29: [U],  # *_HI20
    24: [I], 27: [I], 30: [I],  # *_LO12_I
    25: [S], 28: [S], 31: [S],  # *_LO12_S
}
PCREL_LO = {24, 25}
IGNORED = {43, 51, 32}  # ALIGN, RELAX, TPREL_ADD: no field


@dataclass
class Func:
    key: str  # "file::name" for local symbols, "name" for global ones
    name: str
    addr: int
    size: int
    sha256: str

    @property
    def insns(self) -> int:
        return self.size // 4


def _symbols(elf):
    symtab = elf.get_section_by_name(".symtab")
    if symtab is None:
        raise SystemExit("no .symtab: the binary must not be stripped")
    funcs, named = [], []
    cur_file = ""
    for s in symtab.iter_symbols():
        t, b = s["st_info"]["type"], s["st_info"]["bind"]
        if t == "STT_FILE":
            cur_file = s.name
            continue
        if not s.name or s["st_shndx"] in ("SHN_UNDEF", "SHN_ABS"):
            continue
        if t in ("STT_FUNC", "STT_OBJECT", "STT_TLS") or (t == "STT_NOTYPE" and not s.name.startswith(".L")):
            named.append((s["st_value"], s["st_size"], s.name))
        if t in ("STT_FUNC", "STT_OBJECT") and s["st_size"] > 0:
            key = s.name if b != "STB_LOCAL" else f"{cur_file}::{s.name}"
            funcs.append((s["st_value"], s["st_size"], s.name, key, t == "STT_FUNC"))
    named.sort()
    return funcs, named, symtab


def _resolver(named):
    addrs = [a for a, _, _ in named]

    def resolve(target: int) -> str:
        i = bisect.bisect_right(addrs, target) - 1
        # prefer a symbol that contains the target; else the nearest one below it
        j = i
        while j >= 0 and addrs[j] == addrs[i]:
            a, sz, n = named[j]
            if a <= target < a + max(sz, 1):
                return f"{n}+{target - a}"
            j -= 1
        if i >= 0:
            a, _, n = named[i]
            return f"{n}+{target - a}"
        return f"?+{target}"

    return resolve


def canonical_funcs(path: str) -> dict[str, Func]:
    return canonical(path)[0]


def canonical(path: str):
    """(functions, data objects): key -> Func, for both kinds."""
    with open(path, "rb") as fh:
        elf = ELFFile(fh)
        funcs, named, symtab = _symbols(elf)
        resolve = _resolver(named)
        # text bytes by address
        segs = []
        for sec in elf.iter_sections():
            if sec["sh_flags"] & 0x2 and sec["sh_type"] == "SHT_PROGBITS":  # SHF_ALLOC, with contents
                segs.append((sec["sh_addr"], sec.data()))
        relocs = []  # (addr, type, target address, sym name)
        for sec in elf.iter_sections():
            if not isinstance(sec, RelocationSection):
                continue
            tgt = elf.get_section(sec["sh_info"])
            if not (tgt["sh_flags"] & 0x2):
                continue
            for r in sec.iter_relocations():
                sym = symtab.get_symbol(r["r_info_sym"])
                relocs.append((r["r_offset"], r["r_info_type"], sym["st_value"] + r["r_addend"]))
        relocs.sort()
        raddrs = [r[0] for r in relocs]

        def read(addr, size):
            for a, d in segs:
                if a <= addr and addr + size <= a + len(d):
                    return bytearray(d[addr - a : addr - a + size])
            raise ValueError(hex(addr))

        out: dict[str, Func] = {}
        data: dict[str, Func] = {}
        for addr, size, name, key, is_func in funcs:
            try:
                b = read(addr, size)
            except ValueError:  # .bss and other sections without contents
                if is_func:
                    continue
                b = bytearray(size)
            lines = []
            lo = bisect.bisect_left(raddrs, addr)
            hi = bisect.bisect_left(raddrs, addr + size)
            for off_abs, typ, target in relocs[lo:hi]:
                off = off_abs - addr
                if typ in IGNORED:
                    continue
                masks = MASKS.get(typ, []) if is_func else []
                if not is_func and typ in (1, 2):  # R_RISCV_32 / R_RISCV_64: a whole pointer
                    n = 4 if typ == 1 else 8
                    b[off : off + n] = bytes(n)
                for k, m in enumerate(masks):
                    o = off + 4 * k
                    if o + 4 <= size:
                        (w,) = struct.unpack_from("<I", b, o)
                        struct.pack_into("<I", b, o, w & ~m & 0xFFFFFFFF)
                if typ in PCREL_LO and addr <= target < addr + size:
                    t = f"self+{target - addr}"
                else:
                    t = resolve(target)
                lines.append(f"reloc {off} {typ} {t}")
            h = hashlib.sha256()
            h.update(b"swe-bin-rfunc 1\n")
            h.update(bytes(b))
            h.update("\n".join(lines).encode())
            dst = out if is_func else data
            if key in dst:  # same local name twice in one file: keep both
                key = f"{key}@{len([k for k in dst if k.startswith(key)])}"
            dst[key] = Func(key, name, addr, size, h.hexdigest())
        return out, data


def changed(base: dict[str, Func], gold: dict[str, Func]):
    """Functions the gold build changes: (modified, added, removed), by key."""
    mod = sorted(k for k in base.keys() & gold.keys() if base[k].sha256 != gold[k].sha256)
    add = sorted(gold.keys() - base.keys())
    rem = sorted(base.keys() - gold.keys())
    return mod, add, rem


if __name__ == "__main__":
    a, ad_ = canonical(sys.argv[1])
    if len(sys.argv) > 2:
        b, bd_ = canonical(sys.argv[2])
        m, ad, rm = changed(ad_, bd_)
        print(f"data objects: modified {len(m)}, added {len(ad)}, removed {len(rm)}:", " ".join(m + ad + rm)[:2000])
        m, ad, rm = changed(a, b)
        print(f"functions: {len(a)} / {len(b)}; modified {len(m)}, added {len(ad)}, removed {len(rm)}")
        for k in m:
            print("M", k, a[k].insns, "->", b[k].insns)
        for k in ad:
            print("A", k, b[k].insns)
        for k in rm:
            print("R", k, a[k].insns)
    else:
        print(len(a), "functions,", sum(f.insns for f in a.values()), "instructions")
