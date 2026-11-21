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
import os
import hashlib
import re
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
            nm = LLVM_SUFFIX.sub("", s.name)
            key = nm if b != "STB_LOCAL" else f"{cur_file}::{nm}"
            funcs.append((s["st_value"], s["st_size"], s.name, key, t == "STT_FUNC"))
    named.sort()
    return funcs, named, symtab


LLVM_SUFFIX = re.compile(r"\.llvm\.\d+$")
# anonymous constants: names that carry a per-build hash (rustc's anon.<hash>.N, alloc_<hash>)
ANON = re.compile(r"^(anon\.|\.Lanon|alloc_[0-9a-f]{8,}|str\.\d|\.L)")


def _resolver(named, content):
    """target address -> a layout-independent name for it.

    The named symbol with a size that holds the target, plus the offset into it; a symbol whose
    name is per-build (an anonymous constant) is named by its content instead. Else a symbol at
    exactly that address; else the nearest sized symbol below (marked "~", which can make
    unchanged code look changed when the gap moves, never the other way)."""
    sized = [x for x in named if x[1] > 0]
    starts = [a for a, _, _ in sized]
    exact = {}
    for a, _, n in named:
        exact.setdefault(a, n)

    def name(a, sz, n):
        n = LLVM_SUFFIX.sub("", n)
        if ANON.match(n):
            return "lit:" + hashlib.sha256(content(a, sz)).hexdigest()[:16]
        return n

    def resolve(target: int) -> str:
        i = bisect.bisect_right(starts, target) - 1
        for j in range(i, max(i - 64, -1), -1):
            a, sz, n = sized[j]
            if a <= target < a + sz:
                return f"{name(a, sz, n)}+{target - a}"
        if target in exact:
            return f"{LLVM_SUFFIX.sub('', exact[target])}+0"
        if i >= 0:
            a, sz, n = sized[i]
            return f"~{name(a, sz, n)}+{target - a}"
        return f"?+{target}"

    return resolve


def canonical_funcs(path: str) -> dict[str, Func]:
    return canonical(path)[0]


def canonical(path: str):
    """(functions, data objects): key -> Func, for both kinds."""
    with open(path, "rb") as fh:
        elf = ELFFile(fh)
        funcs, named, symtab = _symbols(elf)
        def content(a, sz):
            try:
                return bytes(read(a, sz))
            except ValueError:
                return b"\0" * sz

        resolve = _resolver(named, content)
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
        calls: dict[str, set] = {}
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
            frel = list(relocs[lo:hi])
            if is_func:
                frel += implicit_calls(b, addr, size, {r[0] for r in frel})
                frel.sort()
                calls.setdefault(name, set()).update(t for _, ty, t in frel if ty in (17, 18, 19))
            for off_abs, typ, target in frel:
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
            if os.environ.get("SWB_FUNCS_DEBUG") == name:
                sys.stderr.write(f"== {path} {name}\n" + bytes(b).hex() + "\n" + "\n".join(lines) + "\n")
            h = hashlib.sha256()
            h.update(b"swe-bin-rfunc 1\n")
            h.update(bytes(b))
            h.update("\n".join(lines).encode())
            dst = out if is_func else data
            if key in dst:  # same local name twice in one file: keep both
                key = f"{key}@{len([k for k in dst if k.startswith(key)])}"
            dst[key] = Func(key, name, addr, size, h.hexdigest())
        global LAST_CALLS
        LAST_CALLS = {n: sorted(t) for n, t in calls.items()}
        return out, data


LAST_CALLS: dict = {}  # name -> call targets (addresses), of the last canonical() call


def implicit_calls(b: bytes, addr: int, size: int, have: set):
    """Calls and jumps out of the function that carry no relocation: to a function of the same
    section, which the assembler resolved itself (-mno-relax). As (address, JAL or CALL, target)."""
    out = []
    n = size // 4
    ws = [struct.unpack_from("<I", b, 4 * k)[0] for k in range(n)]
    for k, w in enumerate(ws):
        a = addr + 4 * k
        if a in have:
            continue
        if w & 0x7F == 0x6F:
            imm = (((w >> 31) & 1) << 20) | (((w >> 21) & 0x3FF) << 1) | (((w >> 20) & 1) << 11) | (((w >> 12) & 0xFF) << 12)
            if imm & (1 << 20):
                imm -= 1 << 21
            t = a + imm
            if not (addr <= t < addr + size):
                out.append((a, 17, t))
        elif w & 0x7F == 0x17 and k + 1 < n:
            w2 = ws[k + 1]
            if w2 & 0x707F == 0x67 and (w2 >> 15) & 0x1F == (w >> 7) & 0x1F:
                hi = w & 0xFFFFF000
                if hi & 0x80000000:
                    hi -= 1 << 32
                lo_ = w2 >> 20
                if lo_ & 0x800:
                    lo_ -= 1 << 12
                t = a + hi + lo_
                if not (addr <= t < addr + size):
                    out.append((a, 18, t))
    return out


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


# ---- source-level changes ---------------------------------------------------------------------

def patch_lines(patch: str):
    """{path: (old lines, new lines)} the patch touches. Old: removed lines, and the line before
    each run of added lines (where code goes in). New: added lines."""
    out = {}
    path = None
    old_l = new_l = 0
    for line in patch.splitlines():
        if line.startswith("diff --git"):
            path = None
        elif line.startswith("+++ "):
            p = line[4:].strip()
            path = p[2:] if p.startswith("b/") else None
            if path:
                out.setdefault(path, (set(), set()))
        elif line.startswith("@@") and path:
            m = re.match(r"@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@", line)
            old_l, new_l = int(m.group(1)), int(m.group(2))
            prev_added = False
        elif path and line.startswith("-") and not line.startswith("---"):
            out[path][0].add(old_l)
            old_l += 1
            prev_added = False
        elif path and line.startswith("+"):
            out[path][1].add(new_l)
            if not prev_added:
                out[path][0].add(max(old_l - 1, 1))
            new_l += 1
            prev_added = True
        elif path and line.startswith(" "):
            old_l += 1
            new_l += 1
            prev_added = False
    return out


def functions_at_lines(debug_elf: str, lines_by_path: dict) -> list[str]:
    """The functions of a binary (linked with -g) whose code comes from one of the given lines,
    by the DWARF line tables: inlined copies count for the function they are inlined into."""
    want = {p: ls for p, ls in lines_by_path.items() if ls}
    if not want:
        return []
    with open(debug_elf, "rb") as fh:
        elf = ELFFile(fh)
        if not elf.has_dwarf_info():
            return []
        funcs, _, _ = _symbols(elf)
        fl = sorted((a, sz, n) for a, sz, n, _, is_f in funcs if is_f)
        starts = [a for a, _, _ in fl]
        hits = set()
        dw = elf.get_dwarf_info(relocate_dwarf_sections=False)  # linked: --emit-relocs kept .rela.debug_*
        for cu in dw.iter_CUs():
            lp = dw.line_program_for_CU(cu)
            if lp is None:
                continue
            hdr = lp.header
            names = []
            ver = hdr["version"]
            dirs = [d if isinstance(d, str) else d.decode(errors="replace") for d in hdr["include_directory"]]
            top = cu.get_top_DIE().attributes.get("DW_AT_comp_dir")
            comp = top.value.decode(errors="replace") if top is not None and isinstance(top.value, bytes) else ""
            for fe in hdr["file_entry"]:
                n = fe.name.decode(errors="replace") if isinstance(fe.name, bytes) else fe.name
                di = fe.dir_index
                # DWARF 5: directory 0 is the compilation directory; DWARF 4: index 0 means it
                d = dirs[di] if ver >= 5 and di < len(dirs) else (dirs[di - 1] if 0 < di <= len(dirs) else "")
                names.append(os.path.normpath(os.path.join(comp, d, n)))
            # which file indices are patched files, and their line sets
            idx = {}
            for i, full in enumerate(names):
                for p, ls in want.items():
                    if full.endswith("/" + p) or full == p:
                        idx[i if ver >= 5 else i + 1] = ls
            if not idx:
                continue
            for ent in lp.get_entries():
                st = ent.state
                if st is None or st.end_sequence:
                    continue
                ls = idx.get(st.file)
                if ls and st.line in ls:
                    k = bisect.bisect_right(starts, st.address) - 1
                    if k >= 0 and fl[k][0] <= st.address < fl[k][0] + fl[k][1]:
                        hits.add(fl[k][2])
        return sorted(hits)


def callers(path: str, names: list[str]) -> dict:
    """name -> the functions that call or jump to it (relocations plus decoded calls)."""
    fs, _ = canonical(path)
    at = {f.addr: f.name for f in fs.values()}
    want = {a: n for a, n in at.items() if n in names}
    out = {n: set() for n in names}
    for caller, targets in LAST_CALLS.items():
        for t in targets:
            if t in want and caller != want[t]:
                out[want[t]].add(caller)
    return {n: sorted(v) for n, v in out.items()}


def _type_name(die, depth=0):
    if die is None:
        return "void"
    if depth > 12:
        return "..."
    tag = die.tag
    name = die.attributes.get("DW_AT_name")
    nm = name.value.decode(errors="replace") if name else None
    sub = die.get_DIE_from_attribute("DW_AT_type") if "DW_AT_type" in die.attributes else None
    if tag == "DW_TAG_pointer_type":
        return _type_name(sub, depth + 1) + " *"
    if tag == "DW_TAG_const_type":
        return "const " + _type_name(sub, depth + 1)
    if tag == "DW_TAG_volatile_type":
        return "volatile " + _type_name(sub, depth + 1)
    if tag in ("DW_TAG_typedef", "DW_TAG_base_type"):
        return nm or "?"
    if tag == "DW_TAG_structure_type":
        return f"struct {nm or '(anonymous)'}"
    if tag == "DW_TAG_union_type":
        return f"union {nm or '(anonymous)'}"
    if tag == "DW_TAG_enumeration_type":
        return f"enum {nm or '(anonymous)'}"
    if tag == "DW_TAG_array_type":
        return _type_name(sub, depth + 1) + " []"
    if tag == "DW_TAG_subroutine_type":
        return _type_name(sub, depth + 1) + " (*)(...)"
    return nm or tag


def signatures(debug_elf: str, names: list[str]) -> dict:
    """name -> a C prototype from the DWARF of a -g build (types only, no source)."""
    out = {}
    want = set(names)
    with open(debug_elf, "rb") as fh:
        elf = ELFFile(fh)
        if not elf.has_dwarf_info():
            return out
        dw = elf.get_dwarf_info(relocate_dwarf_sections=False)
        for cu in dw.iter_CUs():
            for conc in cu.iter_DIEs():
                if conc.tag != "DW_TAG_subprogram" or "DW_AT_low_pc" not in conc.attributes:
                    continue
                # an out-of-line copy of an inline function names its abstract origin
                die = conc
                for _ in range(2):
                    if "DW_AT_name" in die.attributes:
                        break
                    org = die.attributes.get("DW_AT_abstract_origin") or die.attributes.get("DW_AT_specification")
                    if org is None:
                        break
                    die = die.get_DIE_from_attribute(org.name)
                if "DW_AT_name" not in die.attributes:
                    continue
                n = die.attributes["DW_AT_name"].value.decode(errors="replace")
                if n not in want or n in out:
                    continue
                ret = _type_name(die.get_DIE_from_attribute("DW_AT_type")) if "DW_AT_type" in die.attributes else "void"
                params = []
                for ch in die.iter_children():
                    if ch.tag == "DW_TAG_formal_parameter":
                        t = _type_name(ch.get_DIE_from_attribute("DW_AT_type")) if "DW_AT_type" in ch.attributes else "?"
                        pn = ch.attributes.get("DW_AT_name")
                        params.append(f"{t} {pn.value.decode(errors='replace')}" if pn else t)
                    elif ch.tag == "DW_TAG_unspecified_parameters":
                        params.append("...")
                static = "static " if "DW_AT_external" not in die.attributes else ""
                out[n] = f"{static}{ret} {n}({', '.join(params) or 'void'})"
    return out
