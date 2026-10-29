/-
  Independent reader of a RAM-resident ELF32 image (QEMU `virt`, `-bios
  none`), for the image-coherence theorem of RAM-image boards. Original e5r
  code, Apache-2.0.

  Written against the ELF specification and the board's image placement
  (`boards/qemu-virt-rv32.json`), not translated from the Rust exporter. A
  theorem `loadRam base size elfBytes = .ok img` makes an exported image a
  checked function of the original file bytes.

  Every PT_LOAD is loaded in place (p_paddr = p_vaddr) inside DRAM. A
  read-only one becomes an immutable image segment holding its file bytes
  followed by zeros up to p_memsz; a writable one is initial RAM data. All
  read-only segments lie below every writable one, so model RAM can begin
  at `rwBase`, the end of the highest read-only segment.
-/
import Theories.FlashElf

namespace E5R.RamElf
open E5R E5R.FlashElf

structure Image where
  entry : Nat
  /-- The read-only PT_LOADs: the immutable image. -/
  ro : List Segment
  /-- The writable PT_LOADs: (address, file bytes, memory size). -/
  rw : List (Nat × List Nat × Nat)
  /-- The first byte after the read-only segments: where model RAM starts. -/
  rwBase : Nat
  deriving Repr, DecidableEq

/-- The PT_LOADs of program headers `i, i+1, ...`; `last` is the end of the
    previous one, for the ordering/overlap rule. -/
def headers (base size : Nat) (bs : List Nat) (phoff : Nat) :
    Nat → Nat → Nat → Except String (List Segment × List (Nat × List Nat × Nat))
  | 0, _, _ => pure ([], [])
  | n+1, i, last => do
    let at_ (k : Nat) := le bs (phoff + 32 * i + k) 4
    let kind ← at_ 0
    -- PT_NULL, PT_GNU_STACK and PT_RISCV_ATTRIBUTES describe no memory.
    if kind = 0 || kind = 0x6474e551 || kind = 0x70000003 then
      return ← headers base size bs phoff n (i+1) last
    if kind ≠ 1 then throw "unsupported program header"
    let file ← at_ 4
    let vaddr ← at_ 8
    let paddr ← at_ 12
    let filesz ← at_ 16
    let memsz ← at_ 20
    let flags ← at_ 24
    if flags > 7 || flags / 4 % 2 = 0 || filesz > memsz || memsz = 0 then throw "bad PT_LOAD"
    let exec := flags % 2 = 1
    let write := flags / 2 % 2 = 1
    if exec && write then throw "writable and executable"
    if vaddr ≠ paddr then throw "not loaded in place"
    if !inside vaddr memsz base size then throw "outside DRAM"
    if file + filesz > bs.length then throw "file bytes outside the file"
    if vaddr < last then throw "overlapping or out of order"
    let (ro, rw) ← headers base size bs phoff n (i+1) (vaddr + memsz)
    let bytes := (bs.drop file).take filesz
    if write then return (ro, (vaddr, bytes, memsz) :: rw)
    else return (⟨vaddr, bytes ++ List.replicate (memsz - filesz) 0, exec⟩ :: ro, rw)

def loadRam (base size : Nat) (bs : List Nat) : Except String Image := do
  if bs.length < 52 || bs.length > 16777216 then throw "size"
  if (← le bs 0 4) ≠ 0x464c457f || (← le bs 4 3) ≠ 0x010101 then throw "not ELF32 LE"
  if (← le bs 16 2) ≠ 2 || (← le bs 18 2) ≠ 243 || (← le bs 20 4) ≠ 1 then throw "not RISC-V ET_EXEC"
  let flags ← le bs 36 4
  if flags ≠ 0 && flags ≠ 1 then throw "e_flags"
  if (← le bs 40 2) ≠ 52 || (← le bs 42 2) ≠ 32 then throw "header sizes"
  let count ← le bs 44 2
  if count = 0 || count > 16 then throw "program header count"
  let (ro, rw) ← headers base size bs (← le bs 28 4) count 0 0
  if ro.foldl (fun n s => n + s.bytes.length) 0 > 4194304 then throw "too much image"
  let rwBase := ro.foldl (fun m s => max m (s.base + s.bytes.length)) base
  if !rw.all (fun r => rwBase ≤ r.1) then throw "writable segment below a read-only one"
  let entry ← le bs 24 4
  if entry % 2 ≠ 0 || !ro.any (fun s => s.exec && inside entry 2 s.base s.bytes.length) then
    throw "entry"
  return ⟨entry, ro, rw, rwBase⟩

end E5R.RamElf
