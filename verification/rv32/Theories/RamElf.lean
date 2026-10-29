/-
  Independent reader of a RAM-resident ELF32 image (QEMU `virt`, `-bios
  none`), for RAM-image boards. Original e5r code, Apache-2.0.

  Written against the ELF specification and the board's image placement
  (`boards/qemu-virt-rv32.json`), not translated from the Rust exporter.

  The file is given packed (`File`: its length and 64-byte little-endian
  words), the only form in which a few hundred KiB elaborate and evaluate
  in the kernel. The model's image is *defined* as this reader's output
  (`imageOf`), so the image is a function of the file's bytes by
  construction; the kernel only decides that the reader accepts the file
  (`accepts`), which reads the headers and never forces segment bytes.

  Every PT_LOAD is loaded in place (p_paddr = p_vaddr) inside DRAM. A
  read-only one becomes an immutable image segment holding its file bytes
  followed by zeros up to p_memsz; a writable one is initial RAM data. All
  read-only segments lie below every writable one, so model RAM can begin
  at `rwBase`, the end of the highest read-only segment.
-/
import Theories.Platform

namespace E5R.RamElf
open E5R

/-- A file: `len` bytes, packed little-endian into 64-byte words. -/
structure File where
  len : Nat
  words : List Nat

/-- The `n` low bytes of `x`, least significant first. -/
def unpackN : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, x => x % 256 :: unpackN n (x / 256)

/-- Byte `i` of the file (0 past its end). -/
def File.byte (f : File) (i : Nat) : Nat :=
  if i < f.len then f.words.getD (i / 64) 0 / 256 ^ (i % 64) % 256 else 0

/-- Bytes `[off, off + n)` of the file, read word by word. -/
def File.slice (f : File) (off n : Nat) : List Nat :=
  go (f.words.drop (off / 64)) (off % 64) n
where
  go : List Nat → Nat → Nat → List Nat
    | _, _, 0 => []
    | [], _, n => List.replicate n 0
    | w :: ws, k, n =>
      let bs := (unpackN 64 w).drop k
      if n ≤ bs.length then bs.take n else bs ++ go ws 0 (n - bs.length)

/-- Little-endian field of `width` bytes. -/
def le (f : File) (off width : Nat) : Except String Nat := do
  if off + width > f.len then throw s!"truncated at {off}"
  return (List.range width).foldr (fun k acc => acc * 256 + f.byte (off + k)) 0

def inside (a n base size : Nat) : Bool := base ≤ a && a + n ≤ base + size

structure Image where
  entry : Nat
  /-- The read-only PT_LOADs: the immutable image. -/
  ro : List Segment
  /-- The writable PT_LOADs: (address, file bytes, memory size). -/
  rw : List (Nat × List Nat × Nat)
  /-- The first byte after the read-only segments: where model RAM starts. -/
  rwBase : Nat

/-- One accepted PT_LOAD: address, memory size, write, exec, file offset and size. -/
structure Load where
  vaddr : Nat
  memsz : Nat
  write : Bool
  exec : Bool
  off : Nat
  filesz : Nat

/-- The PT_LOADs of program headers `i, i+1, ...`; `last` is the end of the
    previous one, for the ordering/overlap rule. -/
def headers (base size : Nat) (f : File) (phoff : Nat) :
    Nat → Nat → Nat → Except String (List Load)
  | 0, _, _ => pure []
  | n+1, i, last => do
    let at_ (k : Nat) := le f (phoff + 32 * i + k) 4
    let kind ← at_ 0
    -- PT_NULL, PT_GNU_STACK and PT_RISCV_ATTRIBUTES describe no memory.
    if kind = 0 || kind = 0x6474e551 || kind = 0x70000003 then
      return ← headers base size f phoff n (i+1) last
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
    if file + filesz > f.len then throw "file bytes outside the file"
    if vaddr < last then throw "overlapping or out of order"
    let rest ← headers base size f phoff n (i+1) (vaddr + memsz)
    return ⟨vaddr, memsz, write, exec, file, filesz⟩ :: rest

/-- The checked load list, entry and rwBase (no segment bytes). -/
def check (base size : Nat) (f : File) : Except String (Nat × List Load × Nat) := do
  if f.len < 52 || f.len > 16777216 then throw "size"
  if f.words.length ≠ (f.len + 63) / 64 then throw "packing"
  if (← le f 0 4) ≠ 0x464c457f || (← le f 4 3) ≠ 0x010101 then throw "not ELF32 LE"
  if (← le f 16 2) ≠ 2 || (← le f 18 2) ≠ 243 || (← le f 20 4) ≠ 1 then throw "not RISC-V ET_EXEC"
  let flags ← le f 36 4
  if flags ≠ 0 && flags ≠ 1 then throw "e_flags"
  if (← le f 40 2) ≠ 52 || (← le f 42 2) ≠ 32 then throw "header sizes"
  let count ← le f 44 2
  if count = 0 || count > 16 then throw "program header count"
  let loads ← headers base size f (← le f 28 4) count 0 0
  let ro := loads.filter (!·.write)
  if ro.foldl (fun n l => n + l.memsz) 0 > 4194304 then throw "too much image"
  let rwBase := ro.foldl (fun m l => max m (l.vaddr + l.memsz)) base
  if !loads.all (fun l => !l.write || rwBase ≤ l.vaddr) then throw "writable segment below a read-only one"
  let entry ← le f 24 4
  if entry % 2 ≠ 0 || !ro.any (fun l => l.exec && inside entry 2 l.vaddr l.memsz) then throw "entry"
  return (entry, loads, rwBase)

/-- The reader accepts the file (decided by the kernel for a given file). -/
def accepts (base size : Nat) (f : File) : Bool :=
  match check base size f with
  | .ok _ => true
  | .error _ => false

/-- The image the model runs: segment bytes are slices of the file. -/
def imageOf (base size : Nat) (f : File) : Image :=
  match check base size f with
  | .ok (entry, loads, rwBase) =>
    { entry, rwBase
      ro := (loads.filter (!·.write)).map fun l =>
        ⟨l.vaddr, f.slice l.off l.filesz ++ List.replicate (l.memsz - l.filesz) 0, l.exec⟩
      rw := (loads.filter (·.write)).map fun l => (l.vaddr, f.slice l.off l.filesz, l.memsz) }
  | .error _ => ⟨0, [], [], base + size⟩

end E5R.RamElf
