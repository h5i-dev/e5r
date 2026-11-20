import NoCompiler.Image

/-
Reading `.text` and the data sections out of an ELF64 little-endian file,
in Lean.

Used by Audit.lean to check that the code image and the data segments a
proof is about (exported by the Rust tool) hold exactly the bytes of the
binary on disk, so neither the exporter nor its ELF reader has to be
trusted. Only what that check needs is read: the section headers, their
names, types and flags, and the sections' bytes.
-/
namespace NoCompiler.Elf

def le (b : ByteArray) (o n : Nat) : Except String Nat :=
  if o + n ≤ b.size then
    .ok <| (List.range n).foldr (fun i acc => acc * 256 + (b.get! (o + i)).toNat) 0
  else .error s!"truncated at offset {o}"

def cstr (b : ByteArray) (o : Nat) : Except String String := do
  let mut cs : List Char := []
  let mut i := o
  while true do
    if i ≥ b.size then throw s!"unterminated name at {o}"
    let c := b.get! i
    if c = 0 then break
    cs := cs ++ [Char.ofNat c.toNat]
    i := i + 1
  return String.ofList cs

structure Section where
  name : String
  kind : Nat
  flags : Nat
  addr : Nat
  offset : Nat
  size : Nat
  link : Nat := 0

def sections (b : ByteArray) : Except String (List Section) := do
  if b.size < 64 || b.get! 0 != 0x7f || b.get! 1 != 0x45 || b.get! 2 != 0x4c || b.get! 3 != 0x46 then
    throw "not an ELF file"
  if b.get! 4 != 2 then throw "not ELF64"
  if b.get! 5 != 1 then throw "not little-endian"
  if (← le b 18 2) != 243 then throw "not RISC-V"
  let shoff ← le b 40 8
  let shentsize ← le b 58 2
  let shnum ← le b 60 2
  let shstrndx ← le b 62 2
  let hdr (i : Nat) : Except String (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
    let o := shoff + i * shentsize
    return (← le b o 4, ← le b (o + 4) 4, ← le b (o + 8) 8, ← le b (o + 16) 8,
      ← le b (o + 24) 8, ← le b (o + 32) 8, ← le b (o + 40) 4)
  let (_, _, _, _, stroff, _, _) ← hdr shstrndx
  (List.range shnum).mapM fun i => do
    let (name, kind, flags, addr, offset, size, link) ← hdr i
    return { name := ← cstr b (stroff + name), kind, flags, addr, offset, size, link }

/-- The `.text` section as a code image. -/
def text (b : ByteArray) : Except String Code := do
  let some t := (← sections b).find? (·.name == ".text") | throw "no .text"
  if t.size % 4 != 0 then throw ".text is not whole words"
  if t.offset + t.size > b.size then throw ".text extends past the end of the file"
  let words ← (List.range (t.size / 4)).mapM fun i => do
    return BitVec.ofNat 32 (← le b (t.offset + 4 * i) 4)
  return ⟨BitVec.ofNat 64 t.addr, words.toArray⟩

def SHT_PROGBITS : Nat := 1
def SHT_NOBITS : Nat := 8
def SHF_WRITE : Nat := 1
def SHF_ALLOC : Nat := 2
def SHF_EXECINSTR : Nat := 4

def flag (flags f : Nat) : Bool := flags / f % 2 == 1

/-- Every allocated, non-executable PROGBITS or NOBITS section with bytes in
    it, in section-header order: what the process image holds besides code.
    NOBITS (`.bss`) is zeros. -/
def segments (b : ByteArray) : Except String (List Segment) := do
  let secs := (← sections b).filter fun s =>
    flag s.flags SHF_ALLOC && !flag s.flags SHF_EXECINSTR && s.size > 0 &&
      (s.kind == SHT_PROGBITS || s.kind == SHT_NOBITS)
  secs.mapM fun s => do
    let bytes ← if s.kind == SHT_NOBITS then pure (Array.replicate s.size 0) else do
      if s.offset + s.size > b.size then throw s!"{s.name} extends past the end of the file"
      pure ((List.range s.size).map fun i => BitVec.ofNat 8 (b.get! (s.offset + i)).toNat).toArray
    return { name := s.name, base := BitVec.ofNat 64 s.addr, bytes, writable := flag s.flags SHF_WRITE }

/-- The function symbols (`STT_FUNC`, nonzero size) of `.symtab`: name and address. -/
def funcSymbols (b : ByteArray) : Except String (List (String × Nat)) := do
  let secs ← sections b
  let some st := secs.find? (·.kind == 2) | return []
  let some str := secs[st.link]? | throw "the symbol table links no string table"
  let n := st.size / 24
  let syms ← (List.range n).mapM fun i => do
    let o := st.offset + 24 * i
    let name ← cstr b (str.offset + (← le b o 4))
    return (name, (← le b (o + 4) 1) % 16, ← le b (o + 8) 8, ← le b (o + 16) 8)
  return (syms.filter fun (_, ty, _, sz) => ty == 2 && sz > 0).map fun (nm, _, v, _) => (nm, v)

end NoCompiler.Elf
