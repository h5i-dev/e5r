import E5R.Step

/-
Reading `.text` out of an ELF64 little-endian file, in Lean.

Used by Audit.lean to check that the code image a proof is about (exported
by the Rust tool) holds exactly the words of the binary on disk, so neither
the exporter nor its ELF reader has to be trusted. Only what that check
needs is read: the section headers, their names, and `.text`.
-/
namespace E5R.Elf

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
  addr : Nat
  offset : Nat
  size : Nat

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
  let hdr (i : Nat) : Except String (Nat × Nat × Nat × Nat) := do
    let o := shoff + i * shentsize
    return (← le b o 4, ← le b (o + 16) 8, ← le b (o + 24) 8, ← le b (o + 32) 8)
  let (_, _, stroff, _) ← hdr shstrndx
  (List.range shnum).mapM fun i => do
    let (name, addr, offset, size) ← hdr i
    return { name := ← cstr b (stroff + name), addr, offset, size }

/-- The `.text` section as a code image. -/
def text (b : ByteArray) : Except String Code := do
  let some t := (← sections b).find? (·.name == ".text") | throw "no .text"
  if t.size % 4 != 0 then throw ".text is not whole words"
  if t.offset + t.size > b.size then throw ".text extends past the end of the file"
  let words ← (List.range (t.size / 4)).mapM fun i => do
    return BitVec.ofNat 32 (← le b (t.offset + 4 * i) 4)
  return ⟨BitVec.ofNat 64 t.addr, words.toArray⟩

end E5R.Elf
