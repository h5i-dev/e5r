import Theories.RV32
namespace RV32

/- Independent minimal ELF32 reader. This is a second modeled loader, not a
   proof of ELF specification compliance. Strict bounds precede allocations. -/
def le (bs : List Nat) (off width : Nat) : Except Fault Nat := do
  if off + width > bs.length then throw .malformed
  let bytes := (bs.drop off).take width
  if bytes.any (· ≥ 256) then throw .malformed
  return (bytes.reverse.foldl (fun acc b => acc*256+b) 0)

def loadHeaders (bs : List Nat) : Nat → Nat → Except Fault (List Region)
  | _, 0 => pure []
  | off, n+1 => do
    let kind ← le bs off 4
    let rest ← loadHeaders bs (off+32) n
    if kind = 0 || kind = 0x6474e551 then return rest
    if kind != 1 then throw .malformed
    let file ← le bs (off+4) 4
    let base ← le bs (off+8) 4
    let filesz ← le bs (off+16) 4
    let memsz ← le bs (off+20) 4
    let flags ← le bs (off+24) 4
    if filesz > memsz || memsz = 0 || memsz > 65536 ||
        file+filesz > bs.length || base+memsz > modulus || flags > 7 then
      throw .malformed
    let bytes := (bs.drop file).take filesz ++ List.replicate (memsz-filesz) 0
    return ⟨base, bytes, flags / 4 % 2 == 1, flags / 2 % 2 == 1, flags % 2 == 1⟩ :: rest

def loadElf (bs : List Nat) : Except Fault (Nat × List Region) := do
  if bs.length > 65536 || bs.length < 52 then throw .malformed
  if (← le bs 0 7) != 0x010101464c457f ||
     (← le bs 16 4) != 0x00f30002 ||
     (← le bs 20 4) != 1 || (← le bs 36 4) != 0 ||
     (← le bs 40 2) != 52 || (← le bs 42 2) != 32 then throw .malformed
  let count ← le bs 44 2
  if count = 0 || count > 16 then throw .malformed
  let regions ← loadHeaders bs (← le bs 28 4) count
  return (← le bs 24 4, regions)
end RV32
