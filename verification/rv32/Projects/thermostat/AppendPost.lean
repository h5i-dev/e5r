import Projects.thermostat.FormatCursor
namespace E5R.Thermostat.AppendPost
open E5R E5R.Thermostat

/-- Byte append/refusal with an explicit enclosing scratch allocation size. -/
structure Post (B : Board) (c d : Core) (before after : Word → BitVec 8) (sp obj dst : Word)
    (scratch cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  returned : FormatCursor.Returned c d
  result : d.get 10 = Cursor.resultWord cap pos xs.length
  pointer : ramRead after obj .w = dst
  capacity : ramRead after (obj+4#32) .w = BitVec.ofNat 32 cap
  position : ramRead after (obj+8#32) .w = BitVec.ofNat 32 (Cursor.nextPosition cap pos xs.length)
  written : pos+xs.length ≤ cap → Bytes.Span B after (dst+BitVec.ofNat 32 pos) xs
  refused : ¬pos+xs.length ≤ cap → ∀ x, (∀ i : Fin scratch, x ≠ sp+BitVec.ofNat 32 i.val) → after x = before x
  frame : ∀ x, (∀ i : Fin scratch, x ≠ sp+BitVec.ofNat 32 i.val) →
    (∀ i : Fin xs.length, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 4, x ≠ (obj+8#32)+BitVec.ofNat 32 i.val) → after x = before x
end E5R.Thermostat.AppendPost
