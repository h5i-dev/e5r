import NoCompiler.Mem

/-
The data of a binary: every allocated section that is not code (`.rodata`,
`.data`, `.bss`, ...), as `nocompiler export` writes it next to the code image.

A proof that reads a constant (a string in `.rodata`, a table in `.data`)
assumes `Segment.Loaded` for its segment at entry, the way it assumes
`Code.Loaded` for the code: it is what the loader establishes. `nocompiler-audit`
re-reads each segment from the ELF file in Lean and checks it byte for byte
against the exported one, so the exporter is not trusted for the contents.
-/
namespace NoCompiler

structure Segment where
  name : String
  base : Word
  bytes : Array Byte
  /-- The section is writable (SHF_WRITE): a proof cannot assume it unchanged
      after code it does not control has run. -/
  writable : Bool
  deriving DecidableEq

namespace Segment

/-- Memory holds the segment. -/
def Loaded (g : Segment) (m : Word → Byte) : Prop :=
  ∀ i (h : i < g.bytes.size), m (g.base + BitVec.ofNat 64 i) = g.bytes[i]

def region (g : Segment) : Region := ⟨g.base, g.bytes.size⟩

/-- Reading `n` bytes at offset `o` of a loaded segment. -/
theorem readBytes_of_loaded {g : Segment} {m : Word → Byte} (h : g.Loaded m) :
    ∀ (o n : Nat), o + n ≤ g.bytes.size →
      readBytes m (g.base + BitVec.ofNat 64 o) n = (g.bytes.toList.drop o).take n := by
  intro o n
  induction n generalizing o with
  | zero => intro _; simp [readBytes]
  | succ n ih =>
    intro hon
    have ho : o < g.bytes.size := by omega
    simp only [readBytes]
    have e : g.base + BitVec.ofNat 64 o + 1 = g.base + BitVec.ofNat 64 (o + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [h o ho, e, ih (o + 1) (by omega)]
    have hl : o < g.bytes.toList.length := by simpa using ho
    have : List.drop o g.bytes.toList = g.bytes.toList[o] :: List.drop (o + 1) g.bytes.toList :=
      List.drop_eq_getElem_cons hl
    rw [this]
    simp

end Segment

end NoCompiler
