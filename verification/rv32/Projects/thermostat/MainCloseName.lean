import Projects.thermostat.MainCloseNameChain
import Projects.thermostat.HeaderInput
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseName
open E5R E5R.Thermostat

/-- Case-insensitive name comparison against the actual RAM slice. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (name : List (BitVec 8))
    (span : Bytes.Span B ram base name) (length : name.length=10)
    (hp : c.pc=0x8000249a#32) (h15 : c.get 15=base) (literals : MainCloseNameChain.Literals c) :
    ∃ n d, n≤60 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.same name (WireSpec.ascii "connection") then 0x80002574#32 else 0x80002474#32) ∧
      MainCloseNameChain.Frame c d ∧ d.sameCsr c := by
  rw [MainCloseConnectionSpec.correspondence name length]
  apply MainCloseNameChain.contract B c ram base (fun i => name[i]?.getD 0#8) hp h15 literals
  · intro k hk
    exact span.memory ⟨k,by omega⟩
  · intro k hk
    have bound : k<name.length := by omega
    rw [List.getElem?_eq_getElem bound]
    exact span.bytes ⟨k,bound⟩

/-- Header offsets derive this slice; the bytes are not postulated separately. -/
theorem header (B : Board) (c : Core) (ram : Word → BitVec 8) (rawPtr : Word) (raw : List (BitVec 8))
    (e : HeaderSpec.Entry) (span : Bytes.Span B ram rawPtr raw) (bounds : HeaderSpec.Bounds raw.length e)
    (length : e.nameEnd-e.nameStart=10) (hp : c.pc=0x8000249a#32)
    (h15 : c.get 15=rawPtr+BitVec.ofNat 32 e.nameStart) (literals : MainCloseNameChain.Literals c) :
    ∃ n d, n≤60 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.same (HeaderSpec.name raw e) (WireSpec.ascii "connection") then 0x80002574#32 else 0x80002474#32) ∧
      MainCloseNameChain.Frame c d ∧ d.sameCsr c :=
  contract B c ram _ _ (HeaderInput.name_span span bounds) ((HeaderInput.name_length bounds).trans length) hp h15 literals
end E5R.Thermostat.MainCloseName
