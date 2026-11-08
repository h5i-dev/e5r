import Projects.thermostat.HeaderInput
namespace E5R.Thermostat.HeaderResult
open E5R E5R.Thermostat

/-- Empty Some values keep a nonzero slice pointer; None constrains only its
    niche pointer, leaving the inactive length register unconstrained. -/
def At (B : Board) (ram : Word → BitVec 8) (p : Word) (raw : List (BitVec 8)) (c : Core) : Option HeaderSpec.Entry → Prop
  | none => c.get 10 = 0#32
  | some e => c.get 10 = p+BitVec.ofNat 32 e.valueStart ∧
      c.get 11 = BitVec.ofNat 32 (HeaderSpec.value raw e).length ∧
      Bytes.Span B ram (c.get 10) (HeaderSpec.value raw e) ∧ c.get 10 ≠ 0#32

theorem pointer_nonzero (p : Word) (k len : Nat) (hpos : 0 < p.toNat)
    (hbound : p.toNat+len < 2^32) (hk : k ≤ len) : p+BitVec.ofNat 32 k ≠ 0#32 := by
  intro he
  have hh := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at hh
  change (p.toNat+k%4294967296)%4294967296 = 0 at hh
  omega

def Frame (c d : Core) : Prop := ∀ r : Reg, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 10 → r ≠ 11 → r ≠ 14 → r ≠ 16 → r ≠ 28 → r ≠ 29 → d.get r = c.get r

theorem Frame.trans {a b c : Core} (hab : Frame a b) (hbc : Frame b c) : Frame a c :=
  fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => (hbc r h1 h2 h3 h4 h5 h6 h7 h8 h9).trans (hab r h1 h2 h3 h4 h5 h6 h7 h8 h9)

def BytesAt (B : Board) (ram : Word → BitVec 8) (c : Core) : Option (List (BitVec 8)) → Prop
  | none => c.get 10 = 0#32
  | some bytes => c.get 10 ≠ 0#32 ∧ c.get 11 = BitVec.ofNat 32 bytes.length ∧ Bytes.Span B ram (c.get 10) bytes

theorem as_lookup {B ram p raw query entries c}
    (h : At B ram p raw c (HeaderSpec.find raw query entries)) :
    BytesAt B ram c (HeaderSpec.lookup raw query entries) := by
  rw [HeaderSpec.lookup_find]
  cases hf : HeaderSpec.find raw query entries with
  | none => rw [hf] at h;exact h
  | some e =>
    rw [hf] at h
    exact ⟨h.2.2.2,h.2.1,h.2.2.1⟩
end E5R.Thermostat.HeaderResult
