import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.ViewFrame
open E5R

theorem half {before after p n} (h : Region before after p n) (k : Nat) (hk : k+2 ≤ n) :
    ramRead after (p+BitVec.ofNat 32 k) .h = ramRead before (p+BitVec.ofNat 32 k) .h := by
  have h0 := h ⟨k,by omega⟩
  have h1 := h ⟨k+1,by omega⟩
  have he : (p+BitVec.ofNat 32 k)+(1 : Word) = p+BitVec.ofNat 32 (k+1) := by
    rw [BitVec.add_assoc,BitVec.ofNat_add];rfl
  simp only [ramRead,he,h0,h1]
end E5R.Thermostat.ViewFrame
