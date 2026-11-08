import Projects.thermostat.BodyMemory
import Projects.thermostat.ResponseWordBytes
namespace E5R.Thermostat.BodyResponseView
open E5R E5R.Thermostat

theorem word {ram out ct len used status} (h : BodyMemory.At ram out ct len used status)
    (k : Fin 3) : ramRead ram (out+BitVec.ofNat 32 (4*k.val)) .w=(if k.val=0 then ct else if k.val=1 then len else used) := by
  apply ResponseWordBytes.word
  intro i
  have hi := i.isLt
  have hk := k.isLt
  have v := h ⟨4*k.val+i.val,by omega⟩
  have he : (out+BitVec.ofNat 32 (4*k.val))+BitVec.ofNat 32 i.val=out+BitVec.ofNat 32 (4*k.val+i.val) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [he]
  have ik : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  have kk : k.val=0 ∨ k.val=1 ∨ k.val=2 := by omega
  rcases kk with e|e|e <;> rcases ik with f|f|f|f
  all_goals simpa [BodyMemory.responseByte,e,f] using v

theorem half {ram out ct len used status} (h : BodyMemory.At ram out ct len used status) (hs : status.toNat<65536) :
    extend .h false (ramRead ram (out+12#32) .h)=status := by
  apply ResponseWordBytes.half ram (out+12#32) status hs
  intro i
  have hi := i.isLt
  have v := h ⟨12+i.val,by omega⟩
  have he : (out+12#32)+BitVec.ofNat 32 i.val=out+BitVec.ofNat 32 (12+i.val) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [he]
  have ik : i.val=0 ∨ i.val=1 := by omega
  rcases ik with e|e
  all_goals simpa [BodyMemory.responseByte,e] using v

theorem extra {ram out ct len used status} (h : BodyMemory.At ram out ct len used status) : ram (out+14#32)=0#8 := by
  exact h ⟨14,by decide⟩
end E5R.Thermostat.BodyResponseView
