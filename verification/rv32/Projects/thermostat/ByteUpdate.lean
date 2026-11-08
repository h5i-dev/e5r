import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ByteUpdate
open E5R E5R.Thermostat

/-- Replace one checked RAM byte and the corresponding byte of its slice. -/
theorem span {B ram p xs} (h : Bytes.Span B ram p xs) (k : Nat) (b : BitVec 8) (hk : k < xs.length) :
    Bytes.Span B (ramPut ram (p+BitVec.ofNat 32 k) b) p (xs.set k b) := by
  refine ⟨by simpa using h.length,by simpa using h.nowrap,?_,?_⟩
  · intro i
    exact h.memory ⟨i.val,by simpa using i.isLt⟩
  · intro i
    have hi : i.val < xs.length := by simpa using i.isLt
    change ramPut ram (p+BitVec.ofNat 32 k) b (p+BitVec.ofNat 32 i.val) = (xs.set k b)[i.val]
    rw [List.getElem_set]
    by_cases he : k = i.val
    · simp only [he,ite_true,ramPut_eq]
    · rw [ite_eq_right he,ramPut_ne _ (Bytes.offset_ne p i.val k (by have := h.length;omega) (by have := h.length;omega) (Ne.symm he))]
      exact h.bytes ⟨i.val,hi⟩
end E5R.Thermostat.ByteUpdate
