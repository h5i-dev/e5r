import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Bytes
open E5R E5R.Thermostat

theorem left_part {B ram p xs ys} (hs : Span B ram p (xs++ys)) : Span B ram p xs := by
  have hl : xs.length+ys.length < 2^32 := by simpa using hs.length
  have hn : p.toNat+(xs.length+ys.length) ≤ 2^32 := by simpa using hs.nowrap
  refine ⟨by omega,by omega,?_,?_⟩
  · intro i
    exact hs.memory ⟨i.val,by simp only [List.length_append];omega⟩
  · intro i
    have hi := i.isLt
    have hb := hs.bytes ⟨i.val,by simp only [List.length_append];omega⟩
    change ram (p+BitVec.ofNat 32 i.val) = (xs++ys)[i.val] at hb
    rw [List.getElem_append_left hi] at hb
    exact hb

theorem suffix {B ram p xs ys} (hs : Span B ram p (xs++ys)) :
    Span B ram (p+BitVec.ofNat 32 xs.length) ys := by
  have hl : xs.length+ys.length < 2^32 := by simpa using hs.length
  have hn : p.toNat+(xs.length+ys.length) ≤ 2^32 := by simpa using hs.nowrap
  refine ⟨by omega,?_,?_,?_⟩
  · by_cases hz : ys.length = 0
    · have hp := (p+BitVec.ofNat 32 xs.length).isLt;omega
    · rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show xs.length < 2^32 by omega),Nat.mod_eq_of_lt (show p.toNat+xs.length < 2^32 by omega)]
      omega
  · intro i
    have hi := i.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hs.memory ⟨xs.length+i.val,by simp only [List.length_append];omega⟩
  · intro i
    have hi := i.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    have hb := hs.bytes ⟨xs.length+i.val,by simp only [List.length_append];omega⟩
    change ram (p+BitVec.ofNat 32 (xs.length+i.val)) = (xs++ys)[xs.length+i.val] at hb
    rw [List.getElem_append_right (by omega)] at hb
    simpa using hb

theorem same {B ram ram' p xs} (hs : Span B ram p xs)
    (hf : ∀ i : Fin xs.length, ram' (p+BitVec.ofNat 32 i.val) = ram (p+BitVec.ofNat 32 i.val)) :
    Span B ram' p xs := ⟨hs.length,hs.nowrap,hs.memory,fun i => (hf i).trans (hs.bytes i)⟩
end E5R.Thermostat.Bytes
