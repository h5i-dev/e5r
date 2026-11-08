import Projects.thermostat.Bytes
namespace E5R.Thermostat.Bytes
open E5R E5R.Thermostat

theorem append_of_block {B ram dst cap xs ys} (hm : Memory.Block B dst cap) (hc : cap < 2^32)
    (hf : xs.length+ys.length ≤ cap) (hx : Span B ram dst xs)
    (hy : Span B ram (dst+BitVec.ofNat 32 xs.length) ys) : Span B ram dst (xs++ys) := by
  apply of_block
  · exact ⟨hm.1,by have := hm.2.1;simp only [List.length_append];omega,by have := hm.2.2;simp only [List.length_append];omega⟩
  · simp only [List.length_append];omega
  · intro i
    change ram (dst+BitVec.ofNat 32 i.val) = (xs++ys)[i.val]
    by_cases hi : i.val < xs.length
    · rw [List.getElem_append_left hi]
      exact hx.bytes ⟨i.val,hi⟩
    · have hj : i.val-xs.length < ys.length := by have := i.isLt;simp only [List.length_append] at this;omega
      rw [List.getElem_append_right (by omega)]
      have hh := hy.bytes ⟨i.val-xs.length,hj⟩
      change ram ((dst+BitVec.ofNat 32 xs.length)+BitVec.ofNat 32 (i.val-xs.length)) = ys[i.val-xs.length] at hh
      have he : (dst+BitVec.ofNat 32 xs.length)+BitVec.ofNat 32 (i.val-xs.length) = dst+BitVec.ofNat 32 i.val := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
        congr 2
        omega
      rw [he] at hh
      exact hh
end E5R.Thermostat.Bytes
