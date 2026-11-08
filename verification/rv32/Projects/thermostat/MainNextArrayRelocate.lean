import Projects.thermostat.MainNextArrayView
namespace E5R.Thermostat.MainNextArrayRelocate
open E5R E5R.Thermostat HttpRequestSpec

/-- Byte-for-byte relocation of the actual264-byte Next/Request header
    array portion, including its count and consumed-head length. -/
theorem contract {before after src dst head} (view : MainNextArrayView.At before src head)
    (copy : MainCopyView.At before after src dst 264) : MainNextArrayView.At after dst head := by
  refine ⟨view.bound,(MainCopyView.word copy 256 (by decide)).trans view.count,
    (MainCopyView.word copy 260 (by decide)).trans view.length,?_⟩
  intro i
  have bound : i.val<16 := Nat.lt_of_lt_of_le i.isLt view.bound
  have word (off : Nat) (small : off+4≤264) := MainCopyView.word copy off small
  have offset (p : Word) (off : Nat) : (p+BitVec.ofNat 32 off)+BitVec.ofNat 32 (16*i.val)=p+BitVec.ofNat 32 (off+16*i.val) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  refine ⟨(word (16*i.val) (by omega)).trans (view.headers i).1,?_,?_,?_⟩
  · simpa only [offset] using (word (4+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.1)
  · simpa only [offset] using (word (8+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.2.1)
  · simpa only [offset] using (word (12+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.2.2)
end E5R.Thermostat.MainNextArrayRelocate
