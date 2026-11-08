import Projects.thermostat.MainNextArrayView
namespace E5R.Thermostat.MainNextArrayFrame
open E5R E5R.Thermostat HttpRequestSpec

theorem preserve {before after dst head} (view : MainNextArrayView.At before dst head)
    (frame : ViewFrame.Region before after dst 264) : MainNextArrayView.At after dst head := by
  refine ⟨view.bound,(ViewFrame.word frame 256 (by decide)).trans view.count,(ViewFrame.word frame 260 (by decide)).trans view.length,?_⟩
  intro i
  have bound : i.val<16 := Nat.lt_of_lt_of_le i.isLt view.bound
  have word (off : Nat) (small : off+4≤264) := ViewFrame.word frame off small
  have offset (p : Word) (off : Nat) : (p+BitVec.ofNat 32 off)+BitVec.ofNat 32 (16*i.val)=p+BitVec.ofNat 32 (off+16*i.val) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  refine ⟨(word (16*i.val) (by omega)).trans (view.headers i).1,?_,?_,?_⟩
  · simpa only [offset] using (word (4+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.1)
  · simpa only [offset] using (word (8+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.2.1)
  · simpa only [offset] using (word (12+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.2.2)
end E5R.Thermostat.MainNextArrayFrame
