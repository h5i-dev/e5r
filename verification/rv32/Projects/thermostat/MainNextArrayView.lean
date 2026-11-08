import Projects.thermostat.MainNextCopy264
namespace E5R.Thermostat.MainNextArrayView
open E5R E5R.Thermostat HttpRequestSpec

/-- The264-byte portion of the real Next object: sixteen header descriptors,
    their count and the consumed-head length. Other Next fields are separate. -/
structure At (ram : Word → BitVec 8) (dst : Word) (head : Head) : Prop where
  bound : head.headers.length≤16
  count : ramRead ram (dst+256#32) .w=BitVec.ofNat 32 head.headers.length
  length : ramRead ram (dst+260#32) .w=BitVec.ofNat 32 head.len
  headers : ∀ i : Fin head.headers.length,
    ramRead ram (dst+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 head.headers[i].ns ∧
    ramRead ram ((dst+4#32)+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 head.headers[i].ne ∧
    ramRead ram ((dst+8#32)+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 head.headers[i].vs ∧
    ramRead ram ((dst+12#32)+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 head.headers[i].ve

theorem copied {before after src dst} (head : Head)
    (copy : MainCopyView.At before after (src+32#32) dst 264)
    (view : HeadCompletedView.At before src head) : At after dst head := by
  have offset (p : Word) (a b : Nat) : (p+BitVec.ofNat 32 a)+BitVec.ofNat 32 b=p+BitVec.ofNat 32 (a+b) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  refine ⟨view.count_bound,?_,?_,?_⟩
  · have count := (MainCopyView.word copy 256 (by decide)).trans (by simpa only [offset] using view.count)
    exact count
  · exact (MainCopyView.word copy 260 (by decide)).trans (by simpa only [offset] using view.length)
  · intro i
    have small : i.val<16 := Nat.lt_of_lt_of_le i.isLt view.count_bound
    refine ⟨(MainCopyView.word copy (16*i.val) (by omega)).trans (view.headers i).1,?_,?_,?_⟩
    · have h := MainCopyView.word copy (4+16*i.val) (by omega)
      simpa only [←offset] using h.trans (by simpa only [offset,←Nat.add_assoc,Nat.reduceAdd] using (view.headers i).2.1)
    · have h := MainCopyView.word copy (8+16*i.val) (by omega)
      simpa only [←offset] using h.trans (by simpa only [offset,←Nat.add_assoc,Nat.reduceAdd] using (view.headers i).2.2.1)
    · have h := MainCopyView.word copy (12+16*i.val) (by omega)
      simpa only [←offset] using h.trans (by simpa only [offset,←Nat.add_assoc,Nat.reduceAdd] using (view.headers i).2.2.2)

theorem fixed (ram : Word → BitVec 8) (sp : Word) (head : Head) (stack : Memory.Block B sp 5232)
    (view : HeadCompletedView.At ram (sp+3320#32) head) :
    At (MainNextCopy264.memory ram sp 3352) (sp+4904#32) head := by
  apply copied head (view := view)
  simpa only [MainNextCopy264.source,BitVec.add_assoc,show 3320#32+32#32=3352#32 by decide +kernel] using MainNextCopy264.bytes ram sp 3352 stack

theorem empty (ram : Word → BitVec 8) (sp : Word) (head : Head) (stack : Memory.Block B sp 5232)
    (view : HeadCompletedView.At ram (sp+4520#32) head) :
    At (MainNextCopy264.memory ram sp 4552) (sp+4904#32) head := by
  apply copied head (view := view)
  simpa only [MainNextCopy264.source,BitVec.add_assoc,show 4520#32+32#32=4552#32 by decide +kernel] using MainNextCopy264.bytes ram sp 4552 stack
end E5R.Thermostat.MainNextArrayView
