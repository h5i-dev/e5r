import Projects.thermostat.HeadValueAdvanceUpdate
import Projects.thermostat.HeadValueAdvanceBranch
import Projects.thermostat.HeadValueState
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadValueAdvance
open E5R E5R.Thermostat

/-- The real three cursor/remainder updates and loop-exit test. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (pos finish length : Nat)
    (hp : c.pc=0x80003074#32) (state : HeadValueState.At c buf pos finish length)
    (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if pos+1=finish then 0x800030a4#32 else 0x8000307c#32) ∧
      HeadValueState.At d buf (pos+1) finish length ∧
      (∀ r : Reg, r≠13 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,update,pc,remaining,ptr,rawRemaining,frame,csr⟩ := HeadValueAdvanceUpdate.contract B c ram (BitVec.ofNat 32 (finish-pos))
    (buf+BitVec.ofNat 32 pos) (BitVec.ofNat 32 (length-pos)) state.remaining state.ptr state.rawRemaining hp
  have rem : a.get 13=BitVec.ofNat 32 (finish-(pos+1)) := remaining.trans (HeadTargetMath.remaining_next pos finish hi)
  have zero : taken .eq (BitVec.ofNat 32 (finish-(pos+1))) (0 : Word)=decide (pos+1=finish) := by
    by_cases last : pos+1=finish
    · simp [last,taken]
    · simpa only [last,decide_false] using HeadMethodMath.nonzero (finish-(pos+1)) (by omega) (by omega)
  obtain ⟨d,branch,pc2,frame2,csr2⟩ := HeadValueAdvanceBranch.contract B a ram (BitVec.ofNat 32 (finish-(pos+1))) (decide (pos+1=finish)) pc rem zero
  refine ⟨d,update.trans branch,?_,?_,fun r h13 h10 h31 => (frame2 r).trans (frame r h13 h10 h31),csr2.trans csr⟩
  · simpa only [decide_eq_true_eq] using pc2
  · exact ⟨(frame2 10).trans (ptr.trans (by rw [BitVec.add_assoc,←BitVec.ofNat_add])),
      (frame2 13).trans rem,(frame2 31).trans (rawRemaining.trans (HeadTargetMath.remaining_next pos length (by omega)))⟩
end E5R.Thermostat.HeadValueAdvance
