import Projects.thermostat.HeadOwsForwardUpdate
import Projects.thermostat.HeadOwsForwardBranch
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadOwsForwardAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (pos finish : Nat)
    (hp : c.pc=0x8000309c#32) (h15 : c.get 15=BitVec.ofNat 32 pos) (h25 : c.get 25=BitVec.ofNat 32 (finish-pos))
    (hi : pos<finish) (hn : finish≤2048) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if pos+1=finish then 0x800030f2#32 else 0x800030a4#32) ∧
      d.get 15=BitVec.ofNat 32 (pos+1) ∧ d.get 25=BitVec.ofNat 32 (finish-(pos+1)) ∧
      (∀ r : Reg, r≠25 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,update,pc,rem,index,frame,csr⟩ := HeadOwsForwardUpdate.contract B c ram (BitVec.ofNat 32 pos) (BitVec.ofNat 32 (finish-pos)) h15 h25 hp
  have remaining : a.get 25=BitVec.ofNat 32 (finish-(pos+1)) := rem.trans (HeadTargetMath.remaining_next pos finish hi)
  have test : taken .eq (BitVec.ofNat 32 (finish-(pos+1))) (0 : Word)=decide (pos+1=finish) := by
    by_cases last : pos+1=finish
    · simp [last,taken]
    · simpa only [last,decide_false] using HeadMethodMath.nonzero (finish-(pos+1)) (by omega) (by omega)
  obtain ⟨d,branch,pc2,frame2,csr2⟩ := HeadOwsForwardBranch.contract B a ram (BitVec.ofNat 32 (finish-(pos+1))) (decide (pos+1=finish)) pc remaining test
  refine ⟨d,update.trans branch,?_,(frame2 15).trans (index.trans (HeadScanMath.next_word pos)),(frame2 25).trans remaining,
    fun r h25 h15 => (frame2 r).trans (frame r h25 h15),csr2.trans csr⟩
  simpa only [decide_eq_true_eq] using pc2
end E5R.Thermostat.HeadOwsForwardAdvance
