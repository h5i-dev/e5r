import Projects.thermostat.HeadValueSetupLoad
import Projects.thermostat.HeadValueEmptyBranch
import Projects.thermostat.HeadValueSetupTail
import Projects.thermostat.HeadNameState
import Projects.thermostat.HeadValueState
namespace E5R.Thermostat.HeadValueInit
open E5R E5R.Thermostat

/-- Actual value-start load and empty/nonempty branch. The nonempty slice
    state is derived from the preceding name scan's real register values. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start k finish length : Nat)
    (hp : c.pc=0x80003068#32) (state : HeadNameState.At c sp buf start k finish length)
    (h26 : c.get 26=BitVec.ofNat 32 finish) (hword : ramRead ram (sp+4#32) .w=BitVec.ofNat 32 k)
    (hi : k<finish) (hn : finish≤length) (hlen : length≤2048) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    ∃ n d, 3≤n ∧ n≤5 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if k+1=finish then 0x800030c0#32 else 0x8000307c#32) ∧ d.get 15=BitVec.ofNat 32 (k+1) ∧
      (k+1<finish → HeadValueState.At d buf (k+1) finish length) ∧
      (∀ r : Reg, r≠15 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,load,pc,index,frame,csr⟩ := HeadValueSetupLoad.contract B c ram sp (BitVec.ofNat 32 k) state.stack hword stack ha hp
  have next : a.get 15=BitVec.ofNat 32 (k+1) := index.trans (HeadScanMath.next_word k)
  have test : taken .geu (BitVec.ofNat 32 (k+1)) (BitVec.ofNat 32 finish)=decide (k+1=finish) := by
    simpa only [show (finish≤k+1) ↔ (k+1=finish) by omega] using HeadTargetMath.geu (k+1) finish (by omega) (by omega)
  obtain ⟨b,branch,pc2,frame2,csr2⟩ := HeadValueEmptyBranch.contract B a ram (BitVec.ofNat 32 (k+1)) (BitVec.ofNat 32 finish) (decide (k+1=finish)) pc next
    ((frame 26 (by decide)).trans h26) test
  have source (r : Reg) (h15 : r≠15) : b.get r=c.get r := (frame2 r).trans (frame r h15)
  by_cases last : k+1=finish
  · refine ⟨3,b,by decide,by decide,load.trans branch,?_,(frame2 15).trans next,?_,fun r h15 _ => source r h15,csr2.trans csr⟩
    · simpa only [last,decide_true,ite_true] using pc2
    · intro more;omega
  · have atTail : b.pc=0x80003070#32 := by simpa only [last,decide_false,Bool.false_eq_true,ite_false] using pc2
    obtain ⟨d,tail,pc3,remaining,frame3,csr3⟩ := HeadValueSetupTail.contract B b ram (BitVec.ofNat 32 (finish-k-1))
      ((source 25 (by decide)).trans state.inverse) atTail
    refine ⟨5,d,by decide,by decide,(load.trans branch).trans tail,?_,(frame3 15 (by decide)).trans ((frame2 15).trans next),?_,
      fun r h15 h13 => (frame3 r h13).trans (source r h15),csr3.trans (csr2.trans csr)⟩
    · simpa only [last,ite_false] using pc3
    · intro _
      exact ⟨(frame3 10 (by decide)).trans ((source 10 (by decide)).trans state.ptr),by simpa only [Nat.sub_sub] using remaining,
        by simpa only [Nat.sub_sub] using (frame3 31 (by decide)).trans ((source 31 (by decide)).trans state.remaining)⟩
end E5R.Thermostat.HeadValueInit
