import Projects.thermostat.HeadFieldsEmptyBranch
import Projects.thermostat.HeadFieldsNonempty
import Projects.thermostat.HeadMethodMath
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadFieldsEmpty
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (i t : Nat)
    (hp : c.pc=0x80002fb4#32) (h21 : c.get 21=BitVec.ofNat 32 t)
    (h24 : c.get 24=BitVec.ofNat 32 i) (h26 : c.get 26=BitVec.ofNat 32 (i+t)) (hn : i+t≤2048) :
    ∃ n d, 1≤n ∧ n≤2 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if t=0 then 0x80003456#32 else 0x80002fbc#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  have test : taken .eq (BitVec.ofNat 32 t) (0 : Word)=decide (t=0) := by
    by_cases empty : t=0
    · subst t;decide +kernel
    · simpa only [empty,decide_false] using HeadMethodMath.nonzero t (by omega) (by omega)
  obtain ⟨a,emptyBranch,pc,frame,csr⟩ := HeadFieldsEmptyBranch.contract B c ram (BitVec.ofNat 32 t) (decide (t=0)) hp h21 test
  by_cases empty : t=0
  · exact ⟨1,a,by decide,by decide,emptyBranch,by simpa only [empty,decide_true,ite_true] using pc,frame,csr⟩
  · have atCheck : a.pc=0x80002fb8#32 := by simpa only [empty,decide_false,Bool.false_eq_true,ite_false] using pc
    have test2 : taken .geu (BitVec.ofNat 32 i) (BitVec.ofNat 32 (i+t))=false := by
      rw [HeadTargetMath.geu i (i+t) (by omega) hn]
      simp only [show ¬i+t≤i by omega,decide_false]
    obtain ⟨d,check,pc2,frame2,csr2⟩ := HeadFieldsNonempty.contract B a ram (BitVec.ofNat 32 i) (BitVec.ofNat 32 (i+t))
      atCheck ((frame 24).trans h24) ((frame 26).trans h26) test2
    exact ⟨2,d,by decide,by decide,emptyBranch.trans check,by simpa only [empty,ite_false] using pc2,
      fun r => (frame2 r).trans (frame r),csr2.trans csr⟩
end E5R.Thermostat.HeadFieldsEmpty
