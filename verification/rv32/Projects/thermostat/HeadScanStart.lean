import Projects.thermostat.HeadScanSetup
import Projects.thermostat.HeadNonemptyBranch
namespace E5R.Thermostat.HeadScanStart
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat)
    (hp : c.pc=0x80002c88#32) (h14 : c.get 14=BitVec.ofNat 32 n) (hn : n≤1024) :
    ∃ steps d, 1≤steps ∧ steps≤4 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if n=0 then 0x80002ce6#32 else 0x80002c90#32) ∧
      (n≠0 → d.get 9=0#32 ∧ d.get 15=10#32 ∧ d.get 17=13#32) ∧
      (∀ r : Reg, r≠9 → r≠15 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  by_cases empty : n=0
  · subst n
    obtain ⟨d,branch,pc,frame,csr⟩ := HeadNonemptyBranch.contract B c ram 0#32 true hp h14 (by decide +kernel)
    exact ⟨1,d,by decide,by decide,branch,pc,by simp,fun r _ _ _ => frame r,csr⟩
  · have ht : taken .eq (BitVec.ofNat 32 n) (0 : Word)=false := by
      have words : BitVec.ofNat 32 n≠(0 : Word) := by
        intro he
        have eq := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at eq
        change n=0 at eq
        exact empty eq
      simpa [taken] using words
    obtain ⟨a,branch,pc,frame,csr⟩ := HeadNonemptyBranch.contract B c ram (BitVec.ofNat 32 n) false hp h14 ht
    obtain ⟨d,setup,pc2,zero,ten,thirteen,frame2,csr2⟩ := HeadScanSetup.contract B a ram pc
    refine ⟨4,d,by decide,by decide,branch.trans setup,?_,fun _ => ⟨zero,ten,thirteen⟩,?_,csr2.trans csr⟩
    · simpa only [empty,ite_false] using pc2
    · intro r h9 h15 h17
      exact (frame2 r h9 h15 h17).trans (frame r)
end E5R.Thermostat.HeadScanStart
