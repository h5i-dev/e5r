import Projects.thermostat.HeadTargetGuard
import Projects.thermostat.HeadTargetSetup
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadTargetStart
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m j : Nat)
    (hp : c.pc=0x80002dc0#32) (h17 : c.get 17=BitVec.ofNat 32 m) (h9 : c.get 9=BitVec.ofNat 32 j)
    (hi : m+1<j) (hj : j≤2048) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002dd8#32 ∧
      d.get 29=BitVec.ofNat 32 (m+1) ∧ d.get 30=0#32 ∧ d.get 31=BitVec.ofNat 32 (j-(m+1)) ∧
      d.get 8=BitVec.ofNat 32 (m+1) ∧ d.get 19=94#32 ∧
      (∀ r : Reg, r≠29 → r≠30 → r≠31 → r≠8 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  have test : taken .geu (BitVec.ofNat 32 m+1#32) (BitVec.ofNat 32 j)=false := by
    rw [HeadScanMath.next_word,HeadTargetMath.geu (m+1) j (by omega) hj]
    simp only [show ¬j≤m+1 by omega,decide_false]
  obtain ⟨a,guard,pc,start,frame,csr⟩ := HeadTargetGuard.contract B c ram (BitVec.ofNat 32 m) (BitVec.ofNat 32 j) false hp h17 h9 test
  obtain ⟨d,setup,endPC,zero,rem,next,constant,frame2,csr2⟩ := HeadTargetSetup.contract B a ram (BitVec.ofNat 32 m) (BitVec.ofNat 32 j)
    ((frame 17 (by decide)).trans h17) ((frame 9 (by decide)).trans h9) (by simpa only [Bool.false_eq_true,ite_false] using pc)
  refine ⟨d,guard.trans setup,endPC,?_,zero,?_,?_,constant,?_,csr2.trans csr⟩
  · exact (frame2 29 (by decide) (by decide) (by decide) (by decide)).trans (start.trans (HeadScanMath.next_word m))
  · have eq : j-m-1=j-(m+1) := by omega
    exact rem.trans ((HeadTargetMath.remaining m j (by omega) hj).trans (congrArg (BitVec.ofNat 32) eq))
  · exact next.trans (HeadScanMath.next_word m)
  · intro r h29 h30 h31 h8 h19
    exact (frame2 r h30 h31 h8 h19).trans (frame r h29)
end E5R.Thermostat.HeadTargetStart
