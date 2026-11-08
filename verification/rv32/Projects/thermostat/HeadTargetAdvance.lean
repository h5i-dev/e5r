import Projects.thermostat.HeadTargetIncrement
import Projects.thermostat.HeadTargetContinue
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadTargetAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m i j : Nat)
    (hp : c.pc=0x80002df4#32) (h31 : c.get 31=BitVec.ofNat 32 (j-i)) (h30 : c.get 30=BitVec.ofNat 32 (i-m-1))
    (hm : m<i) (hi : i<j) (hj : j≤2048) :
    ∃ n d, 3≤n ∧ n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if i+1<j then 0x80002dd8#32 else 0x80002efc#32) ∧
      d.get 31=BitVec.ofNat 32 (j-(i+1)) ∧ d.get 30=BitVec.ofNat 32 (i+1-m-1) ∧
      (∀ r : Reg, r≠31 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,inc,pc,rem,off,frame,csr⟩ := HeadTargetIncrement.contract B c ram
    (BitVec.ofNat 32 (j-i)) (BitVec.ofNat 32 (i-m-1)) h31 h30 hp
  have rem' : a.get 31=BitVec.ofNat 32 (j-(i+1)) := rem.trans (HeadTargetMath.remaining_next i j hi)
  have off' : a.get 30=BitVec.ofNat 32 (i+1-m-1) := off.trans (HeadTargetMath.offset_next m i hm)
  obtain ⟨b,branch,pc2,frame2,csr2⟩ := HeadTargetContinue.contract B a ram (BitVec.ofNat 32 (j-(i+1))) (decide (i+1<j)) pc rem' (HeadTargetMath.again i j hi hj)
  by_cases more : i+1<j
  · refine ⟨3,b,by decide,by decide,inc.trans branch,?_,(frame2 31).trans rem',(frame2 30).trans off',?_,csr2.trans csr⟩
    · simpa only [more,decide_true,ite_true] using pc2
    · intro r h31 h30
      exact (frame2 r).trans (frame r h31 h30)
  · have atExit : b.pc=0x80002dfc#32 := by simpa only [more,decide_false,Bool.false_eq_true,ite_false] using pc2
    obtain ⟨d,exit,pc3,frame3,csr3⟩ := HeadTargetContinue.exhausted B b ram atExit
    refine ⟨4,d,by decide,by decide,(inc.trans branch).trans exit,?_,
      (frame3 31).trans ((frame2 31).trans rem'),(frame3 30).trans ((frame2 30).trans off'),?_,csr3.trans (csr2.trans csr)⟩
    · simpa only [more,ite_false] using pc3
    · intro r h31 h30
      exact (frame3 r).trans ((frame2 r).trans (frame r h31 h30))
end E5R.Thermostat.HeadTargetAdvance
