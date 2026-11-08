import Projects.thermostat.HeadMethodSpaceCalc
import Projects.thermostat.HeadMethodSpaceBranch
import Projects.thermostat.HeadMethodSpaceFlow
namespace E5R.Thermostat.HeadMethodSpace
open E5R E5R.Thermostat

/-- The real guard rejects an empty method or any delimiter other than SP. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m j : Nat) (b : BitVec 8)
    (hp : c.pc=0x80002da2#32) (h17 : c.get 17=BitVec.ofNat 32 m) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h19 : c.get 19=BitVec.ofNat 32 b.toNat) (hm : m<j) (hj : j≤2048) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if m=0 ∨ b.toNat≠32 then 0x80002efc#32 else 0x80002dc0#32) ∧
      (∀ r : Reg, r≠6 → r≠7 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,arith,pc,flag,byteFlag,byteDiff,frame,csr⟩ := HeadMethodSpaceCalc.contract B c ram (BitVec.ofNat 32 m)
    (BitVec.ofNat 32 j) (BitVec.ofNat 32 b.toNat) h17 h9 h19 hp
  have value : a.get 6=HeadMethodSpaceFlow.flags (BitVec.ofNat 32 m) (BitVec.ofNat 32 j) b := flag
  obtain ⟨d,branch,pc2,frame2,csr2⟩ := HeadMethodSpaceBranch.contract B a ram
    (HeadMethodSpaceFlow.flags (BitVec.ofNat 32 m) (BitVec.ofNat 32 j) b) (decide (m=0 ∨ b.toNat≠32)) pc value
    (HeadMethodSpaceFlow.bad_test m j b hm hj)
  refine ⟨d,arith.trans branch,?_,fun r h6 h7 h19 => (frame2 r).trans (frame r h6 h7 h19),csr2.trans csr⟩
  simpa only [decide_eq_true_eq] using pc2
end E5R.Thermostat.HeadMethodSpace
