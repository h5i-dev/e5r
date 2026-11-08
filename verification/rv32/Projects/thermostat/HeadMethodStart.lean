import Projects.thermostat.HeadMethodClass
import Projects.thermostat.HeadMethodSetup
import Projects.thermostat.HeadMethodEntry
import Projects.thermostat.HeadMethodMath
namespace E5R.Thermostat.HeadMethodStart
open E5R E5R.Thermostat

/-- The actual nonempty-line entry establishes every classifier constant and
    the zero method index; they are not assumed to appear at the scan loop. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (j : Nat)
    (hp : c.pc=0x80002cba#32) (h9 : c.get 9=BitVec.ofNat 32 j) (hj : 0<j) (hn : j≤2048) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002cfa#32 ∧
      d.get 17=0#32 ∧ d.get 15=400#32 ∧ HeadMethodClass.Constants d ∧
      (∀ r : Reg, r≠15 → r≠17 → r≠5 → r≠6 → r≠7 → r≠8 → r≠18 → r≠29 → r≠30 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,entry,pc,status,frame,csr⟩ := HeadMethodEntry.contract B c ram (BitVec.ofNat 32 j) false hp h9 (HeadMethodMath.nonzero j hj hn)
  obtain ⟨d,setup,pc2,index,mask,low,mid,nibble,digit,letter,upper,bracket,frame2,csr2⟩ := HeadMethodSetup.contract B a ram pc
  refine ⟨d,entry.trans setup,pc2,index,?_,⟨mask,low,mid,upper,bracket,nibble,digit,letter⟩,?_,csr2.trans csr⟩
  · exact (frame2 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans status
  · intro r h15 h17 h5 h6 h7 h8 h18 h29 h30 h31
    exact (frame2 r h17 h5 h6 h7 h29 h30 h31 h8 h18).trans (frame r h15)
end E5R.Thermostat.HeadMethodStart
