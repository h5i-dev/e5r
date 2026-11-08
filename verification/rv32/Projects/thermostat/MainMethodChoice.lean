import Projects.thermostat.QuietBranch
import Projects.thermostat.MainMethodByteMath
set_option autoImplicit false
namespace E5R.Thermostat.MainMethodChoice
open E5R

theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc off : Word) (literal : Nat) (byte : BitVec 8)
    (hp : c.pc=pc) (h16 : c.get 16=BitVec.ofNat 32 byte.toNat) (bound : literal≤255)
    (aligned : pc.getLsbD 0=false) (aligned1 : (pc+4#32).getLsbD 0=false)
    (targetAligned : (pc+4#32+off).getLsbD 0=false)
    (lit : fetchDecode img pc=some (.opimm .add 17 0 (BitVec.ofNat 32 literal),4#32))
    (branch : fetchDecode img (pc+4#32)=some (.branch .ne 16 17 off,4#32)) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠literal then pc+4#32+off else pc+8#32) ∧
      d.get 17=BitVec.ofNat 32 literal ∧ (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 17 (BitVec.ofNat 32 literal) (pc+4#32)
  have t : E5R.Thermostat.Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine E5R.Thermostat.Quiet.step_of (by rw [hp];exact aligned) (by rw [hp];exact lit) fun o => ?_
    change E5R.Thermostat.Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp]
    change Observed.interp B img o (Eff.done (c.wr 17 (0#32+BitVec.ofNat 32 literal) (pc+4#32))) ram 0 [] [] = _
    rw [BitVec.zero_add];rfl
  have a16 : a.get 16=BitVec.ofNat 32 byte.toNat := by simp [a,Core.wr_get_ne,h16]
  have a17 : a.get 17=BitVec.ofNat 32 literal := by simp [a,Core.wr_get]
  obtain ⟨d,t2,pd,dr,dc⟩ := E5R.Thermostat.QuietBranch.contract B img a ram (pc+4#32) 4#32 off .ne 16 17 (decide (byte.toNat≠literal)) rfl aligned1 targetAligned branch
    (by rw [a16,a17];exact E5R.Thermostat.MainMethodByteMath.neTest byte literal bound)
  refine ⟨d,(E5R.Thermostat.Quiet.Steps.single t).trans t2,?_,(dr 17).trans a17,?_,dc⟩
  · simpa only [decide_eq_true_eq,BitVec.add_assoc,show 4#32+4#32=8#32 by decide +kernel] using pd
  · intro r ne;exact (dr r).trans (by simp [a,Core.wr_get_ne,ne])
end E5R.Thermostat.MainMethodChoice
