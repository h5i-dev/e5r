import Projects.thermostat.QuietBranch
import Projects.thermostat.Memory
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodByteTest
open E5R E5R.Thermostat

/-- Actual LBU, literal load, and conditional branch. This helper is independent
    of the method strings; its concrete instruction certificates are mandatory. -/
theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc base offset literal branchOffset : Word) (byte : BitVec 8) (cond : BrCond) (test : Bool)
    (hp : c.pc=pc) (h15 : c.get 15=base)
    (memory : B.inRam (base+offset) 1=true) (data : ram (base+offset)=byte)
    (aligned : pc.getLsbD 0=false) (aligned1 : (pc+4#32).getLsbD 0=false)
    (aligned2 : (pc+8#32).getLsbD 0=false) (targetAligned : (pc+8#32+branchOffset).getLsbD 0=false)
    (load : fetchDecode img pc=some (.load .b false 16 15 offset,4#32))
    (lit : fetchDecode img (pc+4#32)=some (.opimm .add 17 0 literal,4#32))
    (branch : fetchDecode img (pc+8#32)=some (.branch cond 16 17 branchOffset,4#32))
    (tested : taken cond (BitVec.ofNat 32 byte.toNat) literal=test) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if test then pc+8#32+branchOffset else pc+12#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=literal ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 16 (BitVec.ofNat 32 byte.toNat) (pc+4#32)
  let b := a.wr 17 literal (pc+8#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];exact aligned) (by rw [hp];exact load) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_load,h15,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) memory,Memory.load_byte,data,hp]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of aligned1 lit fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (Eff.done (a.wr 17 (0#32+literal) (pc+4#32+4#32))) ram 0 [] [] = _
    rw [BitVec.zero_add,BitVec.add_assoc,show 4#32+4#32=8#32 by decide +kernel]
    rfl
  have b16 : b.get 16=BitVec.ofNat 32 byte.toNat := by simp [b,a,Core.wr_get_ne,Core.wr_get]
  have b17 : b.get 17=literal := by simp [b,Core.wr_get]
  obtain ⟨d,t2,pd,dr,dc⟩ := QuietBranch.contract B img b ram (pc+8#32) 4#32 branchOffset cond 16 17 test rfl aligned2 targetAligned branch (by rw [b16,b17];exact tested)
  refine ⟨d,(Quiet.Steps.single t0).trans ((Quiet.Steps.single t1).trans t2),?_,(dr 16).trans b16,(dr 17).trans b17,?_,dc⟩
  · simpa only [BitVec.add_assoc,show 8#32+4#32=12#32 by decide +kernel] using pd
  · intro r h16 h17
    exact (dr r).trans (by simp [b,a,Core.wr_get_ne,Core.wr_get,h16,h17])
end E5R.Thermostat.MainMethodByteTest
