import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClDigitLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr value : Word) (h10 : c.get 10=ptr) (hvalue : BitVec.ofNat 32 (ram ptr).toNat=value) (memory : B.inRam ptr 1=true)
    (hp : c.pc=0x8000320a#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000321a#32 ∧
      d.get 30=value ∧ d.get 12=alu .and (alu .add value 0xffffffc6#32) 255#32 ∧ d.get 29=246#32 ∧ (∀ r : Reg, r≠30 → r≠12 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 30 (value) 0x8000320e#32
  let c2 := c1.wr 12 (alu .add value 0xffffffc6#32) 0x80003212#32
  let c3 := c2.wr 12 (alu .and (alu .add value 0xffffffc6#32) 255#32) 0x80003216#32
  let c4 := c3.wr 29 (246#32) 0x8000321a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496458) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) memory,Memory.load_byte,hvalue];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000320e#32).getLsbD 0=false;decide) hh2147496462 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=value := by simp [c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003212#32).getLsbD 0=false;decide) hh2147496466 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v12 : c2.get 12=alu .add value 0xffffffc6#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003216#32).getLsbD 0=false;decide) hh2147496470 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · intro reg h30 h12 h29;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h30,h12,h29]
end E5R.Thermostat.HeadClDigitLoad
