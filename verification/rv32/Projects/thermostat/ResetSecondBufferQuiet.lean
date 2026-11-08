-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.SecondBuffer
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.SecondBuffer
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 2147486018#32) (hsp : c.get 2 = 0x80ffeb90#32)
    :
    Quiet.Steps B img 6 ⟨c,ram⟩ (execute c ram) := by
  let c1 := c.wr 11 0#32 2147486020#32
  let c2 := c1.wr 10 2164257679#32 2147486024#32
  let c3 := c2.wr 10 2164257812#32 2147486028#32
  let c4 := c3.wr 12 1024#32 2147486032#32
  let c5 := c4.wr 1 2147506512#32 2147486036#32
  let c6 := c5.wr 1 2147486040#32 2147505720#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact li2147486018) fun o => ?_
    have ha : c.get 0 = 0#32 := by simp [Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp]
    rw [exec_opimm,ha,hp]
    simp only [alu]
    rw [show (0#32)+(0x00000000#32) = 0#32 by decide +kernel]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147486020#32).getLsbD 0 = false;decide) li2147486020 fun o => ?_
    have ha : c1.get 2 = 0x80ffeb90#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x000007ff#32) = 2164257679#32 by decide +kernel]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147486024#32).getLsbD 0 = false;decide) li2147486024 fun o => ?_
    have ha : c2.get 10 = 2164257679#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2164257679#32)+(0x00000085#32) = 2164257812#32 by decide +kernel]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (2147486028#32).getLsbD 0 = false;decide) li2147486028 fun o => ?_
    have ha : c3.get 0 = 0#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000400#32) = 1024#32 by decide +kernel]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (2147486032#32).getLsbD 0 = false;decide) li2147486032 fun o => ?_
    rw [exec_auipc]
    change interp B img o (.done (c4.wr 1 (2147486032#32+0x00005000#32) 2147486036#32)) ram 0 [] = _
    rw [show 2147486032#32+0x00005000#32 = 2147506512#32 by decide +kernel]
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (2147486036#32).getLsbD 0 = false;decide) li2147486036 fun o => ?_
    have hv : c5.get 1 = 2147506512#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp]
    rw [exec_jalr,hv]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5)))))

end E5R.Thermostat.SecondBuffer
