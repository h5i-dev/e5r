-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ApplyReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ApplyReturn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (ret : Word)
    (hp : c.pc = 0x80001e44) (hr : B.inRam (c.get 2+12#32) 4 = true)
    (ha : (c.get 2+12#32).toNat % 4 = 0)
    (hv : ramRead ram (c.get 2+12#32) .w = ret) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = ret &&& ~~~1 ∧
      d.get 2 = c.get 2+16#32 ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 ret 0x80001e46
  let c2 := c1.wr 2 (c.get 2+16#32) 0x80001e48
  let d := c2.goto (ret &&& ~~~1)
  have h0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact t2147491396) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+12#32) o ha hr,hv,hp]
    rfl
  have h1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e46 : Word).getLsbD 0 = false;decide) t2147491398 fun o => ?_
    have hs : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    rw [exec_opimm,hs]
    rfl
  have h2 : Quiet.Step B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e48 : Word).getLsbD 0 = false;decide) t2147491400 fun o => ?_
    have hr1 : c2.get 1 = ret := by simp [c2,c1,Core.wr_get,Core.wr_get_ne]
    rw [exec_jalr,hr1,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)]
    rfl
  refine ⟨d,.step h0 (.step h1 (.single h2)),rfl,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get]
  · intro r h1' h2'
    simp [d,c2,c1,Core.wr_get_ne,h1',h2']

end E5R.Thermostat.ApplyReturn
