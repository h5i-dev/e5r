-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ParamReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ParamReturn
theorem none_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x800027be#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧ Result d Option.none ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 0#32 0x800027c0#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pm2147493822) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027c0#32).getLsbD 0 = false;decide) pm2147493824 fun o => ?_
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · change d.get 10 = 0#32;simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.ParamReturn
namespace E5R.Thermostat.ParamReturn
theorem range_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat)
    (hn : n < 10000000000) (hp : c.pc = 0x8000280e#32) (hv : c.get 13 = BitVec.ofNat 32 (n/4294967296)) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = (if n ≤ 4294967295 then 1#32 else 0#32) ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (if n ≤ 4294967295 then 1#32 else 0#32) 0x80002812#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pm2147493902) fun o => ?_
    rw [exec_opimm,hv,range_flag n hn,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002812#32).getLsbD 0 = false;decide) pm2147493906 fun o => ?_
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.ParamReturn
