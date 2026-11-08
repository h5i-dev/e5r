-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RelayGuard
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.RelayGuard
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (v : Option Word)
    (hp : c.pc = 0x8000219e#32) (h : ParamReturn.Result c v) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if valid v then 0x800021aa#32 else 0x800021d8#32) ∧
      d.get 10 = 255#32 ∧ d.get 12 = (if valid v then 1#32 else 0#32) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (alu .sltu (c.get 11) 256#32) 0x800021a2#32
  let c2 := c1.wr 12 (if valid v then 1#32 else 0#32) 0x800021a4#32
  let c3 := c2.wr 10 255#32 0x800021a8#32
  let d := c3.goto (if valid v then 0x800021aa#32 else 0x800021d8#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147492254) fun o => ?_
    rw [exec_opimm,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800021a2#32).getLsbD 0 = false;decide) wd2147492258 fun o => ?_
    have hv12 : c1.get 12 = alu .sltu (c.get 11) 256#32 := by simp [c1,Core.wr_get]
    have hv10 : c1.get 10 = c.get 10 := by simp [c1,Core.wr_get_ne]
    rw [exec_op,hv12,hv10]
    change interp B img o (.done (c1.wr 12 (alu .sltu (c.get 11) 256#32 &&& c.get 10) 0x800021a4#32)) ram 0 [] = _
    rw [mask c v h];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800021a4#32).getLsbD 0 = false;decide) wd2147492260 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800021a8#32).getLsbD 0 = false;decide) wd2147492264 fun o => ?_
    have hv : c3.get 12 = (if valid v then 1#32 else 0#32) := by simp [c3,c2,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero]
    cases he : valid v with
    | true => change interp B img o (.done (c3.goto 0x800021aa#32)) ram 0 [] = _;simp only [d,he,ite_true];rfl
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      have hz : taken .eq 0#32 (0 : Word) = true := by decide +kernel
      rw [hz]
      simp only [ite_true]
      change interp B img o (jump c3 (0x800021a8#32+48#32)) ram 0 [] = _
      rw [show 0x800021a8#32+48#32 = 0x800021d8#32 by decide +kernel,jump_ok _ _ (by decide)]
      simp only [d,he,Bool.false_eq_true,ite_false];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c3,Core.wr_get]
  · simp [d,c3,c2,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2;simp [d,c3,c2,c1,Core.wr_get_ne,h1,h2]

end E5R.Thermostat.RelayGuard
