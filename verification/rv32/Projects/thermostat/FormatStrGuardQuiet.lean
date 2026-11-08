-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatStrGuard
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatStrGuard
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt flags : Word)
    (hp : c.pc = 0x800047ac#32) (hsp : c.get 2 = sp) (h10 : c.get 10 = fmt)
    (hm : Memory.Block B fmt 12) (ha : fmt.toNat%4 = 0)
    (hv : ramRead ram (fmt+8#32) .w = flags) (hmask : flags &&& 0x18000000#32 = 0#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000486c#32 ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 13 → r ≠ 19 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 (sp+64#32) 0x800047ae#32
  let c2 := c1.wr 19 flags 0x800047b2#32
  let c3 := c2.wr 13 0x18000000#32 0x800047b6#32
  let c4 := c3.wr 13 0#32 0x800047ba#32
  let d := c4.goto 0x8000486c#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact fs2147501996) fun o => ?_
    rw [exec_opimm,hsp,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800047ae#32).getLsbD 0 = false;decide) fs2147501998 fun o => ?_
    have hf : c1.get 10 = fmt := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned fmt 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),hv];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800047b2#32).getLsbD 0 = false;decide) fs2147502002 fun o => ?_
    rw [exec_lui];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800047b6#32).getLsbD 0 = false;decide) fs2147502006 fun o => ?_
    have hv19 : c3.get 19 = flags := by simp [c3,c2,Core.wr_get_ne,Core.wr_get]
    have hv13 : c3.get 13 = 0x18000000#32 := by simp [c3,Core.wr_get]
    rw [exec_op,hv19,hv13]
    change interp B img o (.done (c3.wr 13 (flags &&& 0x18000000#32) 0x800047ba#32)) ram 0 [] = _
    rw [hmask];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800047ba#32).getLsbD 0 = false;decide) fs2147502010 fun o => ?_
    have hv13 : c4.get 13 = 0#32 := by simp [c4,Core.wr_get]
    rw [exec_branch,hv13,Core.get_zero,show taken .eq 0#32 (0 : Word) = true by decide]
    simp only [ite_true]
    change interp B img o (jump c4 0x8000486c#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,by rfl⟩
  intro r h8 h13 h19
  simp [d,c4,c3,c2,c1,Core.wr_get_ne,h8,h13,h19]

end E5R.Thermostat.FormatStrGuard
