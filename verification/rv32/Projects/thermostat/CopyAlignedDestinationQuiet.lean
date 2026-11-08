-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyAlignedDestination
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyAlignedDestination
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10 = dst) (ha : dst.toNat%4=0)
    (hp : c.pc = 0x80005192#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800051b6#32 ∧
      d.get 13 = 0#32 ∧ d.get 14 = dst ∧ (∀ r : Reg, r ≠ 13 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (0#32-dst) 0x80005196#32
  let c2 := c1.wr 13 (0#32) 0x80005198#32
  let c3 := c2.wr 14 (dst) 0x8000519c#32
  let c4 := c3.goto 0x800051b6#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504530) fun o => ?_
    rw [exec_op,Core.get_zero,h10];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005196#32).getLsbD 0 = false;decide) cp2147504534 fun o => ?_
    have hv : c1.get 13 = 0#32-dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_opimm,hv]
    change interp B img o (.done (c1.wr 13 ((0#32-dst) &&& 3#32) 0x80005198#32)) ram 0 [] = _
    rw [CopyBits.neg_aligned dst ha];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005198#32).getLsbD 0 = false;decide) cp2147504536 fun o => ?_
    have hv10 : c2.get 10 = dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    have hv13 : c2.get 13 = 0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_op,hv10,hv13]
    simp only [alu,BitVec.add_zero];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000519c#32).getLsbD 0 = false;decide) cp2147504540 fun o => ?_
    have hv10 : c3.get 10 = dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    have hv14 : c3.get 14 = dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_branch,hv10,hv14,show E5R.taken .geu dst dst = true by simp [taken,BitVec.ult]]
    simp only [ite_true]
    change interp B img o (jump c3 0x800051b6#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c4,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · intro r h13 h14
    simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h13,h14]

end E5R.Thermostat.CopyAlignedDestination
