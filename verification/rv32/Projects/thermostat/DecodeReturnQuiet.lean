-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.DecodeReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.DecodeReturn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80002212#32) (hsp : c.get 2 = sp)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = ramRead ram (sp+12#32) .w &&& ~~~1 ∧ d.get 2 = sp+16#32 ∧
      d.get 1 = ramRead ram (sp+12#32) .w ∧ d.get 8 = ramRead ram (sp+8#32) .w ∧
      d.get 9 = ramRead ram (sp+4#32) .w ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 8 → r ≠ 9 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 (ramRead ram (sp+12#32) .w) 0x80002214#32
  let c2 := c1.wr 8 (ramRead ram (sp+8#32) .w) 0x80002216#32
  let c3 := c2.wr 9 (ramRead ram (sp+4#32) .w) 0x80002218#32
  let c4 := c3.wr 2 (sp+16#32) 0x8000221a#32
  let d := c4.goto (ramRead ram (sp+12#32) .w &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147492370) fun o => ?_
    rw [exec_load,hsp,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide)),hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002214#32).getLsbD 0 = false;decide) wd2147492372 fun o => ?_
    have hv : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,hsp]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002216#32).getLsbD 0 = false;decide) wd2147492374 fun o => ?_
    have hv : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,hsp]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002218#32).getLsbD 0 = false;decide) wd2147492376 fun o => ?_
    have hv : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,hsp]
    rw [exec_opimm,hv];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000221a#32).getLsbD 0 = false;decide) wd2147492378 fun o => ?_
    have hv : c4.get 1 = ramRead ram (sp+12#32) .w := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,c4,Core.wr_get]
  · simp [d,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,c4,c3,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3 h4;simp [d,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3,h4]

end E5R.Thermostat.DecodeReturn
