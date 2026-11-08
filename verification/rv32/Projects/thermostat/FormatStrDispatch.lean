import Projects.thermostat.FormatStrCode
import Projects.thermostat.FormatLiterals
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.FormatStrDispatch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fmt writer : Word)
    (hp : c.pc = 0x8000486c#32) (h10 : c.get 10 = fmt) (hm : Memory.Block B fmt 12) (ha : fmt.toNat%4 = 0)
    (hv : ramRead ram (fmt+4#32) .w = 0x80005c04#32) (hw : ramRead ram fmt .w = writer)
    (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004874#32 ∧ d.get 10 = writer ∧ d.get 6 = 0x800022a0#32 ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 10 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 0x80005c04#32 0x8000486e#32
  let c2 := c1.wr 10 writer 0x80004870#32
  let d := c2.wr 6 0x800022a0#32 0x80004874#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact fs2147502188) fun o => ?_
    rw [exec_load,h10,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned fmt 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),hv,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000486e#32).getLsbD 0 = false;decide) fs2147502190 fun o => ?_
    have hf : c1.get 10 = fmt := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_load,hf,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hw];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80004870#32).getLsbD 0 = false;decide) fs2147502192 fun o => ?_
    have hv13 : c2.get 13 = 0x80005c04#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_load,hv13,show 0x80005c04#32+12#32 = 0x80005c10#32 by decide +kernel,
      interp_load_rom (B := B) (img := img) (w := .w) o (by decide) hrom rfl FormatLiterals.cursor_method_word];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,Core.wr_get]
  · intro r h6 h10 h13
    simp [d,c2,c1,Core.wr_get_ne,h6,h10,h13]
end E5R.Thermostat.FormatStrDispatch
