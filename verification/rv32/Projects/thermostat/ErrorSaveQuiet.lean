-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ErrorSave
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ErrorSave
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80001e4a#32) (hs : c.get 2 = sp+16#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80001e52#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x80001e4c#32
  let c2 := c1.goto 0x80001e4e#32
  let r1 := ramWrite ram (sp+12#32) (c.get 1) .w
  let c3 := c2.goto 0x80001e50#32
  let r2 := ramWrite r1 (sp+8#32) (c.get 8) .w
  let c4 := c3.goto 0x80001e52#32
  let r3 := ramWrite r2 (sp+4#32) (c.get 9) .w
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ee2147491402) fun o => ?_
    rw [exec_opimm,hs,hp]
    change interp B img o (.done (c.wr 2 ((sp+16#32)+0xfffffff0#32) 0x80001e4c#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show 16#32+0xfffffff0#32 = 0#32 by decide +kernel,BitVec.add_zero];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x80001e4c#32).getLsbD 0 = false;decide) ee2147491404 fun o => ?_
    have hsp : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001e4e#32).getLsbD 0 = false;decide) ee2147491406 fun o => ?_
    have hsp : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine QuietDet.step_of (by change (0x80001e50#32).getLsbD 0 = false;decide) ee2147491408 fun o => ?_
    have hsp : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];rfl
  refine ⟨c4,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get]
  · intro r hr
    simp [c4,c3,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.ErrorSave
