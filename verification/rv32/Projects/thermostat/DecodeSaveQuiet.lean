-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.DecodeSave
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.DecodeSave
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80001f6e#32) (hsp : c.get 2 = sp+16#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80001f76#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x80001f70#32
  let c2 := c1.goto 0x80001f72#32
  let c3 := c2.goto 0x80001f74#32
  let d := c3.goto 0x80001f76#32
  let r1 := ramWrite ram (sp+12#32) (c.get 1) .w
  let r2 := ramWrite r1 (sp+8#32) (c.get 8) .w
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491694) fun o => ?_
    rw [exec_opimm,hsp]
    simp only [alu]
    rw [BitVec.add_assoc,show 16#32+0xfffffff0#32 = 0#32 by decide +kernel,BitVec.add_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x80001f70#32).getLsbD 0 = false;decide) tr2147491696 fun o => ?_
    have h2 : c1.get 2 = sp := by simp [c1,Core.wr_get]
    have h1 : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_store,h2,h1,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001f72#32).getLsbD 0 = false;decide) tr2147491698 fun o => ?_
    have h2 : c2.get 2 = sp := by simp [c2,c1,Core.wr_get]
    have h8 : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_store,h2,h8,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨d,memory ram sp c⟩ := by
    refine QuietDet.step_of (by change (0x80001f74#32).getLsbD 0 = false;decide) tr2147491700 fun o => ?_
    have h2 : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get]
    have h9 : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,h2,h9,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,by rfl⟩
  · simp [d,c3,c2,c1,Core.wr_get]
  · intro r hr;simp [d,c3,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.DecodeSave
