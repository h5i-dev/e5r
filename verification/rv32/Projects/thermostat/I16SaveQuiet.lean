-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16Save
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16Save
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80004e5e#32) (hs : c.get 2 = sp+16#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80004e64#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 2 sp 0x80004e60#32
  let r0 := ramWrite ram (sp+12#32) (c.get 1) .w
  let b := a.goto 0x80004e62#32
  let d := b.goto 0x80004e64#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147503710) fun o => ?_
    rw [exec_opimm,hs,hp]
    change interp B img o (.done (c.wr 2 ((sp+16#32)+0xfffffff0#32) 0x80004e60#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show 16#32+0xfffffff0#32 = 0#32 by decide +kernel,BitVec.add_zero];rfl
  have s1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,r0⟩ := by
    refine QuietDet.step_of (by change (0x80004e60#32).getLsbD 0 = false;decide) di2147503712 fun o => ?_
    have hs0 : a.get 2 = sp := by simp [a,Core.wr_get]
    have hv : a.get 1 = c.get 1 := by simp [a,Core.wr_get_ne]
    rw [exec_store,hs0,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨b,r0⟩ ⟨d,memory ram sp c⟩ := by
    refine QuietDet.step_of (by change (0x80004e62#32).getLsbD 0 = false;decide) di2147503714 fun o => ?_
    have hs0 : b.get 2 = sp := by simp [b,a,Core.wr_get]
    have hv : b.get 8 = c.get 8 := by simp [b,a,Core.wr_get_ne]
    rw [exec_store,hs0,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,by rfl⟩
  · simp [d,b,a,Core.wr_get]
  · intro r hr;simp [d,b,a,Core.wr_get_ne,hr]

end E5R.Thermostat.I16Save
