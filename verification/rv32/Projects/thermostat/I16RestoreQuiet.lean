-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16Restore
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16Restore
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80004f88#32) (hm : Memory.Block B (c.get 2) 16) (ha : (c.get 2).toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = ramRead ram (c.get 2+12#32) .w &&& ~~~1 ∧ d.get 2 = c.get 2+16#32 ∧
      d.get 1 = ramRead ram (c.get 2+12#32) .w ∧ d.get 8 = ramRead ram (c.get 2+8#32) .w ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 8 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 1 (ramRead ram (c.get 2+12#32) .w) 0x80004f8a#32
  let b := a.wr 8 (ramRead ram (c.get 2+8#32) .w) 0x80004f8c#32
  let u := b.wr 2 (c.get 2+16#32) 0x80004f8e#32
  let d := u.goto (ramRead ram (c.get 2+12#32) .w &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147504008) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide)),hp];rfl
  have s1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f8a#32).getLsbD 0 = false;decide) di2147504010 fun o => ?_
    have hs : a.get 2 = c.get 2 := by simp [a,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨b,ram⟩ ⟨u,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f8c#32).getLsbD 0 = false;decide) di2147504012 fun o => ?_
    have hs : b.get 2 = c.get 2 := by simp [b,a,Core.wr_get_ne]
    rw [exec_opimm,hs];rfl
  have s3 : Quiet.Step B img ⟨u,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f8e#32).getLsbD 0 = false;decide) di2147504014 fun o => ?_
    have hr : u.get 1 = ramRead ram (c.get 2+12#32) .w := by simp [u,b,a,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,hr,BitVec.add_zero]
    change interp B img o (jump u (ramRead ram (c.get 2+12#32) .w &&& ~~~1)) ram 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,u,Core.wr_get]
  · simp [d,u,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,u,b,a,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h8;simp [d,u,b,a,Core.wr_get_ne,h1,h2,h8]

end E5R.Thermostat.I16Restore
