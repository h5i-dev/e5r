-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PrefixSave
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.PrefixSave
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80004e00#32) (hs : c.get 2 = sp+32#32)
    (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80004e0e#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x80004e02#32
  let c2 := c1.goto 0x80004e04#32
  let r1 := ramWrite ram (sp+28#32) (c.get 1) .w
  let c3 := c2.goto 0x80004e06#32
  let r2 := ramWrite r1 (sp+24#32) (c.get 8) .w
  let c4 := c3.goto 0x80004e08#32
  let r3 := ramWrite r2 (sp+20#32) (c.get 9) .w
  let c5 := c4.goto 0x80004e0a#32
  let r4 := ramWrite r3 (sp+16#32) (c.get 18) .w
  let c6 := c5.goto 0x80004e0c#32
  let r5 := ramWrite r4 (sp+12#32) (c.get 19) .w
  let c7 := c6.goto 0x80004e0e#32
  let r6 := ramWrite r5 (sp+8#32) (c.get 20) .w
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wp2147503616) fun o => ?_
    rw [exec_opimm,hs,hp]
    change interp B img o (.done (c.wr 2 ((sp+32#32)+0xffffffe0#32) 0x80004e02#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show 32#32+0xffffffe0#32 = 0#32 by decide +kernel,BitVec.add_zero];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x80004e02#32).getLsbD 0 = false;decide) wp2147503618 fun o => ?_
    have hsp : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x80004e04#32).getLsbD 0 = false;decide) wp2147503620 fun o => ?_
    have hsp : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];rfl
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine QuietDet.step_of (by change (0x80004e06#32).getLsbD 0 = false;decide) wp2147503622 fun o => ?_
    have hsp : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];rfl
  have s4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine QuietDet.step_of (by change (0x80004e08#32).getLsbD 0 = false;decide) wp2147503624 fun o => ?_
    have hsp : c4.get 2 = sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c4.get 18 = c.get 18 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];rfl
  have s5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine QuietDet.step_of (by change (0x80004e0a#32).getLsbD 0 = false;decide) wp2147503626 fun o => ?_
    have hsp : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c5.get 19 = c.get 19 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine QuietDet.step_of (by change (0x80004e0c#32).getLsbD 0 = false;decide) wp2147503628 fun o => ?_
    have hsp : c6.get 2 = sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c6.get 20 = c.get 20 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  refine ⟨c7,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_,?_,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
  · intro r hr
    simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.PrefixSave
