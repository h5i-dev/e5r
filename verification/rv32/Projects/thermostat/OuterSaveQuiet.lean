-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.OuterSave
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.OuterSave
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x800004c6#32) (hsp : c.get 2 = sp+96#32)
    (hm : Memory.Block B sp 96) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x800004e2#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x800004c8#32
  let c2 := c1.goto 0x800004ca#32
  let c3 := c2.goto 0x800004cc#32
  let c4 := c3.goto 0x800004ce#32
  let c5 := c4.goto 0x800004d0#32
  let c6 := c5.goto 0x800004d2#32
  let c7 := c6.goto 0x800004d4#32
  let c8 := c7.goto 0x800004d6#32
  let c9 := c8.goto 0x800004d8#32
  let c10 := c9.goto 0x800004da#32
  let c11 := c10.goto 0x800004dc#32
  let c12 := c11.goto 0x800004de#32
  let c13 := c12.goto 0x800004e0#32
  let c14 := c13.goto 0x800004e2#32
  let r1 := ramWrite ram (sp+92#32) (c.get 1) .w
  let r2 := ramWrite r1 (sp+88#32) (c.get 8) .w
  let r3 := ramWrite r2 (sp+84#32) (c.get 9) .w
  let r4 := ramWrite r3 (sp+80#32) (c.get 18) .w
  let r5 := ramWrite r4 (sp+76#32) (c.get 19) .w
  let r6 := ramWrite r5 (sp+72#32) (c.get 20) .w
  let r7 := ramWrite r6 (sp+68#32) (c.get 21) .w
  let r8 := ramWrite r7 (sp+64#32) (c.get 22) .w
  let r9 := ramWrite r8 (sp+60#32) (c.get 23) .w
  let r10 := ramWrite r9 (sp+56#32) (c.get 24) .w
  let r11 := ramWrite r10 (sp+52#32) (c.get 25) .w
  let r12 := ramWrite r11 (sp+48#32) (c.get 26) .w
  let r13 := ramWrite r12 (sp+44#32) (c.get 27) .w
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wh2147484870) fun o => ?_
    rw [exec_opimm,hsp]
    simp only [alu]
    rw [BitVec.add_assoc,show 96#32+0xffffffa0#32 = 0#32 by decide +kernel,BitVec.add_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x800004c8#32).getLsbD 0 = false;decide) wh2147484872 fun o => ?_
    have hs : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 23 ha) (Memory.block_access hm (off := 92) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x800004ca#32).getLsbD 0 = false;decide) wh2147484874 fun o => ?_
    have hs : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 22 ha) (Memory.block_access hm (off := 88) (by decide) (by decide))];rfl
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine QuietDet.step_of (by change (0x800004cc#32).getLsbD 0 = false;decide) wh2147484876 fun o => ?_
    have hs : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 21 ha) (Memory.block_access hm (off := 84) (by decide) (by decide))];rfl
  have s4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine QuietDet.step_of (by change (0x800004ce#32).getLsbD 0 = false;decide) wh2147484878 fun o => ?_
    have hs : c4.get 2 = sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c4.get 18 = c.get 18 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 20 ha) (Memory.block_access hm (off := 80) (by decide) (by decide))];rfl
  have s5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine QuietDet.step_of (by change (0x800004d0#32).getLsbD 0 = false;decide) wh2147484880 fun o => ?_
    have hs : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c5.get 19 = c.get 19 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 19 ha) (Memory.block_access hm (off := 76) (by decide) (by decide))];rfl
  have s6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine QuietDet.step_of (by change (0x800004d2#32).getLsbD 0 = false;decide) wh2147484882 fun o => ?_
    have hs : c6.get 2 = sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c6.get 20 = c.get 20 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 18 ha) (Memory.block_access hm (off := 72) (by decide) (by decide))];rfl
  have s7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine QuietDet.step_of (by change (0x800004d4#32).getLsbD 0 = false;decide) wh2147484884 fun o => ?_
    have hs : c7.get 2 = sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c7.get 21 = c.get 21 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 17 ha) (Memory.block_access hm (off := 68) (by decide) (by decide))];rfl
  have s8 : Quiet.Step B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine QuietDet.step_of (by change (0x800004d6#32).getLsbD 0 = false;decide) wh2147484886 fun o => ?_
    have hs : c8.get 2 = sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c8.get 22 = c.get 22 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 16 ha) (Memory.block_access hm (off := 64) (by decide) (by decide))];rfl
  have s9 : Quiet.Step B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine QuietDet.step_of (by change (0x800004d8#32).getLsbD 0 = false;decide) wh2147484888 fun o => ?_
    have hs : c9.get 2 = sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c9.get 23 = c.get 23 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 15 ha) (Memory.block_access hm (off := 60) (by decide) (by decide))];rfl
  have s10 : Quiet.Step B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine QuietDet.step_of (by change (0x800004da#32).getLsbD 0 = false;decide) wh2147484890 fun o => ?_
    have hs : c10.get 2 = sp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c10.get 24 = c.get 24 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 14 ha) (Memory.block_access hm (off := 56) (by decide) (by decide))];rfl
  have s11 : Quiet.Step B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine QuietDet.step_of (by change (0x800004dc#32).getLsbD 0 = false;decide) wh2147484892 fun o => ?_
    have hs : c11.get 2 = sp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c11.get 25 = c.get 25 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 13 ha) (Memory.block_access hm (off := 52) (by decide) (by decide))];rfl
  have s12 : Quiet.Step B img ⟨c12,r11⟩ ⟨c13,r12⟩ := by
    refine QuietDet.step_of (by change (0x800004de#32).getLsbD 0 = false;decide) wh2147484894 fun o => ?_
    have hs : c12.get 2 = sp := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c12.get 26 = c.get 26 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 12 ha) (Memory.block_access hm (off := 48) (by decide) (by decide))];rfl
  have s13 : Quiet.Step B img ⟨c13,r12⟩ ⟨c14,r13⟩ := by
    refine QuietDet.step_of (by change (0x800004e0#32).getLsbD 0 = false;decide) wh2147484896 fun o => ?_
    have hs : c13.get 2 = sp := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c13.get 27 = c.get 27 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 11 ha) (Memory.block_access hm (off := 44) (by decide) (by decide))];rfl
  refine ⟨c14,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.single s13))))))))))))),rfl,?_,?_,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r hr
    simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr]

end E5R.Thermostat.OuterSave
