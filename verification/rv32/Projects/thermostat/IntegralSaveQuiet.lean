-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.IntegralSave
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.IntegralSave
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80004514#32) (hsp : c.get 2 = sp+64#32)
    (hm : Memory.Block B sp 64) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80004530#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x80004516#32
  let c2 := c1.goto 0x80004518#32
  let c3 := c2.goto 0x8000451a#32
  let c4 := c3.goto 0x8000451c#32
  let c5 := c4.goto 0x8000451e#32
  let c6 := c5.goto 0x80004520#32
  let c7 := c6.goto 0x80004522#32
  let c8 := c7.goto 0x80004524#32
  let c9 := c8.goto 0x80004526#32
  let c10 := c9.goto 0x80004528#32
  let c11 := c10.goto 0x8000452a#32
  let c12 := c11.goto 0x8000452c#32
  let c13 := c12.goto 0x8000452e#32
  let c14 := c13.goto 0x80004530#32
  let r1 := ramWrite ram (sp+60#32) (c.get 1) .w
  let r2 := ramWrite r1 (sp+56#32) (c.get 8) .w
  let r3 := ramWrite r2 (sp+52#32) (c.get 9) .w
  let r4 := ramWrite r3 (sp+48#32) (c.get 18) .w
  let r5 := ramWrite r4 (sp+44#32) (c.get 19) .w
  let r6 := ramWrite r5 (sp+40#32) (c.get 20) .w
  let r7 := ramWrite r6 (sp+36#32) (c.get 21) .w
  let r8 := ramWrite r7 (sp+32#32) (c.get 22) .w
  let r9 := ramWrite r8 (sp+28#32) (c.get 23) .w
  let r10 := ramWrite r9 (sp+24#32) (c.get 24) .w
  let r11 := ramWrite r10 (sp+20#32) (c.get 25) .w
  let r12 := ramWrite r11 (sp+16#32) (c.get 26) .w
  let r13 := ramWrite r12 (sp+12#32) (c.get 27) .w
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pi2147501332) fun o => ?_
    rw [exec_opimm,hsp]
    simp only [alu]
    rw [BitVec.add_assoc,show 64#32+0xffffffc0#32 = 0#32 by decide +kernel,BitVec.add_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x80004516#32).getLsbD 0 = false;decide) pi2147501334 fun o => ?_
    have hs : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 15 ha) (Memory.block_access hm (off := 60) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x80004518#32).getLsbD 0 = false;decide) pi2147501336 fun o => ?_
    have hs : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 14 ha) (Memory.block_access hm (off := 56) (by decide) (by decide))];rfl
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine QuietDet.step_of (by change (0x8000451a#32).getLsbD 0 = false;decide) pi2147501338 fun o => ?_
    have hs : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 13 ha) (Memory.block_access hm (off := 52) (by decide) (by decide))];rfl
  have s4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine QuietDet.step_of (by change (0x8000451c#32).getLsbD 0 = false;decide) pi2147501340 fun o => ?_
    have hs : c4.get 2 = sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c4.get 18 = c.get 18 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 12 ha) (Memory.block_access hm (off := 48) (by decide) (by decide))];rfl
  have s5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine QuietDet.step_of (by change (0x8000451e#32).getLsbD 0 = false;decide) pi2147501342 fun o => ?_
    have hs : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c5.get 19 = c.get 19 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 11 ha) (Memory.block_access hm (off := 44) (by decide) (by decide))];rfl
  have s6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine QuietDet.step_of (by change (0x80004520#32).getLsbD 0 = false;decide) pi2147501344 fun o => ?_
    have hs : c6.get 2 = sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c6.get 20 = c.get 20 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 10 ha) (Memory.block_access hm (off := 40) (by decide) (by decide))];rfl
  have s7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine QuietDet.step_of (by change (0x80004522#32).getLsbD 0 = false;decide) pi2147501346 fun o => ?_
    have hs : c7.get 2 = sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c7.get 21 = c.get 21 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 9 ha) (Memory.block_access hm (off := 36) (by decide) (by decide))];rfl
  have s8 : Quiet.Step B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine QuietDet.step_of (by change (0x80004524#32).getLsbD 0 = false;decide) pi2147501348 fun o => ?_
    have hs : c8.get 2 = sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c8.get 22 = c.get 22 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))];rfl
  have s9 : Quiet.Step B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine QuietDet.step_of (by change (0x80004526#32).getLsbD 0 = false;decide) pi2147501350 fun o => ?_
    have hs : c9.get 2 = sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c9.get 23 = c.get 23 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))];rfl
  have s10 : Quiet.Step B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine QuietDet.step_of (by change (0x80004528#32).getLsbD 0 = false;decide) pi2147501352 fun o => ?_
    have hs : c10.get 2 = sp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c10.get 24 = c.get 24 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];rfl
  have s11 : Quiet.Step B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine QuietDet.step_of (by change (0x8000452a#32).getLsbD 0 = false;decide) pi2147501354 fun o => ?_
    have hs : c11.get 2 = sp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c11.get 25 = c.get 25 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];rfl
  have s12 : Quiet.Step B img ⟨c12,r11⟩ ⟨c13,r12⟩ := by
    refine QuietDet.step_of (by change (0x8000452c#32).getLsbD 0 = false;decide) pi2147501356 fun o => ?_
    have hs : c12.get 2 = sp := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c12.get 26 = c.get 26 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];rfl
  have s13 : Quiet.Step B img ⟨c13,r12⟩ ⟨c14,r13⟩ := by
    refine QuietDet.step_of (by change (0x8000452e#32).getLsbD 0 = false;decide) pi2147501358 fun o => ?_
    have hs : c13.get 2 = sp := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c13.get 27 = c.get 27 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  refine ⟨c14,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.single s13))))))))))))),rfl,?_,?_,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r hr
    simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr]

end E5R.Thermostat.IntegralSave
