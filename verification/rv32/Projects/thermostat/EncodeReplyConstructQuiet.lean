-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.EncodeReplyConstruct
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.EncodeReplyConstruct
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp reply modePtr modeLen : Word)
    (hp : c.pc = 0x80001ef0#32) (hs : c.get 2 = sp)
    (h10 : c.get 10 = reply) (h11 : c.get 11 = modeLen) (h12 : c.get 12 = modePtr)
    (hm : Memory.Block B sp 96) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 39 ⟨c,ram⟩ ⟨d,memory ram sp reply modePtr modeLen⟩ ∧ d.pc = 0x80004976#32 ∧
      d.get 11 = 0x80005c04#32 ∧
      d.get 12 = 0x8000574b#32 ∧
      d.get 13 = sp+28#32 ∧
      d.get 14 = reply+1#32 ∧
      d.get 15 = reply+2#32 ∧
      d.get 16 = reply+3#32 ∧
      d.get 17 = 0x80004e5e#32 ∧
      d.get 10 = sp+8#32 ∧
      d.get 1 = 0x80001f62#32 ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 10 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001ef2#32
  let r1 := ramWrite ram (sp+20#32) (modePtr) .w
  let c2 := c1.goto 0x80001ef4#32
  let r2 := ramWrite r1 (sp+24#32) (modeLen) .w
  let c3 := c2.wr 11 (reply+4#32) 0x80001ef8#32
  let c4 := c3.wr 12 (reply+6#32) 0x80001efc#32
  let c5 := c4.wr 13 (reply+8#32) 0x80001f00#32
  let c6 := c5.wr 14 (reply+1#32) 0x80001f04#32
  let c7 := c6.wr 15 (reply+2#32) 0x80001f08#32
  let c8 := c7.wr 16 (reply+3#32) 0x80001f0c#32
  let c9 := c8.wr 17 (0x80005000#32) 0x80001f10#32
  let c10 := c9.wr 17 (0x80004e5e#32) 0x80001f14#32
  let c11 := c10.goto 0x80001f16#32
  let r3 := ramWrite r2 (sp+28#32) (reply+4#32) .w
  let c12 := c11.goto 0x80001f18#32
  let r4 := ramWrite r3 (sp+32#32) (0x80004e5e#32) .w
  let c13 := c12.goto 0x80001f1a#32
  let r5 := ramWrite r4 (sp+36#32) (reply+6#32) .w
  let c14 := c13.goto 0x80001f1c#32
  let r6 := ramWrite r5 (sp+40#32) (0x80004e5e#32) .w
  let c15 := c14.wr 11 (0x80005000#32) 0x80001f20#32
  let c16 := c15.wr 11 (0x80005112#32) 0x80001f24#32
  let c17 := c16.goto 0x80001f26#32
  let r7 := ramWrite r6 (sp+44#32) (reply+8#32) .w
  let c18 := c17.goto 0x80001f28#32
  let r8 := ramWrite r7 (sp+48#32) (0x80005112#32) .w
  let c19 := c18.goto 0x80001f2a#32
  let r9 := ramWrite r8 (sp+52#32) (reply) .w
  let c20 := c19.goto 0x80001f2c#32
  let r10 := ramWrite r9 (sp+56#32) (0x80005112#32) .w
  let c21 := c20.goto 0x80001f2e#32
  let r11 := ramWrite r10 (sp+60#32) (reply+1#32) .w
  let c22 := c21.goto 0x80001f30#32
  let r12 := ramWrite r11 (sp+64#32) (0x80005112#32) .w
  let c23 := c22.goto 0x80001f32#32
  let r13 := ramWrite r12 (sp+68#32) (reply+2#32) .w
  let c24 := c23.goto 0x80001f34#32
  let r14 := ramWrite r13 (sp+72#32) (0x80005112#32) .w
  let c25 := c24.wr 10 (sp+20#32) 0x80001f36#32
  let c26 := c25.wr 12 (0x80002000#32) 0x80001f3a#32
  let c27 := c26.wr 12 (0x8000228c#32) 0x80001f3e#32
  let c28 := c27.goto 0x80001f40#32
  let r15 := ramWrite r14 (sp+76#32) (reply+3#32) .w
  let c29 := c28.goto 0x80001f42#32
  let r16 := ramWrite r15 (sp+80#32) (0x80005112#32) .w
  let c30 := c29.goto 0x80001f44#32
  let r17 := ramWrite r16 (sp+84#32) (sp+20#32) .w
  let c31 := c30.goto 0x80001f46#32
  let r18 := ramWrite r17 (sp+88#32) (0x8000228c#32) .w
  let c32 := c31.wr 11 (0x80006000#32) 0x80001f4a#32
  let c33 := c32.wr 11 (0x80005c04#32) 0x80001f4e#32
  let c34 := c33.wr 12 (0x80005000#32) 0x80001f52#32
  let c35 := c34.wr 12 (0x8000574b#32) 0x80001f56#32
  let c36 := c35.wr 10 (sp+8#32) 0x80001f58#32
  let c37 := c36.wr 13 (sp+28#32) 0x80001f5a#32
  let c38 := c37.wr 1 (0x80004f5a#32) 0x80001f5e#32
  let c39 := c38.wr 1 (0x80001f62#32) 0x80004976#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ej2147491568) fun o => ?_
    have hsp : c.get 2 = sp := by simp [Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c.get 12 = modePtr := by simp [Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001ef2#32).getLsbD 0 = false;decide) ej2147491570 fun o => ?_
    have hsp : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c1.get 11 = modeLen := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001ef4#32).getLsbD 0 = false;decide) ej2147491572 fun o => ?_
    have hv : c2.get 10 = reply := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001ef8#32).getLsbD 0 = false;decide) ej2147491576 fun o => ?_
    have hv : c3.get 10 = reply := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001efc#32).getLsbD 0 = false;decide) ej2147491580 fun o => ?_
    have hv : c4.get 10 = reply := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001f00#32).getLsbD 0 = false;decide) ej2147491584 fun o => ?_
    have hv : c5.get 10 = reply := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001f04#32).getLsbD 0 = false;decide) ej2147491588 fun o => ?_
    have hv : c6.get 10 = reply := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s7 : Quiet.Step B img ⟨c7,r2⟩ ⟨c8,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001f08#32).getLsbD 0 = false;decide) ej2147491592 fun o => ?_
    have hv : c7.get 10 = reply := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s8 : Quiet.Step B img ⟨c8,r2⟩ ⟨c9,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001f0c#32).getLsbD 0 = false;decide) ej2147491596 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have s9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001f10#32).getLsbD 0 = false;decide) ej2147491600 fun o => ?_
    have hv : c9.get 17 = 0x80005000#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r3⟩ := by
    refine QuietDet.step_of (by change (0x80001f14#32).getLsbD 0 = false;decide) ej2147491604 fun o => ?_
    have hsp : c10.get 2 = sp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c10.get 11 = reply+4#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s11 : Quiet.Step B img ⟨c11,r3⟩ ⟨c12,r4⟩ := by
    refine QuietDet.step_of (by change (0x80001f16#32).getLsbD 0 = false;decide) ej2147491606 fun o => ?_
    have hsp : c11.get 2 = sp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c11.get 17 = 0x80004e5e#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s12 : Quiet.Step B img ⟨c12,r4⟩ ⟨c13,r5⟩ := by
    refine QuietDet.step_of (by change (0x80001f18#32).getLsbD 0 = false;decide) ej2147491608 fun o => ?_
    have hsp : c12.get 2 = sp := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c12.get 12 = reply+6#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 9 ha) (Memory.block_access hm (off := 36) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s13 : Quiet.Step B img ⟨c13,r5⟩ ⟨c14,r6⟩ := by
    refine QuietDet.step_of (by change (0x80001f1a#32).getLsbD 0 = false;decide) ej2147491610 fun o => ?_
    have hsp : c13.get 2 = sp := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c13.get 17 = 0x80004e5e#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 ha) (Memory.block_access hm (off := 40) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s14 : Quiet.Step B img ⟨c14,r6⟩ ⟨c15,r6⟩ := by
    refine QuietDet.step_of (by change (0x80001f1c#32).getLsbD 0 = false;decide) ej2147491612 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have s15 : Quiet.Step B img ⟨c15,r6⟩ ⟨c16,r6⟩ := by
    refine QuietDet.step_of (by change (0x80001f20#32).getLsbD 0 = false;decide) ej2147491616 fun o => ?_
    have hv : c15.get 11 = 0x80005000#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s16 : Quiet.Step B img ⟨c16,r6⟩ ⟨c17,r7⟩ := by
    refine QuietDet.step_of (by change (0x80001f24#32).getLsbD 0 = false;decide) ej2147491620 fun o => ?_
    have hsp : c16.get 2 = sp := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c16.get 13 = reply+8#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha) (Memory.block_access hm (off := 44) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s17 : Quiet.Step B img ⟨c17,r7⟩ ⟨c18,r8⟩ := by
    refine QuietDet.step_of (by change (0x80001f26#32).getLsbD 0 = false;decide) ej2147491622 fun o => ?_
    have hsp : c17.get 2 = sp := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c17.get 11 = 0x80005112#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha) (Memory.block_access hm (off := 48) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s18 : Quiet.Step B img ⟨c18,r8⟩ ⟨c19,r9⟩ := by
    refine QuietDet.step_of (by change (0x80001f28#32).getLsbD 0 = false;decide) ej2147491624 fun o => ?_
    have hsp : c18.get 2 = sp := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c18.get 10 = reply := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 13 ha) (Memory.block_access hm (off := 52) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s19 : Quiet.Step B img ⟨c19,r9⟩ ⟨c20,r10⟩ := by
    refine QuietDet.step_of (by change (0x80001f2a#32).getLsbD 0 = false;decide) ej2147491626 fun o => ?_
    have hsp : c19.get 2 = sp := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c19.get 11 = 0x80005112#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 14 ha) (Memory.block_access hm (off := 56) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s20 : Quiet.Step B img ⟨c20,r10⟩ ⟨c21,r11⟩ := by
    refine QuietDet.step_of (by change (0x80001f2c#32).getLsbD 0 = false;decide) ej2147491628 fun o => ?_
    have hsp : c20.get 2 = sp := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c20.get 14 = reply+1#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 15 ha) (Memory.block_access hm (off := 60) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s21 : Quiet.Step B img ⟨c21,r11⟩ ⟨c22,r12⟩ := by
    refine QuietDet.step_of (by change (0x80001f2e#32).getLsbD 0 = false;decide) ej2147491630 fun o => ?_
    have hsp : c21.get 2 = sp := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c21.get 11 = 0x80005112#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 16 ha) (Memory.block_access hm (off := 64) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s22 : Quiet.Step B img ⟨c22,r12⟩ ⟨c23,r13⟩ := by
    refine QuietDet.step_of (by change (0x80001f30#32).getLsbD 0 = false;decide) ej2147491632 fun o => ?_
    have hsp : c22.get 2 = sp := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c22.get 15 = reply+2#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 17 ha) (Memory.block_access hm (off := 68) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s23 : Quiet.Step B img ⟨c23,r13⟩ ⟨c24,r14⟩ := by
    refine QuietDet.step_of (by change (0x80001f32#32).getLsbD 0 = false;decide) ej2147491634 fun o => ?_
    have hsp : c23.get 2 = sp := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c23.get 11 = 0x80005112#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 18 ha) (Memory.block_access hm (off := 72) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s24 : Quiet.Step B img ⟨c24,r14⟩ ⟨c25,r14⟩ := by
    refine QuietDet.step_of (by change (0x80001f34#32).getLsbD 0 = false;decide) ej2147491636 fun o => ?_
    have hv : c24.get 2 = sp := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s25 : Quiet.Step B img ⟨c25,r14⟩ ⟨c26,r14⟩ := by
    refine QuietDet.step_of (by change (0x80001f36#32).getLsbD 0 = false;decide) ej2147491638 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have s26 : Quiet.Step B img ⟨c26,r14⟩ ⟨c27,r14⟩ := by
    refine QuietDet.step_of (by change (0x80001f3a#32).getLsbD 0 = false;decide) ej2147491642 fun o => ?_
    have hv : c26.get 12 = 0x80002000#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s27 : Quiet.Step B img ⟨c27,r14⟩ ⟨c28,r15⟩ := by
    refine QuietDet.step_of (by change (0x80001f3e#32).getLsbD 0 = false;decide) ej2147491646 fun o => ?_
    have hsp : c27.get 2 = sp := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c27.get 16 = reply+3#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 19 ha) (Memory.block_access hm (off := 76) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s28 : Quiet.Step B img ⟨c28,r15⟩ ⟨c29,r16⟩ := by
    refine QuietDet.step_of (by change (0x80001f40#32).getLsbD 0 = false;decide) ej2147491648 fun o => ?_
    have hsp : c28.get 2 = sp := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c28.get 11 = 0x80005112#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 20 ha) (Memory.block_access hm (off := 80) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s29 : Quiet.Step B img ⟨c29,r16⟩ ⟨c30,r17⟩ := by
    refine QuietDet.step_of (by change (0x80001f42#32).getLsbD 0 = false;decide) ej2147491650 fun o => ?_
    have hsp : c29.get 2 = sp := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c29.get 10 = sp+20#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 21 ha) (Memory.block_access hm (off := 84) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s30 : Quiet.Step B img ⟨c30,r17⟩ ⟨c31,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f44#32).getLsbD 0 = false;decide) ej2147491652 fun o => ?_
    have hsp : c30.get 2 = sp := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    have hv : c30.get 12 = 0x8000228c#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 22 ha) (Memory.block_access hm (off := 88) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have s31 : Quiet.Step B img ⟨c31,r18⟩ ⟨c32,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f46#32).getLsbD 0 = false;decide) ej2147491654 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have s32 : Quiet.Step B img ⟨c32,r18⟩ ⟨c33,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f4a#32).getLsbD 0 = false;decide) ej2147491658 fun o => ?_
    have hv : c32.get 11 = 0x80006000#32 := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s33 : Quiet.Step B img ⟨c33,r18⟩ ⟨c34,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f4e#32).getLsbD 0 = false;decide) ej2147491662 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have s34 : Quiet.Step B img ⟨c34,r18⟩ ⟨c35,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f52#32).getLsbD 0 = false;decide) ej2147491666 fun o => ?_
    have hv : c34.get 12 = 0x80005000#32 := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s35 : Quiet.Step B img ⟨c35,r18⟩ ⟨c36,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f56#32).getLsbD 0 = false;decide) ej2147491670 fun o => ?_
    have hv : c35.get 2 = sp := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s36 : Quiet.Step B img ⟨c36,r18⟩ ⟨c37,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f58#32).getLsbD 0 = false;decide) ej2147491672 fun o => ?_
    have hv : c36.get 2 = sp := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have s37 : Quiet.Step B img ⟨c37,r18⟩ ⟨c38,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f5a#32).getLsbD 0 = false;decide) ej2147491674 fun o => ?_
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have s38 : Quiet.Step B img ⟨c38,r18⟩ ⟨c39,r18⟩ := by
    refine QuietDet.step_of (by change (0x80001f5e#32).getLsbD 0 = false;decide) ej2147491678 fun o => ?_
    have hv : c38.get 1 = 0x80004f5a#32 := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
    rw [exec_jalr,hv]
    change interp B img o (.done ((c38.set 1 0x80001f62#32).goto 0x80004976#32)) r18 0 [] = _
    rfl
  refine ⟨c39,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.step s24 (.step s25 (.step s26 (.step s27 (.step s28 (.step s29 (.step s30 (.step s31 (.step s32 (.step s33 (.step s34 (.step s35 (.step s36 (.step s37 (.single s38)))))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12]
  · intro r h11 h12 h13 h14 h15 h16 h17 h10 h1
    simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h12,h11,h12,h13,h14,h15,h16,h17,h10,h1]

end E5R.Thermostat.EncodeReplyConstruct
