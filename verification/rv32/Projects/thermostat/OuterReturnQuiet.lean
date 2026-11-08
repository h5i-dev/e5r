-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.OuterReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.OuterReturn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800005c4) (hm : Memory.Block B (c.get 2) 96)
    (ha : (c.get 2).toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = ramRead ram (c.get 2+92#32) .w &&& ~~~1 ∧
      d.get 2 = c.get 2+96#32 ∧ d.sameCsr c ∧ Restored c d ram := by
  let c1 := c.wr 1 (ramRead ram (c.get 2+92#32) .w) 0x800005c6
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide)
      (by rw [hp];exact ep2147485124) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+92#32) o
      (Memory.word_aligned (c.get 2) 23 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 92) (width := 4) hm (by decide) (by decide)),hp]
    rfl
  let c2 := c1.wr 8 (ramRead ram (c.get 2+88#32) .w) 0x800005c8
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005c6 : Word).getLsbD 0 = false;decide)
      (by exact ep2147485126) fun o => ?_
    have hs : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+88#32) o
      (Memory.word_aligned (c.get 2) 22 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 88) (width := 4) hm (by decide) (by decide))]
    rfl
  let c3 := c2.wr 9 (ramRead ram (c.get 2+84#32) .w) 0x800005ca
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005c8 : Word).getLsbD 0 = false;decide)
      (by exact ep2147485128) fun o => ?_
    have hs : c2.get 2 = c.get 2 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+84#32) o
      (Memory.word_aligned (c.get 2) 21 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 84) (width := 4) hm (by decide) (by decide))]
    rfl
  let c4 := c3.wr 18 (ramRead ram (c.get 2+80#32) .w) 0x800005cc
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005ca : Word).getLsbD 0 = false;decide)
      (by exact ep2147485130) fun o => ?_
    have hs : c3.get 2 = c.get 2 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+80#32) o
      (Memory.word_aligned (c.get 2) 20 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 80) (width := 4) hm (by decide) (by decide))]
    rfl
  let c5 := c4.wr 19 (ramRead ram (c.get 2+76#32) .w) 0x800005ce
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005cc : Word).getLsbD 0 = false;decide)
      (by exact ep2147485132) fun o => ?_
    have hs : c4.get 2 = c.get 2 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+76#32) o
      (Memory.word_aligned (c.get 2) 19 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 76) (width := 4) hm (by decide) (by decide))]
    rfl
  let c6 := c5.wr 20 (ramRead ram (c.get 2+72#32) .w) 0x800005d0
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005ce : Word).getLsbD 0 = false;decide)
      (by exact ep2147485134) fun o => ?_
    have hs : c5.get 2 = c.get 2 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+72#32) o
      (Memory.word_aligned (c.get 2) 18 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 72) (width := 4) hm (by decide) (by decide))]
    rfl
  let c7 := c6.wr 21 (ramRead ram (c.get 2+68#32) .w) 0x800005d2
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005d0 : Word).getLsbD 0 = false;decide)
      (by exact ep2147485136) fun o => ?_
    have hs : c6.get 2 = c.get 2 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+68#32) o
      (Memory.word_aligned (c.get 2) 17 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 68) (width := 4) hm (by decide) (by decide))]
    rfl
  let c8 := c7.wr 22 (ramRead ram (c.get 2+64#32) .w) 0x800005d4
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005d2 : Word).getLsbD 0 = false;decide)
      (by exact ep2147485138) fun o => ?_
    have hs : c7.get 2 = c.get 2 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+64#32) o
      (Memory.word_aligned (c.get 2) 16 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 64) (width := 4) hm (by decide) (by decide))]
    rfl
  let c9 := c8.wr 23 (ramRead ram (c.get 2+60#32) .w) 0x800005d6
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005d4 : Word).getLsbD 0 = false;decide)
      (by exact ep2147485140) fun o => ?_
    have hs : c8.get 2 = c.get 2 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+60#32) o
      (Memory.word_aligned (c.get 2) 15 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 60) (width := 4) hm (by decide) (by decide))]
    rfl
  let c10 := c9.wr 24 (ramRead ram (c.get 2+56#32) .w) 0x800005d8
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005d6 : Word).getLsbD 0 = false;decide)
      (by exact ep2147485142) fun o => ?_
    have hs : c9.get 2 = c.get 2 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+56#32) o
      (Memory.word_aligned (c.get 2) 14 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 56) (width := 4) hm (by decide) (by decide))]
    rfl
  let c11 := c10.wr 25 (ramRead ram (c.get 2+52#32) .w) 0x800005da
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005d8 : Word).getLsbD 0 = false;decide)
      (by exact ep2147485144) fun o => ?_
    have hs : c10.get 2 = c.get 2 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+52#32) o
      (Memory.word_aligned (c.get 2) 13 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 52) (width := 4) hm (by decide) (by decide))]
    rfl
  let c12 := c11.wr 26 (ramRead ram (c.get 2+48#32) .w) 0x800005dc
  have s11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005da : Word).getLsbD 0 = false;decide)
      (by exact ep2147485146) fun o => ?_
    have hs : c11.get 2 = c.get 2 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+48#32) o
      (Memory.word_aligned (c.get 2) 12 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 48) (width := 4) hm (by decide) (by decide))]
    rfl
  let c13 := c12.wr 27 (ramRead ram (c.get 2+44#32) .w) 0x800005de
  have s12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005dc : Word).getLsbD 0 = false;decide)
      (by exact ep2147485148) fun o => ?_
    have hs : c12.get 2 = c.get 2 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+44#32) o
      (Memory.word_aligned (c.get 2) 11 ha)
      (Memory.block_access (B := B) (p := c.get 2) (n := 96) (off := 44) (width := 4) hm (by decide) (by decide))]
    rfl
  let c14 := c13.wr 2 (c.get 2+96#32) 0x800005e0
  have s13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005de : Word).getLsbD 0 = false;decide) ep2147485150 fun o => ?_
    have hs : c13.get 2 = c.get 2 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_opimm,hs]
    rfl
  let d := c14.goto (ramRead ram (c.get 2+92#32) .w &&& ~~~1)
  have s14 : Quiet.Step B img ⟨c14,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005e0 : Word).getLsbD 0 = false;decide) ep2147485152 fun o => ?_
    have hr : c14.get 1 = ramRead ram (c.get 2+92#32) .w := by
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,Core.wr_get_ne]
    rw [exec_jalr,hr,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)]
    rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.single s14)))))))))))))),rfl,?_,by rfl,?_⟩
  · simp [d,c14,Core.wr_get]
  · constructor <;> simp [d,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,Core.wr_get_ne]

end E5R.Thermostat.OuterReturn
