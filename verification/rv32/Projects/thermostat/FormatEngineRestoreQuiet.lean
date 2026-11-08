-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatEngineRestore
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatEngineRestore
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80004b18#32) (hm : Memory.Block B (c.get 2) 64) (ha : (c.get 2).toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = ramRead ram (c.get 2+60#32) .w &&& ~~~1 ∧ d.get 2 = c.get 2+64#32 ∧
      Restored c d ram ∧ (∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 (ramRead ram (c.get 2+60#32) .w) 0x80004b1a#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact fe2147502872) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 15 ha) (Memory.block_access hm (off := 60) (by decide) (by decide)),hp];rfl
  let c2 := c1.wr 8 (ramRead ram (c.get 2+56#32) .w) 0x80004b1c#32
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b1a#32).getLsbD 0 = false;decide) fe2147502874 fun o => ?_
    have hs : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 14 ha) (Memory.block_access hm (off := 56) (by decide) (by decide))];rfl
  let c3 := c2.wr 9 (ramRead ram (c.get 2+52#32) .w) 0x80004b1e#32
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b1c#32).getLsbD 0 = false;decide) fe2147502876 fun o => ?_
    have hs : c2.get 2 = c.get 2 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 13 ha) (Memory.block_access hm (off := 52) (by decide) (by decide))];rfl
  let c4 := c3.wr 18 (ramRead ram (c.get 2+48#32) .w) 0x80004b20#32
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b1e#32).getLsbD 0 = false;decide) fe2147502878 fun o => ?_
    have hs : c3.get 2 = c.get 2 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 12 ha) (Memory.block_access hm (off := 48) (by decide) (by decide))];rfl
  let c5 := c4.wr 19 (ramRead ram (c.get 2+44#32) .w) 0x80004b22#32
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b20#32).getLsbD 0 = false;decide) fe2147502880 fun o => ?_
    have hs : c4.get 2 = c.get 2 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 11 ha) (Memory.block_access hm (off := 44) (by decide) (by decide))];rfl
  let c6 := c5.wr 20 (ramRead ram (c.get 2+40#32) .w) 0x80004b24#32
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b22#32).getLsbD 0 = false;decide) fe2147502882 fun o => ?_
    have hs : c5.get 2 = c.get 2 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 10 ha) (Memory.block_access hm (off := 40) (by decide) (by decide))];rfl
  let c7 := c6.wr 21 (ramRead ram (c.get 2+36#32) .w) 0x80004b26#32
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b24#32).getLsbD 0 = false;decide) fe2147502884 fun o => ?_
    have hs : c6.get 2 = c.get 2 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 9 ha) (Memory.block_access hm (off := 36) (by decide) (by decide))];rfl
  let c8 := c7.wr 22 (ramRead ram (c.get 2+32#32) .w) 0x80004b28#32
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b26#32).getLsbD 0 = false;decide) fe2147502886 fun o => ?_
    have hs : c7.get 2 = c.get 2 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))];rfl
  let c9 := c8.wr 23 (ramRead ram (c.get 2+28#32) .w) 0x80004b2a#32
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b28#32).getLsbD 0 = false;decide) fe2147502888 fun o => ?_
    have hs : c8.get 2 = c.get 2 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))];rfl
  let c10 := c9.wr 24 (ramRead ram (c.get 2+24#32) .w) 0x80004b2c#32
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b2a#32).getLsbD 0 = false;decide) fe2147502890 fun o => ?_
    have hs : c9.get 2 = c.get 2 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];rfl
  let c11 := c10.wr 25 (ramRead ram (c.get 2+20#32) .w) 0x80004b2e#32
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b2c#32).getLsbD 0 = false;decide) fe2147502892 fun o => ?_
    have hs : c10.get 2 = c.get 2 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];rfl
  let c12 := c11.wr 26 (ramRead ram (c.get 2+16#32) .w) 0x80004b30#32
  have s11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b2e#32).getLsbD 0 = false;decide) fe2147502894 fun o => ?_
    have hs : c11.get 2 = c.get 2 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];rfl
  let c13 := c12.wr 2 (c.get 2+64#32) 0x80004b32#32
  let d := c13.goto (ramRead ram (c.get 2+60#32) .w &&& ~~~1)
  have s12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b30#32).getLsbD 0 = false;decide) fe2147502896 fun o => ?_
    have hs : c12.get 2 = c.get 2 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_opimm,hs];rfl
  have s13 : Quiet.Step B img ⟨c13,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b32#32).getLsbD 0 = false;decide) fe2147502898 fun o => ?_
    have hv : c13.get 1 = ramRead ram (c.get 2+60#32) .w := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,hv,BitVec.add_zero]
    change interp B img o (jump c13 (ramRead ram (c.get 2+60#32) .w &&& ~~~1)) ram 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.single s13))))))))))))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c13,Core.wr_get]
  · constructor
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h8 h9 h18 h19 h20 h21 h22 h23 h24 h25 h26
    simp [d,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h8,h9,h18,h19,h20,h21,h22,h23,h24,h25,h26]

end E5R.Thermostat.FormatEngineRestore
