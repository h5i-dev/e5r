-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FutureCopy
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.FutureCopy
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (f : Word)
    (hp : c.pc = 0x8000050a#32) (h8 : c.get 8 = f) (hm : Memory.Block B f 41) (ha : f.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,memory ram f⟩ ∧ d.pc = 0x8000052e#32 ∧
      d.get 21 = ramRead ram (f+4#32) .w ∧ d.get 23 = ramRead ram (f+8#32) .w ∧
      d.get 19 = ramRead ram (f+12#32) .w ∧ d.get 18 = ramRead ram (f+16#32) .w ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 18 → r ≠ 19 → r ≠ 21 → r ≠ 23 → d.get r = c.get r) ∧
      d.sameCsr c := by
  let c1 := c.wr 10 (ramRead ram (f+4#32) .w) 0x8000050c#32
  let c2 := c1.wr 11 (ramRead ram (f+8#32) .w) 0x8000050e#32
  let c3 := c2.wr 12 (ramRead ram (f+12#32) .w) 0x80000510#32
  let c4 := c3.wr 13 (ramRead ram (f+16#32) .w) 0x80000512#32
  let c5 := c4.goto 0x80000514#32
  let c6 := c5.goto 0x80000516#32
  let c7 := c6.goto 0x80000518#32
  let c8 := c7.goto 0x8000051a#32
  let c9 := c8.goto 0x8000051e#32
  let c10 := c9.wr 21 (ramRead ram (f+4#32) .w) 0x80000522#32
  let c11 := c10.wr 23 (ramRead ram (f+8#32) .w) 0x80000526#32
  let c12 := c11.wr 19 (ramRead ram (f+12#32) .w) 0x8000052a#32
  let c13 := c12.wr 18 (ramRead ram (f+16#32) .w) 0x8000052e#32
  let r1 := ramWrite ram (f+20#32) (ramRead ram (f+4#32) .w) .w
  let r2 := ramWrite r1 (f+24#32) (ramRead ram (f+8#32) .w) .w
  let r3 := ramWrite r2 (f+28#32) (ramRead ram (f+12#32) .w) .w
  let r4 := ramWrite r3 (f+32#32) (ramRead ram (f+16#32) .w) .w
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wh2147484938) fun o => ?_
    have hf : c.get 8 = f := by simp [Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000050c#32).getLsbD 0 = false;decide) wh2147484940 fun o => ?_
    have hf : c1.get 8 = f := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000050e#32).getLsbD 0 = false;decide) wh2147484942 fun o => ?_
    have hf : c2.get 8 = f := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000510#32).getLsbD 0 = false;decide) wh2147484944 fun o => ?_
    have hf : c3.get 8 = f := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine QuietDet.step_of (by change (0x80000512#32).getLsbD 0 = false;decide) wh2147484946 fun o => ?_
    have hf : c4.get 8 = f := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have hv : c4.get 10 = ramRead ram (f+4#32) .w := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,hf,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];rfl
  have s5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r2⟩ := by
    refine QuietDet.step_of (by change (0x80000514#32).getLsbD 0 = false;decide) wh2147484948 fun o => ?_
    have hf : c5.get 8 = f := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have hv : c5.get 11 = ramRead ram (f+8#32) .w := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,hf,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];rfl
  have s6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r3⟩ := by
    refine QuietDet.step_of (by change (0x80000516#32).getLsbD 0 = false;decide) wh2147484950 fun o => ?_
    have hf : c6.get 8 = f := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have hv : c6.get 12 = ramRead ram (f+12#32) .w := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,hf,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))];rfl
  have s7 : Quiet.Step B img ⟨c7,r3⟩ ⟨c8,r4⟩ := by
    refine QuietDet.step_of (by change (0x80000518#32).getLsbD 0 = false;decide) wh2147484952 fun o => ?_
    have hf : c7.get 8 = f := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have hv : c7.get 13 = ramRead ram (f+16#32) .w := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,hf,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))];rfl
  have s8 : Quiet.Step B img ⟨c8,r4⟩ ⟨c9,memory ram f⟩ := by
    refine QuietDet.step_of (by change (0x8000051a#32).getLsbD 0 = false;decide) wh2147484954 fun o => ?_
    have hf : c8.get 8 = f := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,hf,Core.get_zero,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access hm (off := 36) (by decide) (by decide))];rfl
  have s9 : Quiet.Step B img ⟨c9,memory ram f⟩ ⟨c10,memory ram f⟩ := by
    refine QuietDet.step_of (by change (0x8000051e#32).getLsbD 0 = false;decide) wh2147484958 fun o => ?_
    have hf : c9.get 8 = f := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))]
    have hw : ramRead (memory ram f) (f+20#32) .w = ramRead ram (f+4#32) .w := (words ram f).1
    change interp B img o (.done (c9.wr 21 (ramRead (memory ram f) (f+20#32) .w) 0x80000522#32)) (memory ram f) 0 [] = _
    rw [hw];rfl
  have s10 : Quiet.Step B img ⟨c10,memory ram f⟩ ⟨c11,memory ram f⟩ := by
    refine QuietDet.step_of (by change (0x80000522#32).getLsbD 0 = false;decide) wh2147484962 fun o => ?_
    have hf : c10.get 8 = f := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))]
    have hw : ramRead (memory ram f) (f+24#32) .w = ramRead ram (f+8#32) .w := (words ram f).2.1
    change interp B img o (.done (c10.wr 23 (ramRead (memory ram f) (f+24#32) .w) 0x80000526#32)) (memory ram f) 0 [] = _
    rw [hw];rfl
  have s11 : Quiet.Step B img ⟨c11,memory ram f⟩ ⟨c12,memory ram f⟩ := by
    refine QuietDet.step_of (by change (0x80000526#32).getLsbD 0 = false;decide) wh2147484966 fun o => ?_
    have hf : c11.get 8 = f := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))]
    have hw : ramRead (memory ram f) (f+28#32) .w = ramRead ram (f+12#32) .w := (words ram f).2.2.1
    change interp B img o (.done (c11.wr 19 (ramRead (memory ram f) (f+28#32) .w) 0x8000052a#32)) (memory ram f) 0 [] = _
    rw [hw];rfl
  have s12 : Quiet.Step B img ⟨c12,memory ram f⟩ ⟨c13,memory ram f⟩ := by
    refine QuietDet.step_of (by change (0x8000052a#32).getLsbD 0 = false;decide) wh2147484970 fun o => ?_
    have hf : c12.get 8 = f := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned f 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))]
    have hw : ramRead (memory ram f) (f+32#32) .w = ramRead ram (f+16#32) .w := (words ram f).2.2.2
    change interp B img o (.done (c12.wr 18 (ramRead (memory ram f) (f+32#32) .w) 0x8000052e#32)) (memory ram f) 0 [] = _
    rw [hw];rfl
  refine ⟨c13,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12)))))))))))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h10 h11 h12 h13 h18 h19 h21 h23
    simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h18,h19,h21,h23]

end E5R.Thermostat.FutureCopy
