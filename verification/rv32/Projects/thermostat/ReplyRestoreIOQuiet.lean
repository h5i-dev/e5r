-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReplyRestoreIO
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReplyRestore
theorem contract_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000071c) (hm : Memory.Block B (c.get 2) 34)
    (hal : (c.get 2).toNat % 4 = 0) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,result c ram (c.get 2)⟩ ∧ d.pc = 0x80000736 ∧
      d.get 2 = c.get 2 ∧ d.get 20 = c.get 20 ∧ d.get 23 = c.get 23 ∧ d.sameCsr c ∧ BufferRegs.Frame c d := by
  let sp := c.get 2
  let v10 := ramRead ram (sp+4#32) .w
  let r1 := ramWrite ram (sp+30#32) (c.get 27) .h
  let c1 := c.goto 2147485472
  let r2 := ramWrite r1 (sp+32#32) (c.get 25) .h
  let c2 := c1.goto 2147485476
  let r3 := ramWrite r2 (sp+24#32) (c.get 21) .b
  let c3 := c2.goto 2147485480
  let r4 := ramWrite r3 (sp+25#32) (c.get 24) .b
  let c4 := c3.goto 2147485484
  let c5 := c4.wr 10 v10 2147485486
  let r5 := ramWrite r4 (sp+26#32) v10 .h
  let c6 := c5.goto 2147485490
  let r6 := ramWrite r5 (sp+28#32) (c.get 26) .h
  let c7 := c6.goto 2147485494
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    have hs : c.get 2 = sp := by simp [sp,Core.wr_get_ne]
    have ha : (sp+30#32).toNat % 2 = 0 := Memory.half_aligned sp 15 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+30#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 30) (width := 2) hm (by decide) (by decide)
    have hv : c.get 27 = c.get 27 := by simp [Core.wr_get,Core.wr_get_ne]
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact v2147485468) fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+30#32) (v := c.get 27) o ha hr]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    have hs : c1.get 2 = sp := by simp [sp,c1,Core.wr_get_ne]
    have ha : (sp+32#32).toNat % 2 = 0 := Memory.half_aligned sp 16 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+32#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 32) (width := 2) hm (by decide) (by decide)
    have hv : c1.get 25 = c.get 25 := by simp [c1,Core.wr_get,Core.wr_get_ne]
    refine QuietDet.step_of (by change (2147485472 : Word).getLsbD 0 = false;decide) v2147485472 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+32#32) (v := c.get 25) o ha hr]
    rfl
  have s2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    have hs : c2.get 2 = sp := by simp [sp,c2,c1,Core.wr_get_ne]
    have ha : (sp+24#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+24#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 24) (width := 1) hm (by decide) (by decide)
    have hv : c2.get 21 = c.get 21 := by simp [c2,c1,Core.wr_get,Core.wr_get_ne]
    refine QuietDet.step_of (by change (2147485476 : Word).getLsbD 0 = false;decide) v2147485476 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+24#32) (v := c.get 21) o ha hr]
    rfl
  have s3 : Quiet.Step B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
    have hs : c3.get 2 = sp := by simp [sp,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+25#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+25#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 25) (width := 1) hm (by decide) (by decide)
    have hv : c3.get 24 = c.get 24 := by simp [c3,c2,c1,Core.wr_get,Core.wr_get_ne]
    refine QuietDet.step_of (by change (2147485480 : Word).getLsbD 0 = false;decide) v2147485480 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+25#32) (v := c.get 24) o ha hr]
    rfl
  have s4 : Quiet.Step B img ⟨c4,r4⟩ ⟨c5,r4⟩ := by
    have hs : c4.get 2 = sp := by simp [sp,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+4#32).toNat % 4 = 0 := Memory.word_aligned sp 1 hal
    have hr : B.inRam (sp+4#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 4) (width := 4) hm (by decide) (by decide)
    refine QuietDet.step_of (by change (2147485484 : Word).getLsbD 0 = false;decide) v2147485484 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) (a := sp+4#32) o ha hr]
    have hv : ramRead r4 (sp+4#32) .w = ramRead ram (sp+4#32) .w := by
      simp [r4,r3,r2,r1,ramRead,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]
    rw [hv]
    rfl
  have s5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    have hs : c5.get 2 = sp := by simp [sp,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+26#32).toNat % 2 = 0 := Memory.half_aligned sp 13 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+26#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 26) (width := 2) hm (by decide) (by decide)
    have hv : c5.get 10 = v10 := by simp [c5,c4,c3,c2,c1,Core.wr_get,Core.wr_get_ne]
    refine QuietDet.step_of (by change (2147485486 : Word).getLsbD 0 = false;decide) v2147485486 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+26#32) (v := v10) o ha hr]
    rfl
  have s6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    have hs : c6.get 2 = sp := by simp [sp,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+28#32).toNat % 2 = 0 := Memory.half_aligned sp 14 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+28#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 28) (width := 2) hm (by decide) (by decide)
    have hv : c6.get 26 = c.get 26 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get,Core.wr_get_ne]
    refine QuietDet.step_of (by change (2147485490 : Word).getLsbD 0 = false;decide) v2147485490 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+28#32) (v := c.get 26) o ha hr]
    rfl
  have hresult : r6 = result c ram sp := by rfl
  refine ⟨c7,?_,rfl,?_,?_,?_,by rfl,?_⟩
  · rw [← hresult]
    exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6))))))
  · simp [c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
  · simp [c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
  · simp [c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
  · exact ⟨by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]⟩

end E5R.Thermostat.ReplyRestore
