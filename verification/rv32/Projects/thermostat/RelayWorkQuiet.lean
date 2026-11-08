-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RelayWork
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.RelayWork
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800001f4) (hstack : Memory.Block B (c.get 2) 64)
    (haStack : (c.get 2).toNat % 4 = 0) (hout : Memory.Block B (c.get 10) 20)
    (haOut : (c.get 10).toNat % 2 = 0) :
    ∃ d, Quiet.Steps B img 19 ⟨c,ram⟩ ⟨d,result ram (c.get 2) (c.get 10)⟩ ∧
      d.pc = 0x80000238 ∧ d.get 2 = c.get 2 ∧ d.get 10 = c.get 10 ∧ d.sameCsr c ∧ Upper.Frame c d := by
  let sp := c.get 2
  let out := c.get 10
  let vt := extend .h true (ramRead ram (sp+30#32) .h)
  let vhs := extend .h true (ramRead ram (sp+32#32) .h)
  let wlo := ramRead ram (sp+24#32) .w
  let whi := ramRead ram (sp+28#32) .w
  let vlo := extend .h true (ramRead ram (sp+24#32) .h)
  let vhi := extend .h true (ramRead ram (sp+26#32) .h)
  let vsp := extend .h true (ramRead ram (sp+28#32) .h)
  let vhu := extend .h false (ramRead ram (sp+32#32) .h)
  let r0 := ram
  let c1 := c.wr 11 vt 0x800001f8
  let c2 := c1.wr 12 vhs 0x800001fc
  let c3 := c2.wr 13 wlo 0x800001fe
  let c4 := c3.wr 14 whi 0x80000200
  let c5 := c4.wr 15 vlo 0x80000204
  let c6 := c5.wr 16 vhi 0x80000208
  let c7 := c6.wr 17 vsp 0x8000020c
  let c8 := c7.wr 5 vhu 0x80000210
  let r1 := ramWrite r0 (sp+20#32) vt .h
  let c9 := c8.goto 0x80000214
  let c10 := c9.wr 11 vt 0x80000218
  let r2 := ramWrite r1 (sp+4#32) wlo .w
  let c11 := c10.goto 0x8000021a
  let r3 := ramWrite r2 (sp+8#32) whi .w
  let c12 := c11.goto 0x8000021c
  let r4 := ramWrite r3 (sp+12#32) vhs .h
  let c13 := c12.goto 0x80000220
  let r5 := ramWrite r4 (sp+14#32) vlo .h
  let c14 := c13.goto 0x80000224
  let r6 := ramWrite r5 (sp+16#32) vhi .h
  let c15 := c14.goto 0x80000228
  let r7 := ramWrite r6 (sp+18#32) vsp .h
  let c16 := c15.goto 0x8000022c
  let r8 := ramWrite r7 (sp+22#32) vhu .h
  let c17 := c16.goto 0x80000230
  let r9 := ramWrite r8 (out+16#32) vt .h
  let c18 := c17.goto 0x80000234
  let r10 := ramWrite r9 (out+18#32) vhu .h
  let c19 := c18.goto 0x80000238
  have s0 : Quiet.Step B img ⟨c,r0⟩ ⟨c1,r0⟩ := by
    have hm : B.inRam (sp+30#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 30) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+30#32).toNat % 2 = 0 := Memory.half_aligned sp 15 (by dsimp only [sp];omega)
    have ha : c.get 2 = sp := by simp [sp,Core.wr_get_ne]
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp]; exact d2147484148) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+30#32) o hal hm]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,r0⟩ ⟨c2,r0⟩ := by
    have hm : B.inRam (sp+32#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 32) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+32#32).toNat % 2 = 0 := Memory.half_aligned sp 16 (by dsimp only [sp];omega)
    have ha : c1.get 2 = sp := by simp [c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001f8 : Word).getLsbD 0 = false;decide) (by exact d2147484152) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+32#32) o hal hm]
    rfl
  have s2 : Quiet.Step B img ⟨c2,r0⟩ ⟨c3,r0⟩ := by
    have hm : B.inRam (sp+24#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 24) (width := 4) hstack (by decide) (by decide)
    have hal : (sp+24#32).toNat % 4 = 0 := Memory.word_aligned sp 6 haStack
    have ha : c2.get 2 = sp := by simp [c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001fc : Word).getLsbD 0 = false;decide) (by exact d2147484156) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .w) (a := sp+24#32) o hal hm]
    rfl
  have s3 : Quiet.Step B img ⟨c3,r0⟩ ⟨c4,r0⟩ := by
    have hm : B.inRam (sp+28#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 28) (width := 4) hstack (by decide) (by decide)
    have hal : (sp+28#32).toNat % 4 = 0 := Memory.word_aligned sp 7 haStack
    have ha : c3.get 2 = sp := by simp [c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001fe : Word).getLsbD 0 = false;decide) (by exact d2147484158) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .w) (a := sp+28#32) o hal hm]
    rfl
  have s4 : Quiet.Step B img ⟨c4,r0⟩ ⟨c5,r0⟩ := by
    have hm : B.inRam (sp+24#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 24) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+24#32).toNat % 2 = 0 := Memory.half_aligned sp 12 (by dsimp only [sp];omega)
    have ha : c4.get 2 = sp := by simp [c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000200 : Word).getLsbD 0 = false;decide) (by exact d2147484160) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+24#32) o hal hm]
    rfl
  have s5 : Quiet.Step B img ⟨c5,r0⟩ ⟨c6,r0⟩ := by
    have hm : B.inRam (sp+26#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 26) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+26#32).toNat % 2 = 0 := Memory.half_aligned sp 13 (by dsimp only [sp];omega)
    have ha : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000204 : Word).getLsbD 0 = false;decide) (by exact d2147484164) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+26#32) o hal hm]
    rfl
  have s6 : Quiet.Step B img ⟨c6,r0⟩ ⟨c7,r0⟩ := by
    have hm : B.inRam (sp+28#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 28) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+28#32).toNat % 2 = 0 := Memory.half_aligned sp 14 (by dsimp only [sp];omega)
    have ha : c6.get 2 = sp := by simp [c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000208 : Word).getLsbD 0 = false;decide) (by exact d2147484168) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+28#32) o hal hm]
    rfl
  have s7 : Quiet.Step B img ⟨c7,r0⟩ ⟨c8,r0⟩ := by
    have hm : B.inRam (sp+32#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 32) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+32#32).toNat % 2 = 0 := Memory.half_aligned sp 16 (by dsimp only [sp];omega)
    have ha : c7.get 2 = sp := by simp [c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x8000020c : Word).getLsbD 0 = false;decide) (by exact d2147484172) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+32#32) o hal hm]
    rfl
  have s8 : Quiet.Step B img ⟨c8,r0⟩ ⟨c9,r1⟩ := by
    have hm : B.inRam (sp+20#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 20) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+20#32).toNat % 2 = 0 := Memory.half_aligned sp 10 (by dsimp only [sp];omega)
    have ha : c8.get 2 = sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c8.get 11 = vt := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000210 : Word).getLsbD 0 = false;decide) (by exact d2147484176) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+20#32) (v := vt) o hal hm]
    rfl
  have s9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r1⟩ := by
    have hm : B.inRam (sp+20#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 20) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+20#32).toNat % 2 = 0 := Memory.half_aligned sp 10 (by dsimp only [sp];omega)
    have ha : c9.get 2 = sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000214 : Word).getLsbD 0 = false;decide) (by exact d2147484180) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+20#32) o hal hm]
    have hv : extend .h true (ramRead r1 (sp+20#32) .h) = vt :=
      Fields.half_store_load ram (sp+20#32) ((ramRead ram (sp+30#32) .h).setWidth 16)
    rw [hv]
    rfl
  have s10 : Quiet.Step B img ⟨c10,r1⟩ ⟨c11,r2⟩ := by
    have hm : B.inRam (sp+4#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 4) (width := 4) hstack (by decide) (by decide)
    have hal : (sp+4#32).toNat % 4 = 0 := Memory.word_aligned sp 1 haStack
    have ha : c10.get 2 = sp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c10.get 13 = wlo := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000218 : Word).getLsbD 0 = false;decide) (by exact d2147484184) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := sp+4#32) (v := wlo) o hal hm]
    rfl
  have s11 : Quiet.Step B img ⟨c11,r2⟩ ⟨c12,r3⟩ := by
    have hm : B.inRam (sp+8#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 8) (width := 4) hstack (by decide) (by decide)
    have hal : (sp+8#32).toNat % 4 = 0 := Memory.word_aligned sp 2 haStack
    have ha : c11.get 2 = sp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c11.get 14 = whi := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000021a : Word).getLsbD 0 = false;decide) (by exact d2147484186) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := sp+8#32) (v := whi) o hal hm]
    rfl
  have s12 : Quiet.Step B img ⟨c12,r3⟩ ⟨c13,r4⟩ := by
    have hm : B.inRam (sp+12#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 12) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+12#32).toNat % 2 = 0 := Memory.half_aligned sp 6 (by dsimp only [sp];omega)
    have ha : c12.get 2 = sp := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c12.get 12 = vhs := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000021c : Word).getLsbD 0 = false;decide) (by exact d2147484188) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+12#32) (v := vhs) o hal hm]
    rfl
  have s13 : Quiet.Step B img ⟨c13,r4⟩ ⟨c14,r5⟩ := by
    have hm : B.inRam (sp+14#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 14) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+14#32).toNat % 2 = 0 := Memory.half_aligned sp 7 (by dsimp only [sp];omega)
    have ha : c13.get 2 = sp := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c13.get 15 = vlo := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000220 : Word).getLsbD 0 = false;decide) (by exact d2147484192) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+14#32) (v := vlo) o hal hm]
    rfl
  have s14 : Quiet.Step B img ⟨c14,r5⟩ ⟨c15,r6⟩ := by
    have hm : B.inRam (sp+16#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 16) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+16#32).toNat % 2 = 0 := Memory.half_aligned sp 8 (by dsimp only [sp];omega)
    have ha : c14.get 2 = sp := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c14.get 16 = vhi := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000224 : Word).getLsbD 0 = false;decide) (by exact d2147484196) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+16#32) (v := vhi) o hal hm]
    rfl
  have s15 : Quiet.Step B img ⟨c15,r6⟩ ⟨c16,r7⟩ := by
    have hm : B.inRam (sp+18#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 18) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+18#32).toNat % 2 = 0 := Memory.half_aligned sp 9 (by dsimp only [sp];omega)
    have ha : c15.get 2 = sp := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c15.get 17 = vsp := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000228 : Word).getLsbD 0 = false;decide) (by exact d2147484200) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+18#32) (v := vsp) o hal hm]
    rfl
  have s16 : Quiet.Step B img ⟨c16,r7⟩ ⟨c17,r8⟩ := by
    have hm : B.inRam (sp+22#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 22) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+22#32).toNat % 2 = 0 := Memory.half_aligned sp 11 (by dsimp only [sp];omega)
    have ha : c16.get 2 = sp := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    have hv : c16.get 5 = vhu := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000022c : Word).getLsbD 0 = false;decide) (by exact d2147484204) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := sp+22#32) (v := vhu) o hal hm]
    rfl
  have s17 : Quiet.Step B img ⟨c17,r8⟩ ⟨c18,r9⟩ := by
    have hm : B.inRam (out+16#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 16) (width := 2) hout (by decide) (by decide)
    have hal : (out+16#32).toNat % 2 = 0 := Memory.half_aligned out 8 (by exact haOut)
    have ha : c17.get 10 = out := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c17.get 11 = vt := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000230 : Word).getLsbD 0 = false;decide) (by exact d2147484208) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+16#32) (v := vt) o hal hm]
    rfl
  have s18 : Quiet.Step B img ⟨c18,r9⟩ ⟨c19,r10⟩ := by
    have hm : B.inRam (out+18#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 18) (width := 2) hout (by decide) (by decide)
    have hal : (out+18#32).toNat % 2 = 0 := Memory.half_aligned out 9 (by exact haOut)
    have ha : c18.get 10 = out := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c18.get 5 = vhu := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000234 : Word).getLsbD 0 = false;decide) (by exact d2147484212) fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+18#32) (v := vhu) o hal hm]
    rfl
  have hr : r10 = result ram sp out := by
    rfl
  refine ⟨c19,?_,rfl,?_,?_,?_,?_⟩
  · rw [← hr]
    exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.single s18))))))))))))))))))
  · simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
  · simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
  · rfl

  · intro r hr
    have hn0 := Upper.ne_low r hr 0 (by decide)
    have hn1 := Upper.ne_low r hr 1 (by decide)
    have hn2 := Upper.ne_low r hr 2 (by decide)
    have hn3 := Upper.ne_low r hr 3 (by decide)
    have hn4 := Upper.ne_low r hr 4 (by decide)
    have hn5 := Upper.ne_low r hr 5 (by decide)
    have hn6 := Upper.ne_low r hr 6 (by decide)
    have hn7 := Upper.ne_low r hr 7 (by decide)
    have hn8 := Upper.ne_low r hr 8 (by decide)
    have hn9 := Upper.ne_low r hr 9 (by decide)
    have hn10 := Upper.ne_low r hr 10 (by decide)
    have hn11 := Upper.ne_low r hr 11 (by decide)
    have hn12 := Upper.ne_low r hr 12 (by decide)
    have hn13 := Upper.ne_low r hr 13 (by decide)
    have hn14 := Upper.ne_low r hr 14 (by decide)
    have hn15 := Upper.ne_low r hr 15 (by decide)
    have hn16 := Upper.ne_low r hr 16 (by decide)
    have hn17 := Upper.ne_low r hr 17 (by decide)
    have hn18 := Upper.ne_low r hr 18 (by decide)
    have hn19 := Upper.ne_low r hr 19 (by decide)
    have hn20 := Upper.ne_low r hr 20 (by decide)
    have hn21 := Upper.ne_low r hr 21 (by decide)
    simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

end E5R.Thermostat.RelayWork
