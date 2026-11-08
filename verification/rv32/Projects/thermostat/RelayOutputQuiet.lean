-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RelayOutput
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.RelayOutput
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000238) (hstack : Memory.Block B (c.get 2) 64)
    (haStack : (c.get 2).toNat % 4 = 0) (hout : Memory.Block B (c.get 10) 20)
    (haOut : (c.get 10).toNat % 2 = 0) :
    ∃ d, Quiet.Steps B img 17 ⟨c,ram⟩ ⟨d,result ram ram (c.get 2+4#32) (c.get 10)⟩ ∧
      d.pc = 0x800001ac ∧ d.get 2 = c.get 2 ∧ d.get 10 = c.get 10 ∧ d.sameCsr c ∧ Upper.Frame c d := by
  let sp := c.get 2
  let out := c.get 10
  let v0 := extend .h true (ramRead ram (sp+12#32) .h)
  let v1 := extend .h true (ramRead ram (sp+14#32) .h)
  let v2 := extend .h true (ramRead ram (sp+16#32) .h)
  let v3 := extend .h true (ramRead ram (sp+18#32) .h)
  let v4 := extend .h true (ramRead ram (sp+4#32) .h)
  let v5 := extend .h true (ramRead ram (sp+6#32) .h)
  let v6 := extend .h true (ramRead ram (sp+8#32) .h)
  let v7 := extend .h true (ramRead ram (sp+10#32) .h)
  let c1 := c.wr 11 v0 0x8000023c
  let c2 := c1.wr 12 v1 0x80000240
  let c3 := c2.wr 13 v2 0x80000244
  let c4 := c3.wr 14 v3 0x80000248
  let c5 := c4.wr 15 v4 0x8000024c
  let c6 := c5.wr 16 v5 0x80000250
  let c7 := c6.wr 17 v6 0x80000254
  let c8 := c7.wr 5 v7 0x80000258
  let r0 := ram
  let r1 := ramWrite r0 (out+8#32) v0 .h
  let c9 := c8.goto 0x8000025c
  let r2 := ramWrite r1 (out+10#32) v1 .h
  let c10 := c9.goto 0x80000260
  let r3 := ramWrite r2 (out+12#32) v2 .h
  let c11 := c10.goto 0x80000264
  let r4 := ramWrite r3 (out+14#32) v3 .h
  let c12 := c11.goto 0x80000268
  let r5 := ramWrite r4 (out+0#32) v4 .h
  let c13 := c12.goto 0x8000026c
  let r6 := ramWrite r5 (out+2#32) v5 .h
  let c14 := c13.goto 0x80000270
  let r7 := ramWrite r6 (out+4#32) v6 .h
  let c15 := c14.goto 0x80000274
  let r8 := ramWrite r7 (out+6#32) v7 .h
  let c16 := c15.goto 0x80000278
  let d := c16.goto 0x800001ac
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    have hm : B.inRam (sp+12#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 12) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+12#32).toNat % 2 = 0 := Memory.half_aligned sp 6 (by dsimp [sp];omega)
    have ha : c.get 2 = sp := by simp [sp,Core.wr_get_ne]
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp]; exact d2147484216) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+12#32) o hal hm]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    have hm : B.inRam (sp+14#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 14) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+14#32).toNat % 2 = 0 := Memory.half_aligned sp 7 (by dsimp [sp];omega)
    have ha : c1.get 2 = sp := by simp [c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x8000023c : Word).getLsbD 0 = false;decide) (by exact d2147484220) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+14#32) o hal hm]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    have hm : B.inRam (sp+16#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 16) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+16#32).toNat % 2 = 0 := Memory.half_aligned sp 8 (by dsimp [sp];omega)
    have ha : c2.get 2 = sp := by simp [c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000240 : Word).getLsbD 0 = false;decide) (by exact d2147484224) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+16#32) o hal hm]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    have hm : B.inRam (sp+18#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 18) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+18#32).toNat % 2 = 0 := Memory.half_aligned sp 9 (by dsimp [sp];omega)
    have ha : c3.get 2 = sp := by simp [c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000244 : Word).getLsbD 0 = false;decide) (by exact d2147484228) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+18#32) o hal hm]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    have hm : B.inRam (sp+4#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 4) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+4#32).toNat % 2 = 0 := Memory.half_aligned sp 2 (by dsimp [sp];omega)
    have ha : c4.get 2 = sp := by simp [c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000248 : Word).getLsbD 0 = false;decide) (by exact d2147484232) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+4#32) o hal hm]
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    have hm : B.inRam (sp+6#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 6) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+6#32).toNat % 2 = 0 := Memory.half_aligned sp 3 (by dsimp [sp];omega)
    have ha : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x8000024c : Word).getLsbD 0 = false;decide) (by exact d2147484236) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+6#32) o hal hm]
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    have hm : B.inRam (sp+8#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 8) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+8#32).toNat % 2 = 0 := Memory.half_aligned sp 4 (by dsimp [sp];omega)
    have ha : c6.get 2 = sp := by simp [c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000250 : Word).getLsbD 0 = false;decide) (by exact d2147484240) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+8#32) o hal hm]
    rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    have hm : B.inRam (sp+10#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 10) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+10#32).toNat % 2 = 0 := Memory.half_aligned sp 5 (by dsimp [sp];omega)
    have ha : c7.get 2 = sp := by simp [c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000254 : Word).getLsbD 0 = false;decide) (by exact d2147484244) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+10#32) o hal hm]
    rfl
  have s8 : Quiet.Step B img ⟨c8,r0⟩ ⟨c9,r1⟩ := by
    have hm : B.inRam (out+8#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 8) (width := 2) hout (by decide) (by decide)
    have hal : (out+8#32).toNat % 2 = 0 := Memory.half_aligned out 4 haOut
    have ha : c8.get 10 = out := by simp [c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c8.get 11 = v0 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000258 : Word).getLsbD 0 = false;decide) d2147484248 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+8#32) o hal hm]
    rfl
  have s9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r2⟩ := by
    have hm : B.inRam (out+10#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 10) (width := 2) hout (by decide) (by decide)
    have hal : (out+10#32).toNat % 2 = 0 := Memory.half_aligned out 5 haOut
    have ha : c9.get 10 = out := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c9.get 12 = v1 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000025c : Word).getLsbD 0 = false;decide) d2147484252 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+10#32) o hal hm]
    rfl
  have s10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r3⟩ := by
    have hm : B.inRam (out+12#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 12) (width := 2) hout (by decide) (by decide)
    have hal : (out+12#32).toNat % 2 = 0 := Memory.half_aligned out 6 haOut
    have ha : c10.get 10 = out := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c10.get 13 = v2 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000260 : Word).getLsbD 0 = false;decide) d2147484256 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+12#32) o hal hm]
    rfl
  have s11 : Quiet.Step B img ⟨c11,r3⟩ ⟨c12,r4⟩ := by
    have hm : B.inRam (out+14#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 14) (width := 2) hout (by decide) (by decide)
    have hal : (out+14#32).toNat % 2 = 0 := Memory.half_aligned out 7 haOut
    have ha : c11.get 10 = out := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c11.get 14 = v3 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000264 : Word).getLsbD 0 = false;decide) d2147484260 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+14#32) o hal hm]
    rfl
  have s12 : Quiet.Step B img ⟨c12,r4⟩ ⟨c13,r5⟩ := by
    have hm : B.inRam (out+0#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 0) (width := 2) hout (by decide) (by decide)
    have hal : (out+0#32).toNat % 2 = 0 := Memory.half_aligned out 0 haOut
    have ha : c12.get 10 = out := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c12.get 15 = v4 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000268 : Word).getLsbD 0 = false;decide) d2147484264 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+0#32) o hal hm]
    rfl
  have s13 : Quiet.Step B img ⟨c13,r5⟩ ⟨c14,r6⟩ := by
    have hm : B.inRam (out+2#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 2) (width := 2) hout (by decide) (by decide)
    have hal : (out+2#32).toNat % 2 = 0 := Memory.half_aligned out 1 haOut
    have ha : c13.get 10 = out := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c13.get 16 = v5 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000026c : Word).getLsbD 0 = false;decide) d2147484268 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+2#32) o hal hm]
    rfl
  have s14 : Quiet.Step B img ⟨c14,r6⟩ ⟨c15,r7⟩ := by
    have hm : B.inRam (out+4#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 4) (width := 2) hout (by decide) (by decide)
    have hal : (out+4#32).toNat % 2 = 0 := Memory.half_aligned out 2 haOut
    have ha : c14.get 10 = out := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c14.get 17 = v6 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000270 : Word).getLsbD 0 = false;decide) d2147484272 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+4#32) o hal hm]
    rfl
  have s15 : Quiet.Step B img ⟨c15,r7⟩ ⟨c16,r8⟩ := by
    have hm : B.inRam (out+6#32) 2 = true := Memory.block_access (B := B) (p := out) (n := 20) (off := 6) (width := 2) hout (by decide) (by decide)
    have hal : (out+6#32).toNat % 2 = 0 := Memory.half_aligned out 3 haOut
    have ha : c15.get 10 = out := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,out,Core.wr_get_ne]
    have hv : c15.get 5 = v7 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000274 : Word).getLsbD 0 = false;decide) d2147484276 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+6#32) o hal hm]
    rfl
  have s16 : Quiet.Step B img ⟨c16,r8⟩ ⟨d,r8⟩ := by
    have ht : c16.pc+0xffffff34#32 = 0x800001ac#32 := by
      change 0x80000278#32+0xffffff34#32 = 0x800001ac#32
      decide +kernel
    refine QuietDet.step_of (by change (0x80000278 : Word).getLsbD 0 = false;decide) d2147484280 fun o => ?_
    rw [exec_jal,Core.set_zero,ht,jump_ok c16 0x800001ac#32 (by decide)]
    rfl
  have hr : r8 = result ram ram (sp+4#32) out := by
    simp [r8,r7,r6,r5,r4,r3,r2,r1,r0,result,v0,v1,v2,v3,v4,v5,v6,v7,BitVec.add_assoc]
  refine ⟨d,?_,rfl,?_,?_,?_,?_⟩
  · rw [← hr]
    exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.single s16))))))))))))))))
  · simp [d,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
  · simp [d,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
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
    simp [d,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

end E5R.Thermostat.RelayOutput
