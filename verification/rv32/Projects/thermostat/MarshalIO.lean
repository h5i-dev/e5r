import Projects.thermostat.Marshal
import Projects.thermostat.BufferRegs
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Marshal
open E5R E5R.Thermostat

theorem contract_io (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000678) (hm : Memory.Block B (c.get 2) 44)
    (hal : (c.get 2).toNat % 4 = 0) (reply : Spec.Snapshot)
    (hrReply : Encoding.SnapshotAt ram (c.get 2+34#32) reply)
    (h21 : byteOf (c.get 21) 0 = ram (c.get 2+34#32)) :
    ∃ d, DetSteps B img 25 ⟨c,ram⟩ ⟨d,result ram (c.get 2) (c.get 10)⟩ ∧
      d.pc = 0x800006da ∧ d.get 2 = c.get 2 ∧ d.get 20 = c.get 20 ∧
      d.get 23 = c.get 23 ∧ d.sameCsr c ∧ ReplyCache.At d (result ram (c.get 2) (c.get 10)) (c.get 2) reply ∧ BufferRegs.Frame c d := by
  let sp := c.get 2
  let first := c.get 10
  let v11 := extend .b false (ramRead ram (sp+33#32) .b)
  let v12 := extend .b false (ramRead ram (sp+29#32) .b)
  let v13 := extend .b false (ramRead ram (sp+30#32) .b)
  let v14 := extend .b false (ramRead ram (sp+31#32) .b)
  let v15 := extend .b false (ramRead ram (sp+32#32) .b)
  let v16 := extend .b false (ramRead ram (sp+25#32) .b)
  let v17 := extend .b false (ramRead ram (sp+26#32) .b)
  let v5 := extend .b false (ramRead ram (sp+27#32) .b)
  let v6 := extend .b false (ramRead ram (sp+28#32) .b)
  let v24 := extend .b false (ramRead ram (sp+35#32) .b)
  let v7 := extend .h false (ramRead ram (sp+36#32) .h)
  let v26 := extend .h false (ramRead ram (sp+38#32) .h)
  let v27 := extend .h false (ramRead ram (sp+40#32) .h)
  let v25 := extend .h false (ramRead ram (sp+42#32) .h)
  let c1 := c.wr 11 v11 2147485308
  let c2 := c1.wr 12 v12 2147485312
  let c3 := c2.wr 13 v13 2147485316
  let c4 := c3.wr 14 v14 2147485320
  let c5 := c4.wr 15 v15 2147485324
  let c6 := c5.wr 16 v16 2147485328
  let c7 := c6.wr 17 v17 2147485332
  let c8 := c7.wr 5 v5 2147485336
  let c9 := c8.wr 6 v6 2147485340
  let c10 := c9.wr 24 v24 2147485344
  let c11 := c10.wr 7 v7 2147485348
  let r1 := ramWrite ram (sp+4#32) v7 .w
  let c12 := c11.goto 2147485350
  let c13 := c12.wr 26 v26 2147485354
  let r2 := ramWrite r1 (sp+22#32) v15 .b
  let c14 := c13.goto 2147485358
  let r3 := ramWrite r2 (sp+23#32) v11 .b
  let c15 := c14.goto 2147485362
  let c16 := c15.wr 27 v27 2147485366
  let c17 := c16.wr 25 v25 2147485370
  let r4 := ramWrite r3 (sp+18#32) v6 .b
  let c18 := c17.goto 2147485374
  let r5 := ramWrite r4 (sp+19#32) v12 .b
  let c19 := c18.goto 2147485378
  let r6 := ramWrite r5 (sp+20#32) v13 .b
  let c20 := c19.goto 2147485382
  let r7 := ramWrite r6 (sp+21#32) v14 .b
  let c21 := c20.goto 2147485386
  let r8 := ramWrite r7 (sp+14#32) first .b
  let c22 := c21.goto 2147485390
  let r9 := ramWrite r8 (sp+15#32) v16 .b
  let c23 := c22.goto 2147485394
  let r10 := ramWrite r9 (sp+16#32) v17 .b
  let c24 := c23.goto 2147485398
  let r11 := ramWrite r10 (sp+17#32) v5 .b
  let c25 := c24.goto 2147485402
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    have hs : c.get 2 = sp := by simp [sp,Core.wr_get_ne]
    have ha : (sp+33#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+33#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 33) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact t2147485304) fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+33#32) o ha hr]
    rw [hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    have hs : c1.get 2 = sp := by simp [sp,c1,Core.wr_get_ne]
    have ha : (sp+29#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+29#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 29) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485308 : Word).getLsbD 0 = false;decide) t2147485308 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+29#32) o ha hr]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    have hs : c2.get 2 = sp := by simp [sp,c2,c1,Core.wr_get_ne]
    have ha : (sp+30#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+30#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 30) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485312 : Word).getLsbD 0 = false;decide) t2147485312 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+30#32) o ha hr]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    have hs : c3.get 2 = sp := by simp [sp,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+31#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+31#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 31) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485316 : Word).getLsbD 0 = false;decide) t2147485316 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+31#32) o ha hr]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    have hs : c4.get 2 = sp := by simp [sp,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+32#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+32#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 32) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485320 : Word).getLsbD 0 = false;decide) t2147485320 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+32#32) o ha hr]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    have hs : c5.get 2 = sp := by simp [sp,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+25#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+25#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 25) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485324 : Word).getLsbD 0 = false;decide) t2147485324 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+25#32) o ha hr]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    have hs : c6.get 2 = sp := by simp [sp,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+26#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+26#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 26) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485328 : Word).getLsbD 0 = false;decide) t2147485328 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+26#32) o ha hr]
    rfl
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    have hs : c7.get 2 = sp := by simp [sp,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+27#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+27#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 27) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485332 : Word).getLsbD 0 = false;decide) t2147485332 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+27#32) o ha hr]
    rfl
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    have hs : c8.get 2 = sp := by simp [sp,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+28#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+28#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 28) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485336 : Word).getLsbD 0 = false;decide) t2147485336 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+28#32) o ha hr]
    rfl
  have s9 : DetStep B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    have hs : c9.get 2 = sp := by simp [sp,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+35#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+35#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 35) (width := 1) hm (by decide) (by decide)
    refine detStep_of (by change (2147485340 : Word).getLsbD 0 = false;decide) t2147485340 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := sp+35#32) o ha hr]
    rfl
  have s10 : DetStep B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    have hs : c10.get 2 = sp := by simp [sp,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+36#32).toNat % 2 = 0 := Memory.half_aligned sp 18 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+36#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 36) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485344 : Word).getLsbD 0 = false;decide) t2147485344 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+36#32) o ha hr]
    rfl
  have s11 : DetStep B img ⟨c11,ram⟩ ⟨c12,r1⟩ := by
    have hs : c11.get 2 = sp := by simp [sp,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+4#32).toNat % 4 = 0 := Memory.word_aligned sp 1 hal
    have hr : B.inRam (sp+4#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 4) (width := 4) hm (by decide) (by decide)
    have hv : c11.get 7 = v7 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485348 : Word).getLsbD 0 = false;decide) t2147485348 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := sp+4#32) (v := v7) o ha hr]
    rfl
  have s12 : DetStep B img ⟨c12,r1⟩ ⟨c13,r1⟩ := by
    have hs : c12.get 2 = sp := by simp [sp,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+38#32).toNat % 2 = 0 := Memory.half_aligned sp 19 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+38#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 38) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485350 : Word).getLsbD 0 = false;decide) t2147485350 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+38#32) o ha hr]
    have hv : ramRead r1 (sp+38#32) .h = ramRead ram (sp+38#32) .h := by
      simp [r1,ramRead,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]
    rw [hv]
    rfl
  have s13 : DetStep B img ⟨c13,r1⟩ ⟨c14,r2⟩ := by
    have hs : c13.get 2 = sp := by simp [sp,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+22#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+22#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 22) (width := 1) hm (by decide) (by decide)
    have hv : c13.get 15 = v15 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485354 : Word).getLsbD 0 = false;decide) t2147485354 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+22#32) (v := v15) o ha hr]
    rfl
  have s14 : DetStep B img ⟨c14,r2⟩ ⟨c15,r3⟩ := by
    have hs : c14.get 2 = sp := by simp [sp,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+23#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+23#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 23) (width := 1) hm (by decide) (by decide)
    have hv : c14.get 11 = v11 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485358 : Word).getLsbD 0 = false;decide) t2147485358 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+23#32) (v := v11) o ha hr]
    rfl
  have s15 : DetStep B img ⟨c15,r3⟩ ⟨c16,r3⟩ := by
    have hs : c15.get 2 = sp := by simp [sp,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+40#32).toNat % 2 = 0 := Memory.half_aligned sp 20 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+40#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 40) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485362 : Word).getLsbD 0 = false;decide) t2147485362 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+40#32) o ha hr]
    have hv : ramRead r3 (sp+40#32) .h = ramRead ram (sp+40#32) .h := by
      simp [r3,r2,r1,ramRead,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]
    rw [hv]
    rfl
  have s16 : DetStep B img ⟨c16,r3⟩ ⟨c17,r3⟩ := by
    have hs : c16.get 2 = sp := by simp [sp,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+42#32).toNat % 2 = 0 := Memory.half_aligned sp 21 (by dsimp only [sp];omega)
    have hr : B.inRam (sp+42#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 42) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485366 : Word).getLsbD 0 = false;decide) t2147485366 fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .h) (a := sp+42#32) o ha hr]
    have hv : ramRead r3 (sp+42#32) .h = ramRead ram (sp+42#32) .h := by
      simp [r3,r2,r1,ramRead,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]
    rw [hv]
    rfl
  have s17 : DetStep B img ⟨c17,r3⟩ ⟨c18,r4⟩ := by
    have hs : c17.get 2 = sp := by simp [sp,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+18#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+18#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 18) (width := 1) hm (by decide) (by decide)
    have hv : c17.get 6 = v6 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485370 : Word).getLsbD 0 = false;decide) t2147485370 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+18#32) (v := v6) o ha hr]
    rfl
  have s18 : DetStep B img ⟨c18,r4⟩ ⟨c19,r5⟩ := by
    have hs : c18.get 2 = sp := by simp [sp,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+19#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+19#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 19) (width := 1) hm (by decide) (by decide)
    have hv : c18.get 12 = v12 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485374 : Word).getLsbD 0 = false;decide) t2147485374 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+19#32) (v := v12) o ha hr]
    rfl
  have s19 : DetStep B img ⟨c19,r5⟩ ⟨c20,r6⟩ := by
    have hs : c19.get 2 = sp := by simp [sp,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+20#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+20#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 20) (width := 1) hm (by decide) (by decide)
    have hv : c19.get 13 = v13 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485378 : Word).getLsbD 0 = false;decide) t2147485378 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+20#32) (v := v13) o ha hr]
    rfl
  have s20 : DetStep B img ⟨c20,r6⟩ ⟨c21,r7⟩ := by
    have hs : c20.get 2 = sp := by simp [sp,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+21#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+21#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 21) (width := 1) hm (by decide) (by decide)
    have hv : c20.get 14 = v14 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485382 : Word).getLsbD 0 = false;decide) t2147485382 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+21#32) (v := v14) o ha hr]
    rfl
  have s21 : DetStep B img ⟨c21,r7⟩ ⟨c22,r8⟩ := by
    have hs : c21.get 2 = sp := by simp [sp,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+14#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+14#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 14) (width := 1) hm (by decide) (by decide)
    have hv : c21.get 10 = first := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485386 : Word).getLsbD 0 = false;decide) t2147485386 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+14#32) (v := first) o ha hr]
    rfl
  have s22 : DetStep B img ⟨c22,r8⟩ ⟨c23,r9⟩ := by
    have hs : c22.get 2 = sp := by simp [sp,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+15#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+15#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 15) (width := 1) hm (by decide) (by decide)
    have hv : c22.get 16 = v16 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485390 : Word).getLsbD 0 = false;decide) t2147485390 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+15#32) (v := v16) o ha hr]
    rfl
  have s23 : DetStep B img ⟨c23,r9⟩ ⟨c24,r10⟩ := by
    have hs : c23.get 2 = sp := by simp [sp,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+16#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+16#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 16) (width := 1) hm (by decide) (by decide)
    have hv : c23.get 17 = v17 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485394 : Word).getLsbD 0 = false;decide) t2147485394 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+16#32) (v := v17) o ha hr]
    rfl
  have s24 : DetStep B img ⟨c24,r10⟩ ⟨c25,r11⟩ := by
    have hs : c24.get 2 = sp := by simp [sp,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    have ha : (sp+17#32).toNat % 1 = 0 := Nat.mod_one _
    have hr : B.inRam (sp+17#32) 1 = true := Memory.block_access (B := B) (p := sp) (n := 44) (off := 17) (width := 1) hm (by decide) (by decide)
    have hv : c24.get 5 = v5 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,first,Core.wr_get]
    refine detStep_of (by change (2147485398 : Word).getLsbD 0 = false;decide) t2147485398 fun o => ?_
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) (a := sp+17#32) (v := v5) o ha hr]
    rfl
  have hresult : r11 = result ram sp first := by rfl
  refine ⟨c25,?_,rfl,?_,?_,?_,by rfl,?_,?_⟩
  · rw [← hresult]
    exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.single s24))))))))))))))))))))))))
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
  · apply cache_source ram sp first reply c25 hrReply
    · simpa [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne] using h21
    · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,v24,Core.wr_get,Core.wr_get_ne]
    · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,v26,Core.wr_get,Core.wr_get_ne]
    · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,v27,Core.wr_get,Core.wr_get_ne]
    · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,v25,Core.wr_get,Core.wr_get_ne]
  · exact ⟨by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne],by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]⟩
end E5R.Thermostat.Marshal
