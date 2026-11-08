import Projects.thermostat.CommitCode
import Projects.thermostat.Fields
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StateStore
open E5R E5R.Thermostat

/-- Cached snapshot fields are stored beside the RefCell borrow word. -/
def result (ram : Word → BitVec 8) (sp eng : Word) : Word → BitVec 8 :=
  let v10 := extend .h true (ramRead ram (sp+30#32) .h)
  let v11 := extend .h true (ramRead ram (sp+32#32) .h)
  let v12 := ramRead ram eng .w
  let v13 := extend .h true (ramRead ram (sp+24#32) .h)
  let v14 := extend .h true (ramRead ram (sp+28#32) .h)
  let v15 := extend .h true (ramRead ram (sp+26#32) .h)
  let r1 := ramWrite ram (eng+10#32) v10 .h
  let r2 := ramWrite r1 (eng+12#32) v11 .h
  let r3 := ramWrite r2 (eng+0#32) (v12+1#32) .w
  let r4 := ramWrite r3 (eng+4#32) v13 .h
  let r5 := ramWrite r4 (eng+6#32) v15 .h
  let r6 := ramWrite r5 (eng+8#32) v14 .h
  r6

theorem bytes (ram : Word → BitVec 8) (sp eng : Word) (i : Fin 10) :
    result ram sp eng ((eng+4#32)+BitVec.ofNat 32 i.val) = ram ((sp+24#32)+BitVec.ofNat 32 i.val) := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
    i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals simp [h,result,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right,
    Memory.load_half_byte0,Memory.load_half_byte1]

theorem source (ram : Word → BitVec 8) (sp eng : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram (sp+24#32) s) :
    Encoding.SnapshotAt (result ram sp eng) (eng+4#32) s := by
  intro i
  exact (bytes ram sp eng i).trans (hs i)

theorem borrow (ram : Word → BitVec 8) (sp eng : Word) :
    ramRead (result ram sp eng) eng .w = ramRead ram eng .w+1#32 := by
  calc
    ramRead (result ram sp eng) eng .w =
        ramRead (ramWrite ram eng (ramRead ram eng .w+1#32) .w) eng .w := by
      apply ramRead_w_congr
      intro k hk
      have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hc with h|h|h|h
      all_goals simp [h,result,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]
    _ = _ := ramRead_ramWrite_w _ _ _

theorem released (ram : Word → BitVec 8) (sp eng : Word)
    (hb : ramRead ram eng .w = 0xffffffff#32) :
    ramRead (result ram sp eng) eng .w = 0#32 := by
  rw [borrow,hb]
  decide +kernel

theorem frame (ram : Word → BitVec 8) (sp eng x : Word)
    (hx : ∀ i : Fin 14, x ≠ eng+BitVec.ofNat 32 i.val) : result ram sp eng x = ram x := by
  have hn0 := hx ⟨0,by decide⟩
  have hn1 := hx ⟨1,by decide⟩
  have hn2 := hx ⟨2,by decide⟩
  have hn3 := hx ⟨3,by decide⟩
  have hn4 := hx ⟨4,by decide⟩
  have hn5 := hx ⟨5,by decide⟩
  have hn6 := hx ⟨6,by decide⟩
  have hn7 := hx ⟨7,by decide⟩
  have hn8 := hx ⟨8,by decide⟩
  have hn9 := hx ⟨9,by decide⟩
  have hn10 := hx ⟨10,by decide⟩
  have hn11 := hx ⟨11,by decide⟩
  have hn12 := hx ⟨12,by decide⟩
  have hn13 := hx ⟨13,by decide⟩
  simp [result,ramWrite,ramPut,BitVec.add_assoc] at *
  simp_all

/-- Actual stores of the computed state and release of the borrow. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800006ea) (hm : Memory.Block B (c.get 2) 34)
    (hal : (c.get 2).toNat % 2 = 0) (he : Memory.Block B (c.get 23) 14)
    (hae : (c.get 23).toNat % 4 = 0) (hstate : c.get 20 = c.get 23+4#32) :
    ∃ d, DetSteps B img 13 ⟨c,ram⟩ ⟨d,result ram (c.get 2) (c.get 23)⟩ ∧
      d.pc = 0x8000071c ∧ d.get 2 = c.get 2 ∧ d.get 20 = c.get 20 ∧
      d.get 23 = c.get 23 ∧ d.sameCsr c ∧
      (∀ rr : Reg, rr ≠ 10 → rr ≠ 11 → rr ≠ 12 → rr ≠ 13 → rr ≠ 14 → rr ≠ 15 → d.get rr = c.get rr) := by
  let sp := c.get 2
  let eng := c.get 23
  let v10 := extend .h true (ramRead ram (sp+30#32) .h)
  let v11 := extend .h true (ramRead ram (sp+32#32) .h)
  let v12 := ramRead ram eng .w
  let v13 := extend .h true (ramRead ram (sp+24#32) .h)
  let v14 := extend .h true (ramRead ram (sp+28#32) .h)
  let v15 := extend .h true (ramRead ram (sp+26#32) .h)
  let c1 := c.wr 10 v10 2147485422
  let c2 := c1.wr 11 v11 2147485426
  let c3 := c2.wr 12 v12 2147485430
  let c4 := c3.wr 13 v13 2147485434
  let c5 := c4.wr 14 v14 2147485438
  let c6 := c5.wr 15 v15 2147485442
  let r1 := ramWrite ram (eng+10#32) v10 .h
  let c7 := c6.goto 2147485446
  let r2 := ramWrite r1 (eng+12#32) v11 .h
  let c8 := c7.goto 2147485450
  let c9 := c8.wr 12 (v12+1#32) 2147485452
  let r3 := ramWrite r2 (eng+0#32) (v12+1#32) .w
  let c10 := c9.goto 2147485456
  let r4 := ramWrite r3 (eng+4#32) v13 .h
  let c11 := c10.goto 2147485460
  let r5 := ramWrite r4 (eng+6#32) v15 .h
  let c12 := c11.goto 2147485464
  let r6 := ramWrite r5 (eng+8#32) v14 .h
  let c13 := c12.goto 2147485468
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    have hs : c.get 2 = sp := by simp [sp,eng,hstate,Core.wr_get_ne]
    have ha : (sp+30#32).toNat % 2 = 0 := Memory.half_aligned sp 15 hal
    have hr : B.inRam (sp+30#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 30) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact t2147485418) fun o => ?_
    rw [exec_load,hs]
    rw [interp_load_ram (B := B) (img := img) (w := .h) (a := sp+30#32) o ha hr]
    rw [hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    have hs : c1.get 2 = sp := by simp [c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (sp+32#32).toNat % 2 = 0 := Memory.half_aligned sp 16 hal
    have hr : B.inRam (sp+32#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 32) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485422 : Word).getLsbD 0 = false;decide) t2147485422 fun o => ?_
    rw [exec_load,hs]
    rw [interp_load_ram (B := B) (img := img) (w := .h) (a := sp+32#32) o ha hr]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    have hs : c2.get 23 = eng := by simp [c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (eng+0#32).toNat % 4 = 0 := by simpa using hae
    have hr : B.inRam (eng+0#32) 4 = true := Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
    refine detStep_of (by change (2147485426 : Word).getLsbD 0 = false;decide) t2147485426 fun o => ?_
    rw [exec_load,hs]
    rw [BitVec.add_zero]
    simp only [BitVec.add_zero] at ha hr
    rw [interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    have hs : c3.get 2 = sp := by simp [c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (sp+24#32).toNat % 2 = 0 := Memory.half_aligned sp 12 hal
    have hr : B.inRam (sp+24#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 24) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485430 : Word).getLsbD 0 = false;decide) t2147485430 fun o => ?_
    rw [exec_load,hs]
    rw [interp_load_ram (B := B) (img := img) (w := .h) (a := sp+24#32) o ha hr]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    have hs : c4.get 2 = sp := by simp [c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (sp+28#32).toNat % 2 = 0 := Memory.half_aligned sp 14 hal
    have hr : B.inRam (sp+28#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 28) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485434 : Word).getLsbD 0 = false;decide) t2147485434 fun o => ?_
    rw [exec_load,hs]
    rw [interp_load_ram (B := B) (img := img) (w := .h) (a := sp+28#32) o ha hr]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    have hs : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (sp+26#32).toNat % 2 = 0 := Memory.half_aligned sp 13 hal
    have hr : B.inRam (sp+26#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 34) (off := 26) (width := 2) hm (by decide) (by decide)
    refine detStep_of (by change (2147485438 : Word).getLsbD 0 = false;decide) t2147485438 fun o => ?_
    rw [exec_load,hs]
    rw [interp_load_ram (B := B) (img := img) (w := .h) (a := sp+26#32) o ha hr]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,r1⟩ := by
    have hs : c6.get 20 = (eng+4#32) := by simp [c6,c5,c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (eng+10#32).toNat % 2 = 0 := Memory.half_aligned eng 5 (by dsimp only [eng];omega)
    have hr : B.inRam (eng+10#32) 2 = true := Memory.block_access (B := B) (p := eng) (n := 14) (off := 10) (width := 2) he (by decide) (by decide)
    have hv : c6.get 10 = v10 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine detStep_of (by change (2147485442 : Word).getLsbD 0 = false;decide) t2147485442 fun o => ?_
    rw [exec_store,hs,hv]
    simp only [BitVec.add_assoc,BitVec.add_zero,show 4#32+2#32 = 6#32 by decide +kernel,show 4#32+4#32 = 8#32 by decide +kernel,show 4#32+6#32 = 10#32 by decide +kernel,show 4#32+8#32 = 12#32 by decide +kernel]
    rw [interp_store_ram (B := B) (img := img) (w := .h) (a := eng+10#32) (v := v10) o ha hr]
    rfl
  have s7 : DetStep B img ⟨c7,r1⟩ ⟨c8,r2⟩ := by
    have hs : c7.get 20 = (eng+4#32) := by simp [c7,c6,c5,c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (eng+12#32).toNat % 2 = 0 := Memory.half_aligned eng 6 (by dsimp only [eng];omega)
    have hr : B.inRam (eng+12#32) 2 = true := Memory.block_access (B := B) (p := eng) (n := 14) (off := 12) (width := 2) he (by decide) (by decide)
    have hv : c7.get 11 = v11 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine detStep_of (by change (2147485446 : Word).getLsbD 0 = false;decide) t2147485446 fun o => ?_
    rw [exec_store,hs,hv]
    simp only [BitVec.add_assoc,BitVec.add_zero,show 4#32+2#32 = 6#32 by decide +kernel,show 4#32+4#32 = 8#32 by decide +kernel,show 4#32+6#32 = 10#32 by decide +kernel,show 4#32+8#32 = 12#32 by decide +kernel]
    rw [interp_store_ram (B := B) (img := img) (w := .h) (a := eng+12#32) (v := v11) o ha hr]
    rfl
  have s8 : DetStep B img ⟨c8,r2⟩ ⟨c9,r2⟩ := by
    have hv : c8.get 12 = v12 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine detStep_of (by change (2147485450 : Word).getLsbD 0 = false;decide) t2147485450 fun o => ?_
    rw [exec_opimm,hv]
    rfl
  have s9 : DetStep B img ⟨c9,r2⟩ ⟨c10,r3⟩ := by
    have hs : c9.get 23 = eng := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (eng+0#32).toNat % 4 = 0 := by simpa using hae
    have hr : B.inRam (eng+0#32) 4 = true := Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
    have hv : c9.get 12 = (v12+1#32) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine detStep_of (by change (2147485452 : Word).getLsbD 0 = false;decide) t2147485452 fun o => ?_
    rw [exec_store,hs,hv]
    rw [BitVec.add_zero]
    simp only [BitVec.add_zero] at ha hr
    rw [interp_store_ram (B := B) (img := img) (w := .w) (a := eng) (v := (v12+1#32)) o ha hr]
    simp only [r3,BitVec.add_zero]
    rfl
  have s10 : DetStep B img ⟨c10,r3⟩ ⟨c11,r4⟩ := by
    have hs : c10.get 20 = (eng+4#32) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (eng+4#32).toNat % 2 = 0 := Memory.half_aligned eng 2 (by dsimp only [eng];omega)
    have hr : B.inRam (eng+4#32) 2 = true := Memory.block_access (B := B) (p := eng) (n := 14) (off := 4) (width := 2) he (by decide) (by decide)
    have hv : c10.get 13 = v13 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine detStep_of (by change (2147485456 : Word).getLsbD 0 = false;decide) t2147485456 fun o => ?_
    rw [exec_store,hs,hv]
    simp only [BitVec.add_assoc,BitVec.add_zero,show 4#32+2#32 = 6#32 by decide +kernel,show 4#32+4#32 = 8#32 by decide +kernel,show 4#32+6#32 = 10#32 by decide +kernel,show 4#32+8#32 = 12#32 by decide +kernel]
    rw [interp_store_ram (B := B) (img := img) (w := .h) (a := eng+4#32) (v := v13) o ha hr]
    rfl
  have s11 : DetStep B img ⟨c11,r4⟩ ⟨c12,r5⟩ := by
    have hs : c11.get 20 = (eng+4#32) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (eng+6#32).toNat % 2 = 0 := Memory.half_aligned eng 3 (by dsimp only [eng];omega)
    have hr : B.inRam (eng+6#32) 2 = true := Memory.block_access (B := B) (p := eng) (n := 14) (off := 6) (width := 2) he (by decide) (by decide)
    have hv : c11.get 15 = v15 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine detStep_of (by change (2147485460 : Word).getLsbD 0 = false;decide) t2147485460 fun o => ?_
    rw [exec_store,hs,hv]
    simp only [BitVec.add_assoc,BitVec.add_zero,show 4#32+2#32 = 6#32 by decide +kernel,show 4#32+4#32 = 8#32 by decide +kernel,show 4#32+6#32 = 10#32 by decide +kernel,show 4#32+8#32 = 12#32 by decide +kernel]
    rw [interp_store_ram (B := B) (img := img) (w := .h) (a := eng+6#32) (v := v15) o ha hr]
    rfl
  have s12 : DetStep B img ⟨c12,r5⟩ ⟨c13,r6⟩ := by
    have hs : c12.get 20 = (eng+4#32) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,eng,hstate,Core.wr_get_ne]
    have ha : (eng+8#32).toNat % 2 = 0 := Memory.half_aligned eng 4 (by dsimp only [eng];omega)
    have hr : B.inRam (eng+8#32) 2 = true := Memory.block_access (B := B) (p := eng) (n := 14) (off := 8) (width := 2) he (by decide) (by decide)
    have hv : c12.get 14 = v14 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine detStep_of (by change (2147485464 : Word).getLsbD 0 = false;decide) t2147485464 fun o => ?_
    rw [exec_store,hs,hv]
    simp only [BitVec.add_assoc,BitVec.add_zero,show 4#32+2#32 = 6#32 by decide +kernel,show 4#32+4#32 = 8#32 by decide +kernel,show 4#32+6#32 = 10#32 by decide +kernel,show 4#32+8#32 = 12#32 by decide +kernel]
    rw [interp_store_ram (B := B) (img := img) (w := .h) (a := eng+8#32) (v := v14) o ha hr]
    rfl
  have hresult : r6 = result ram sp eng := by rfl
  refine ⟨c13,?_,rfl,?_,?_,?_,by rfl,?_⟩
  · rw [← hresult]
    exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12))))))))))))
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,eng,Core.wr_get_ne]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,eng,Core.wr_get_ne]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,sp,eng,Core.wr_get_ne]
  · intro rr h10 h11 h12 h13 h14 h15
    simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h10,h11,h12,h13,h14,h15]
end E5R.Thermostat.StateStore
