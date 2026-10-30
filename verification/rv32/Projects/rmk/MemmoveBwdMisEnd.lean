/-
  memmove, backward direction, n ≥ 16, source and destination NOT
  congruent mod 4: the end block 0x8002103a..0x80021084 (pinned RMK image),
  one path per misalignment o. It gathers the `4 - o` source bytes below
  the last loaded word into the stack temporary at sp+0x20 and stores the
  last merged word below `a1`.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.MemmoveBwdMisStart

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-- What the end block leaves: the source word at `Lq - 4 + o` stored below
    `a1`, the temporary word at sp+0x20 possibly changed, nothing else. -/
structure AtBT (g g' : Core) (R0 R' : Word → BitVec 8) (Lq : Word) (o : Nat) : Prop where
  pc : g'.pc = 0x80021088
  csr : g'.sameCsr g
  ram : ∃ Rt : Word → BitVec 8,
    (∀ x, ¬ ((g.get 2 + 0x20#32).toNat ≤ x.toNat ∧ x.toNat < (g.get 2 + 0x20#32).toNat + 4) → Rt x = R0 x) ∧
    R' = ramWrite Rt (g.get 11 + 0xfffffffc#32) (ramRead R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 o) .w) .w
  frame : ∀ r : Reg, r.val ∉ [6, 9, 12, 13, 14, 30] → g'.get r = g.get r

theorem bendVal (t a5 : Word) (o : Nat) (ho : 0 < o ∧ o < 4) :
    alu .or (alu .srl t (BitVec.ofNat 32 (8 * o))) (alu .sll a5 (alu .and (alu .sub 0 (BitVec.ofNat 32 (8 * o))) 0x18#32)) =
      (t >>> (8 * o)) ||| (a5 <<< (32 - 8 * o)) := by
  obtain ⟨e1, e2⟩ := shifts o ho
  simp only [alu, e1, e2]

theorem ramWrite_h_bytes (R : Word → BitVec 8) (a v : Word) :
    ramWrite R a v .h a = byteOf v 0 ∧ ramWrite R a v .h (a + 1) = byteOf v 1 ∧
    ∀ x, x ≠ a → x ≠ a + 1 → ramWrite R a v .h x = R x := by
  have hne : a ≠ a + 1 := by bv_omega
  refine ⟨?_, ?_, ?_⟩
  · simp [ramWrite, ramPut, hne]
  · simp [ramWrite, ramPut]
  · intro x h1 h2; simp only [ramWrite]; rw [ramPut_ne _ h2, ramPut_ne _ h1]

/-- o = 1: one byte and one halfword into the temporary. -/
theorem bend1 (g : Core) (R0 : Word → BitVec 8) (Lq : Word) (hpc : g.pc = 0x8002103a) (hq : Quiet g)
    (hLq : g.get 30 + g.get 18 = Lq) (h6 : g.get 6 = BitVec.ofNat 32 1) (h29 : g.get 29 = BitVec.ofNat 32 (8 * 1))
    (hprev : ∀ k, k < 1 → byteOf (g.get 15) k = R0 (Lq + BitVec.ofNat 32 k))
    (hL : Lq.toNat % 4 = 0) (hL4 : 4 ≤ Lq.toNat)
    (hsrc : B.inRam (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1) 3 = true)
    (hT : B.inRam (g.get 2 + 0x20#32) 4 = true) (hTa : (g.get 2 + 0x20#32).toNat % 4 = 0)
    (hsep : ∀ j < 3, ∀ i < 4, Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + BitVec.ofNat 32 j ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i)
    (hD : (g.get 11 + 0xfffffffc#32).toNat % 4 = 0) (hDr : B.inRam (g.get 11 + 0xfffffffc#32) 4 = true) :
    ∃ g' R', QRun B img 27 ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtBT g g' R0 R' Lq 1 := by
  have hTr := (B_ram _ _).mp hT
  let e1 := g.wr 30 (alu .add (g.get 30) (g.get 18)) 0x8002103c
  let e2 := e1.wr 12 (alu .add (e1.get 0) 0x00000000#32) 0x8002103e
  let e3 := e2.wr 14 (alu .add (e2.get 30) (e2.get 6)) 0x80021042
  let e4 := e3.wr 13 (alu .add (e3.get 0) 0x00000004#32) 0x80021044
  let eR1 := ramWrite R0 (e4.get 2 + 0x00000020#32) (e4.get 0) .w
  let e5 := e4.goto 0x80021046
  let e6 := e5.wr 9 (alu .add (e5.get 2) 0x00000020#32) 0x80021048
  let e7 := e6.wr 13 (alu .sub (e6.get 13) (e6.get 6)) 0x8002104c
  let e8 := e7.wr 6 (alu .or (e7.get 9) (e7.get 6)) 0x80021050
  let e9 := e8.wr 9 (alu .and (e8.get 13) 0x00000001#32) 0x80021054
  let e10 := e9.wr 14 (alu .add (e9.get 14) 0xfffffffc#32) 0x80021056
  let e11 := e10.goto 0x80021058
  let e12 := e11.wr 12 (extend .b false (ramRead eR1 (e11.get 14 + 0x00000000#32) .b)) 0x8002105c
  let eR2 := ramWrite eR1 (e12.get 6 + 0x00000000#32) (e12.get 12) .b
  let e13 := e12.goto 0x80021060
  let e14 := e13.wr 12 (alu .add (e13.get 0) 0x00000001#32) 0x80021062
  let e15 := e14.wr 13 (alu .and (e14.get 13) 0x00000002#32) 0x80021064
  let e16 := e15.goto 0x80021066
  let e17 := e16.wr 14 (alu .add (e16.get 14) (e16.get 12)) 0x80021068
  let e18 := e17.wr 13 (extend .h true (ramRead eR2 (e17.get 14 + 0x00000000#32) .h)) 0x8002106c
  let e19 := e18.wr 12 (alu .add (e18.get 12) (e18.get 6)) 0x8002106e
  let eR3 := ramWrite eR2 (e19.get 12 + 0x00000000#32) (e19.get 13) .h
  let e20 := e19.goto 0x80021072
  let e21 := e20.wr 12 (extend .w true (ramRead eR3 (e20.get 2 + 0x00000020#32) .w)) 0x80021074
  let e22 := e21.wr 13 (alu .sub (e21.get 0) (e21.get 29)) 0x80021078
  let e23 := e22.wr 13 (alu .and (e22.get 13) 0x00000018#32) 0x8002107a
  let e24 := e23.wr 13 (alu .sll (e23.get 15) (e23.get 13)) 0x8002107e
  let e25 := e24.wr 12 (alu .srl (e24.get 12) (e24.get 29)) 0x80021082
  let e26 := e25.wr 12 (alu .or (e25.get 12) (e25.get 13)) 0x80021084
  let eR4 := ramWrite eR3 (e26.get 11 + 0xfffffffc#32) (e26.get 12) .w
  let e27 := e26.goto 0x80021088
  have a18 : e17.get 14 + 0x00000000#32 = Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32 := by
    simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; bv_omega
  have a20 : e19.get 12 + 0x00000000#32 = g.get 2 + 0x20#32 + 2#32 := by
    simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]
    rw [or_small _ _ hTa (by decide)]; bv_omega
  have HIN_5 : B.inRam (e4.get 2 + 0x00000020#32) 4 = true := by
    rw [show e4.get 2 = g.get 2 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hT
  have HAL_5 : (e4.get 2 + 0x00000020#32).toNat % 4 = 0 := by
    rw [show e4.get 2 = g.get 2 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hTa
  have HBR_11 : taken .eq (e10.get 9) (e10.get 0) = false := by
    rw [show e10.get 9 = 1#32 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], Core.get_zero]; decide
  have HIN_12 : B.inRam (e11.get 14 + 0x00000000#32) 1 = true := by
    rw [show e11.get 14 + 0x00000000#32 = Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; bv_omega]
    exact (B_ram _ _).mpr (by have := (B_ram _ _).mp hsrc; omega)
  have HIN_13 : B.inRam (e12.get 6 + 0x00000000#32) 1 = true := by
    rw [show e12.get 6 + 0x00000000#32 = g.get 2 + 0x20#32 + 1#32 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; exact or_small _ _ hTa (by decide)]
    exact (B_ram _ _).mpr (by constructor <;> bv_omega)
  have HBR_16 : taken .eq (e15.get 13) (e15.get 0) = false := by
    rw [show e15.get 13 = 2#32 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], Core.get_zero]; decide
  have HIN_18 : B.inRam (e17.get 14 + 0x00000000#32) 2 = true := by
    rw [a18]; exact (B_ram _ _).mpr (by have := (B_ram _ _).mp hsrc; constructor <;> bv_omega)
  have HAL_18 : (e17.get 14 + 0x00000000#32).toNat % 2 = 0 := by
    rw [a18]; bv_omega
  have HIN_20 : B.inRam (e19.get 12 + 0x00000000#32) 2 = true := by
    rw [a20]; exact (B_ram _ _).mpr (by constructor <;> bv_omega)
  have HAL_20 : (e19.get 12 + 0x00000000#32).toNat % 2 = 0 := by
    rw [a20]; bv_omega
  have HIN_21 : B.inRam (e20.get 2 + 0x00000020#32) 4 = true := by
    rw [show e20.get 2 = g.get 2 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hT
  have HAL_21 : (e20.get 2 + 0x00000020#32).toNat % 4 = 0 := by
    rw [show e20.get 2 = g.get 2 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hTa
  have HIN_27 : B.inRam (e26.get 11 + 0xfffffffc#32) 4 = true := by
    rw [show e26.get 11 = g.get 11 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hDr
  have HAL_27 : (e26.get 11 + 0xfffffffc#32).toNat % 4 = 0 := by
    rw [show e26.get 11 = g.get 11 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hD
  have es1 : DetStep B img ⟨g, R0⟩ ⟨e1, R0⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8002103a) fun o => ?_
    rw [exec_op, hpc]; rfl
  have es2 : DetStep B img ⟨e1, R0⟩ ⟨e2, R0⟩ := by
    refine detStep_of (by show (0x8002103c : Word).getLsbD 0 = false; decide) f8002103c fun o => ?_
    rw [exec_opimm]; rfl
  have es3 : DetStep B img ⟨e2, R0⟩ ⟨e3, R0⟩ := by
    refine detStep_of (by show (0x8002103e : Word).getLsbD 0 = false; decide) f8002103e fun o => ?_
    rw [exec_op]; rfl
  have es4 : DetStep B img ⟨e3, R0⟩ ⟨e4, R0⟩ := by
    refine detStep_of (by show (0x80021042 : Word).getLsbD 0 = false; decide) f80021042 fun o => ?_
    rw [exec_opimm]; rfl
  have es5 : DetStep B img ⟨e4, R0⟩ ⟨e5, eR1⟩ := by
    refine detStep_of (by show (0x80021044 : Word).getLsbD 0 = false; decide) f80021044 fun o => ?_
    rw [exec_store, interp_store_ram (w := .w) o HAL_5 HIN_5]; rfl
  have es6 : DetStep B img ⟨e5, eR1⟩ ⟨e6, eR1⟩ := by
    refine detStep_of (by show (0x80021046 : Word).getLsbD 0 = false; decide) f80021046 fun o => ?_
    rw [exec_opimm]; rfl
  have es7 : DetStep B img ⟨e6, eR1⟩ ⟨e7, eR1⟩ := by
    refine detStep_of (by show (0x80021048 : Word).getLsbD 0 = false; decide) f80021048 fun o => ?_
    rw [exec_op]; rfl
  have es8 : DetStep B img ⟨e7, eR1⟩ ⟨e8, eR1⟩ := by
    refine detStep_of (by show (0x8002104c : Word).getLsbD 0 = false; decide) f8002104c fun o => ?_
    rw [exec_op]; rfl
  have es9 : DetStep B img ⟨e8, eR1⟩ ⟨e9, eR1⟩ := by
    refine detStep_of (by show (0x80021050 : Word).getLsbD 0 = false; decide) f80021050 fun o => ?_
    rw [exec_opimm]; rfl
  have es10 : DetStep B img ⟨e9, eR1⟩ ⟨e10, eR1⟩ := by
    refine detStep_of (by show (0x80021054 : Word).getLsbD 0 = false; decide) f80021054 fun o => ?_
    rw [exec_opimm]; rfl
  have es11 : DetStep B img ⟨e10, eR1⟩ ⟨e11, eR1⟩ := by
    refine detStep_of (by show (0x80021056 : Word).getLsbD 0 = false; decide) f80021056 fun o => ?_
    rw [exec_branch, HBR_11]; rfl
  have es12 : DetStep B img ⟨e11, eR1⟩ ⟨e12, eR1⟩ := by
    refine detStep_of (by show (0x80021058 : Word).getLsbD 0 = false; decide) f80021058 fun o => ?_
    rw [exec_load, interp_load_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_12]; rfl
  have es13 : DetStep B img ⟨e12, eR1⟩ ⟨e13, eR2⟩ := by
    refine detStep_of (by show (0x8002105c : Word).getLsbD 0 = false; decide) f8002105c fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_13]; rfl
  have es14 : DetStep B img ⟨e13, eR2⟩ ⟨e14, eR2⟩ := by
    refine detStep_of (by show (0x80021060 : Word).getLsbD 0 = false; decide) f80021060 fun o => ?_
    rw [exec_opimm]; rfl
  have es15 : DetStep B img ⟨e14, eR2⟩ ⟨e15, eR2⟩ := by
    refine detStep_of (by show (0x80021062 : Word).getLsbD 0 = false; decide) f80021062 fun o => ?_
    rw [exec_opimm]; rfl
  have es16 : DetStep B img ⟨e15, eR2⟩ ⟨e16, eR2⟩ := by
    refine detStep_of (by show (0x80021064 : Word).getLsbD 0 = false; decide) f80021064 fun o => ?_
    rw [exec_branch, HBR_16]; rfl
  have es17 : DetStep B img ⟨e16, eR2⟩ ⟨e17, eR2⟩ := by
    refine detStep_of (by show (0x80021066 : Word).getLsbD 0 = false; decide) f80021066 fun o => ?_
    rw [exec_op]; rfl
  have es18 : DetStep B img ⟨e17, eR2⟩ ⟨e18, eR2⟩ := by
    refine detStep_of (by show (0x80021068 : Word).getLsbD 0 = false; decide) f80021068 fun o => ?_
    rw [exec_load, interp_load_ram (w := .h) o HAL_18 HIN_18]; rfl
  have es19 : DetStep B img ⟨e18, eR2⟩ ⟨e19, eR2⟩ := by
    refine detStep_of (by show (0x8002106c : Word).getLsbD 0 = false; decide) f8002106c fun o => ?_
    rw [exec_op]; rfl
  have es20 : DetStep B img ⟨e19, eR2⟩ ⟨e20, eR3⟩ := by
    refine detStep_of (by show (0x8002106e : Word).getLsbD 0 = false; decide) f8002106e fun o => ?_
    rw [exec_store, interp_store_ram (w := .h) o HAL_20 HIN_20]; rfl
  have es21 : DetStep B img ⟨e20, eR3⟩ ⟨e21, eR3⟩ := by
    refine detStep_of (by show (0x80021072 : Word).getLsbD 0 = false; decide) f80021072 fun o => ?_
    rw [exec_load, interp_load_ram (w := .w) o HAL_21 HIN_21]; rfl
  have es22 : DetStep B img ⟨e21, eR3⟩ ⟨e22, eR3⟩ := by
    refine detStep_of (by show (0x80021074 : Word).getLsbD 0 = false; decide) f80021074 fun o => ?_
    rw [exec_op]; rfl
  have es23 : DetStep B img ⟨e22, eR3⟩ ⟨e23, eR3⟩ := by
    refine detStep_of (by show (0x80021078 : Word).getLsbD 0 = false; decide) f80021078 fun o => ?_
    rw [exec_opimm]; rfl
  have es24 : DetStep B img ⟨e23, eR3⟩ ⟨e24, eR3⟩ := by
    refine detStep_of (by show (0x8002107a : Word).getLsbD 0 = false; decide) f8002107a fun o => ?_
    rw [exec_op]; rfl
  have es25 : DetStep B img ⟨e24, eR3⟩ ⟨e25, eR3⟩ := by
    refine detStep_of (by show (0x8002107e : Word).getLsbD 0 = false; decide) f8002107e fun o => ?_
    rw [exec_op]; rfl
  have es26 : DetStep B img ⟨e25, eR3⟩ ⟨e26, eR3⟩ := by
    refine detStep_of (by show (0x80021082 : Word).getLsbD 0 = false; decide) f80021082 fun o => ?_
    rw [exec_op]; rfl
  have es27 : DetStep B img ⟨e26, eR3⟩ ⟨e27, eR4⟩ := by
    refine detStep_of (by show (0x80021084 : Word).getLsbD 0 = false; decide) f80021084 fun o => ?_
    rw [exec_store, interp_store_ram (w := .w) o HAL_27 HIN_27]; rfl
  have ek1 : e1.sameCsr g := (Core.sameCsr_wr _ _ _ _)
  have ek2 : e2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek1
  have ek3 : e3.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek2
  have ek4 : e4.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek3
  have ek5 : e5.sameCsr g := (Core.sameCsr_goto _ _).trans ek4
  have ek6 : e6.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek5
  have ek7 : e7.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek6
  have ek8 : e8.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek7
  have ek9 : e9.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek8
  have ek10 : e10.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek9
  have ek11 : e11.sameCsr g := (Core.sameCsr_goto _ _).trans ek10
  have ek12 : e12.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek11
  have ek13 : e13.sameCsr g := (Core.sameCsr_goto _ _).trans ek12
  have ek14 : e14.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek13
  have ek15 : e15.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek14
  have ek16 : e16.sameCsr g := (Core.sameCsr_goto _ _).trans ek15
  have ek17 : e17.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek16
  have ek18 : e18.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek17
  have ek19 : e19.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek18
  have ek20 : e20.sameCsr g := (Core.sameCsr_goto _ _).trans ek19
  have ek21 : e21.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek20
  have ek22 : e22.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek21
  have ek23 : e23.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek22
  have ek24 : e24.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek23
  have ek25 : e25.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek24
  have ek26 : e26.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek25
  have ek27 : e27.sameCsr g := (Core.sameCsr_goto _ _).trans ek26
  have erun : QRun B img 27 ⟨g, R0⟩ ⟨e27, eR4⟩ :=
    .step hq es1 (.step (Quiet.of_sameCsr ek1 hq) es2 (.step (Quiet.of_sameCsr ek2 hq) es3 (.step (Quiet.of_sameCsr ek3 hq) es4 (.step (Quiet.of_sameCsr ek4 hq) es5 (.step (Quiet.of_sameCsr ek5 hq) es6 (.step (Quiet.of_sameCsr ek6 hq) es7 (.step (Quiet.of_sameCsr ek7 hq) es8 (.step (Quiet.of_sameCsr ek8 hq) es9 (.step (Quiet.of_sameCsr ek9 hq) es10 (.step (Quiet.of_sameCsr ek10 hq) es11 (.step (Quiet.of_sameCsr ek11 hq) es12 (.step (Quiet.of_sameCsr ek12 hq) es13 (.step (Quiet.of_sameCsr ek13 hq) es14 (.step (Quiet.of_sameCsr ek14 hq) es15 (.step (Quiet.of_sameCsr ek15 hq) es16 (.step (Quiet.of_sameCsr ek16 hq) es17 (.step (Quiet.of_sameCsr ek17 hq) es18 (.step (Quiet.of_sameCsr ek18 hq) es19 (.step (Quiet.of_sameCsr ek19 hq) es20 (.step (Quiet.of_sameCsr ek20 hq) es21 (.step (Quiet.of_sameCsr ek21 hq) es22 (.step (Quiet.of_sameCsr ek22 hq) es23 (.step (Quiet.of_sameCsr ek23 hq) es24 (.step (Quiet.of_sameCsr ek24 hq) es25 (.step (Quiet.of_sameCsr ek25 hq) es26 (.single (Quiet.of_sameCsr ek26 hq) es27))))))))))))))))))))))))))
  -- the temporary word and the stored value
  have sp1 : e12.get 6 + 0x00000000#32 = g.get 2 + 0x20#32 + 1#32 := by
    simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; exact or_small _ _ hTa (by decide)
  have src12 : e11.get 14 + 0x00000000#32 = Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 := by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; bv_omega
  -- RAM after each store, at the temporary and away from it
  have T : ∀ i, i < 4 → g.get 2 + 0x20#32 + BitVec.ofNat 32 i = g.get 2 + 0x20#32 + BitVec.ofNat 32 i := fun _ _ => rfl
  have nT : ∀ x, ¬ ((g.get 2 + 0x20#32).toNat ≤ x.toNat ∧ x.toNat < (g.get 2 + 0x20#32).toNat + 4) →
      ∀ i < 4, x ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i := by
    intro x hx i hi e; apply hx; subst e; constructor <;> bv_omega
  have r1 : ∀ x, (∀ i < 4, x ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i) → eR1 x = R0 x := by
    intro x hx; show ramWrite R0 (e4.get 2 + 0x00000020#32) (e4.get 0) .w x = R0 x
    rw [show e4.get 2 = g.get 2 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact ramWrite_w_other _ _ _ _ (fun k hk => hx k hk)
  have sb : ∀ j < 3, ∀ i < 4, Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + BitVec.ofNat 32 j ≠
      g.get 2 + 0x20#32 + BitVec.ofNat 32 i := hsep
  have s0 : eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1) = R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1) :=
    r1 _ (fun i hi => by have := sb 0 (by decide) i hi; simpa using this)
  have s1 : eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32) = R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32) :=
    r1 _ (fun i hi => sb 1 (by decide) i hi)
  have s2 : eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32 + 1) = R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32 + 1) :=
    r1 _ (fun i hi => by rw [show Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32 + 1 =
      Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + BitVec.ofNat 32 2 by bv_omega]; exact sb 2 (by decide) i hi)
  have hR2 : eR2 = ramPut eR1 (g.get 2 + 0x20#32 + 1#32) (eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1)) := by
    show ramWrite eR1 (e12.get 6 + 0x00000000#32) (e12.get 12) .b = _
    rw [sp1, show e12.get 12 = extend .b false (ramRead eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1) .b) by
      simp only [e12, Core.wr_get_self _ (12 : Reg) _ _ (by decide)]; rw [src12], copyByte]
  have hv : e18.get 13 = extend .h true (ramRead eR2 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32) .h) := by
    simp only [e18, Core.wr_get_self _ (13 : Reg) _ _ (by decide)]; rw [a18]
  have hR3 : eR3 = ramWrite eR2 (g.get 2 + 0x20#32 + 2#32)
      (extend .h true (ramRead eR2 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32) .h)) .h := by
    show ramWrite eR2 (e19.get 12 + 0x00000000#32) (e19.get 13) .h = _
    rw [a20, show e19.get 13 = e18.get 13 by simp [e19, Core.wr_get_ne], hv]
  have ne12 : g.get 2 + 0x20#32 + 1#32 ≠ g.get 2 + 0x20#32 + 2#32 := by bv_omega
  have ne13 : g.get 2 + 0x20#32 + 1#32 ≠ g.get 2 + 0x20#32 + 2#32 + 1 := by bv_omega
  have nsrc1 : Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32 ≠ g.get 2 + 0x20#32 + 1#32 := by
    have := sb 1 (by decide) 1 (by decide); simpa using this
  have nsrc2 : Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32 + 1 ≠ g.get 2 + 0x20#32 + 1#32 := by
    have := sb 2 (by decide) 1 (by decide)
    rwa [show Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + BitVec.ofNat 32 2 =
      Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32 + 1 by bv_omega, show BitVec.ofNat 32 1 = 1#32 from rfl] at this
  have hb := ramWrite_h_bytes eR2 (g.get 2 + 0x20#32 + 2#32)
    (extend .h true (ramRead eR2 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32) .h))
  have hh := byte_read_h eR2 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1 + 1#32)
  have tb : ∀ k, 1 ≤ k → k < 4 → byteOf (ramRead eR3 (g.get 2 + 0x20#32) .w) k =
      R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 k) := by
    intro k hk1 hk2
    rw [byte_read_k _ _ _ hk2, hR3]
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
    · rw [hb.2.2 _ (by bv_omega) (by bv_omega), hR2,
        show g.get 2 + 0x20#32 + BitVec.ofNat 32 1 = g.get 2 + 0x20#32 + 1#32 by bv_omega, ramPut_eq]
      exact s0
    · rw [show g.get 2 + 0x20#32 + BitVec.ofNat 32 2 = g.get 2 + 0x20#32 + 2#32 by bv_omega, hb.1,
        byte_sext _ _ (by decide), hh.1, hR2, ramPut_ne _ nsrc1, s1]
      exact congrArg R0 (by bv_omega)
    · rw [show g.get 2 + 0x20#32 + BitVec.ofNat 32 3 = g.get 2 + 0x20#32 + 2#32 + 1 by bv_omega, hb.2.1,
        byte_sext _ _ (by decide), hh.2, hR2, ramPut_ne _ nsrc2, s2]
      exact congrArg R0 (by bv_omega)
  have v26 : e26.get 12 = (ramRead eR3 (g.get 2 + 0x20#32) .w >>> (8 * 1)) ||| (g.get 15 <<< (32 - 8 * 1)) := by
    rw [← bendVal _ _ 1 (by decide)]
    simp [e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5,
      e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, h29, extend]
  have hR4 : eR4 = ramWrite eR3 (g.get 11 + 0xfffffffc#32) (ramRead R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 1) .w) .w := by
    show ramWrite eR3 (e26.get 11 + 0xfffffffc#32) (e26.get 12) .w = _
    rw [show e26.get 11 = g.get 11 by simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], v26]
    refine merge_store_q R0 eR3 _ _ _ _ 1 (by decide) tb (fun j hj => ?_)
    rw [hprev j hj]; exact congrArg R0 (by bv_omega)
  refine ⟨e27, eR4, erun, ⟨rfl, ek27, ⟨eR3, ?_, hR4⟩, ?_⟩⟩
  · intro x hx
    have hn := nT x hx
    have n2 : x ≠ g.get 2 + 0x20#32 + 2#32 := by have := hn 2 (by decide); exact this
    have n3 : x ≠ g.get 2 + 0x20#32 + 2#32 + 1 := by
      have := hn 3 (by decide)
      rwa [show g.get 2 + 0x20#32 + BitVec.ofNat 32 3 = g.get 2 + 0x20#32 + 2#32 + 1 by bv_omega] at this
    have n1 : x ≠ g.get 2 + 0x20#32 + 1#32 := by have := hn 1 (by decide); exact this
    rw [hR3, (ramWrite_h_bytes _ _ _).2.2 _ n2 n3, hR2, ramPut_ne _ n1]
    exact r1 x hn
  · intro r hr
    have h6' : r ≠ 6 := fun e => hr (by subst e; decide)
    have h9 : r ≠ 9 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h30 : r ≠ 30 := fun e => hr (by subst e; decide)
    simp [e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, h6', h9, h12, h13, h14, h30]

/-- o = 2: one halfword into the temporary. -/
theorem bend2 (g : Core) (R0 : Word → BitVec 8) (Lq : Word) (hpc : g.pc = 0x8002103a) (hq : Quiet g)
    (hLq : g.get 30 + g.get 18 = Lq) (h6 : g.get 6 = BitVec.ofNat 32 2) (h29 : g.get 29 = BitVec.ofNat 32 (8 * 2))
    (hprev : ∀ k, k < 2 → byteOf (g.get 15) k = R0 (Lq + BitVec.ofNat 32 k))
    (hL : Lq.toNat % 4 = 0) (hL4 : 4 ≤ Lq.toNat)
    (hsrc : B.inRam (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2) 2 = true)
    (hT : B.inRam (g.get 2 + 0x20#32) 4 = true) (hTa : (g.get 2 + 0x20#32).toNat % 4 = 0)
    (hsep : ∀ j < 2, ∀ i < 4, Lq + 0xfffffffc#32 + BitVec.ofNat 32 2 + BitVec.ofNat 32 j ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i)
    (hD : (g.get 11 + 0xfffffffc#32).toNat % 4 = 0) (hDr : B.inRam (g.get 11 + 0xfffffffc#32) 4 = true) :
    ∃ g' R', QRun B img 24 ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtBT g g' R0 R' Lq 2 := by
  have hTr := (B_ram _ _).mp hT
  let e1 := g.wr 30 (alu .add (g.get 30) (g.get 18)) 0x8002103c
  let e2 := e1.wr 12 (alu .add (e1.get 0) 0x00000000#32) 0x8002103e
  let e3 := e2.wr 14 (alu .add (e2.get 30) (e2.get 6)) 0x80021042
  let e4 := e3.wr 13 (alu .add (e3.get 0) 0x00000004#32) 0x80021044
  let eR1 := ramWrite R0 (e4.get 2 + 0x00000020#32) (e4.get 0) .w
  let e5 := e4.goto 0x80021046
  let e6 := e5.wr 9 (alu .add (e5.get 2) 0x00000020#32) 0x80021048
  let e7 := e6.wr 13 (alu .sub (e6.get 13) (e6.get 6)) 0x8002104c
  let e8 := e7.wr 6 (alu .or (e7.get 9) (e7.get 6)) 0x80021050
  let e9 := e8.wr 9 (alu .and (e8.get 13) 0x00000001#32) 0x80021054
  let e10 := e9.wr 14 (alu .add (e9.get 14) 0xfffffffc#32) 0x80021056
  let e11 := e10.goto 0x80021062
  let e12 := e11.wr 13 (alu .and (e11.get 13) 0x00000002#32) 0x80021064
  let e13 := e12.goto 0x80021066
  let e14 := e13.wr 14 (alu .add (e13.get 14) (e13.get 12)) 0x80021068
  let e15 := e14.wr 13 (extend .h true (ramRead eR1 (e14.get 14 + 0x00000000#32) .h)) 0x8002106c
  let e16 := e15.wr 12 (alu .add (e15.get 12) (e15.get 6)) 0x8002106e
  let eR2 := ramWrite eR1 (e16.get 12 + 0x00000000#32) (e16.get 13) .h
  let e17 := e16.goto 0x80021072
  let e18 := e17.wr 12 (extend .w true (ramRead eR2 (e17.get 2 + 0x00000020#32) .w)) 0x80021074
  let e19 := e18.wr 13 (alu .sub (e18.get 0) (e18.get 29)) 0x80021078
  let e20 := e19.wr 13 (alu .and (e19.get 13) 0x00000018#32) 0x8002107a
  let e21 := e20.wr 13 (alu .sll (e20.get 15) (e20.get 13)) 0x8002107e
  let e22 := e21.wr 12 (alu .srl (e21.get 12) (e21.get 29)) 0x80021082
  let e23 := e22.wr 12 (alu .or (e22.get 12) (e22.get 13)) 0x80021084
  let eR3 := ramWrite eR2 (e23.get 11 + 0xfffffffc#32) (e23.get 12) .w
  let e24 := e23.goto 0x80021088
  have a15 : e14.get 14 + 0x00000000#32 = Lq + 0xfffffffc#32 + BitVec.ofNat 32 2 := by
    simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; bv_omega
  have a17 : e16.get 12 + 0x00000000#32 = g.get 2 + 0x20#32 + 2#32 := by
    simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]
    rw [or_small _ _ hTa (by decide)]
  have HIN_5 : B.inRam (e4.get 2 + 0x00000020#32) 4 = true := by
    rw [show e4.get 2 = g.get 2 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hT
  have HAL_5 : (e4.get 2 + 0x00000020#32).toNat % 4 = 0 := by
    rw [show e4.get 2 = g.get 2 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hTa
  have HBR_11 : taken .eq (e10.get 9) (e10.get 0) = true := by
    rw [show e10.get 9 = 0#32 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], Core.get_zero]; decide
  have HBR_13 : taken .eq (e12.get 13) (e12.get 0) = false := by
    rw [show e12.get 13 = 2#32 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], Core.get_zero]; decide
  have HIN_15 : B.inRam (e14.get 14 + 0x00000000#32) 2 = true := by
    rw [a15]; exact (B_ram _ _).mpr (by have := (B_ram _ _).mp hsrc; constructor <;> bv_omega)
  have HAL_15 : (e14.get 14 + 0x00000000#32).toNat % 2 = 0 := by
    rw [a15]; bv_omega
  have HIN_17 : B.inRam (e16.get 12 + 0x00000000#32) 2 = true := by
    rw [a17]; exact (B_ram _ _).mpr (by constructor <;> bv_omega)
  have HAL_17 : (e16.get 12 + 0x00000000#32).toNat % 2 = 0 := by
    rw [a17]; bv_omega
  have HIN_18 : B.inRam (e17.get 2 + 0x00000020#32) 4 = true := by
    rw [show e17.get 2 = g.get 2 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hT
  have HAL_18 : (e17.get 2 + 0x00000020#32).toNat % 4 = 0 := by
    rw [show e17.get 2 = g.get 2 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hTa
  have HIN_24 : B.inRam (e23.get 11 + 0xfffffffc#32) 4 = true := by
    rw [show e23.get 11 = g.get 11 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hDr
  have HAL_24 : (e23.get 11 + 0xfffffffc#32).toNat % 4 = 0 := by
    rw [show e23.get 11 = g.get 11 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hD
  have es1 : DetStep B img ⟨g, R0⟩ ⟨e1, R0⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8002103a) fun o => ?_
    rw [exec_op, hpc]; rfl
  have es2 : DetStep B img ⟨e1, R0⟩ ⟨e2, R0⟩ := by
    refine detStep_of (by show (0x8002103c : Word).getLsbD 0 = false; decide) f8002103c fun o => ?_
    rw [exec_opimm]; rfl
  have es3 : DetStep B img ⟨e2, R0⟩ ⟨e3, R0⟩ := by
    refine detStep_of (by show (0x8002103e : Word).getLsbD 0 = false; decide) f8002103e fun o => ?_
    rw [exec_op]; rfl
  have es4 : DetStep B img ⟨e3, R0⟩ ⟨e4, R0⟩ := by
    refine detStep_of (by show (0x80021042 : Word).getLsbD 0 = false; decide) f80021042 fun o => ?_
    rw [exec_opimm]; rfl
  have es5 : DetStep B img ⟨e4, R0⟩ ⟨e5, eR1⟩ := by
    refine detStep_of (by show (0x80021044 : Word).getLsbD 0 = false; decide) f80021044 fun o => ?_
    rw [exec_store, interp_store_ram (w := .w) o HAL_5 HIN_5]; rfl
  have es6 : DetStep B img ⟨e5, eR1⟩ ⟨e6, eR1⟩ := by
    refine detStep_of (by show (0x80021046 : Word).getLsbD 0 = false; decide) f80021046 fun o => ?_
    rw [exec_opimm]; rfl
  have es7 : DetStep B img ⟨e6, eR1⟩ ⟨e7, eR1⟩ := by
    refine detStep_of (by show (0x80021048 : Word).getLsbD 0 = false; decide) f80021048 fun o => ?_
    rw [exec_op]; rfl
  have es8 : DetStep B img ⟨e7, eR1⟩ ⟨e8, eR1⟩ := by
    refine detStep_of (by show (0x8002104c : Word).getLsbD 0 = false; decide) f8002104c fun o => ?_
    rw [exec_op]; rfl
  have es9 : DetStep B img ⟨e8, eR1⟩ ⟨e9, eR1⟩ := by
    refine detStep_of (by show (0x80021050 : Word).getLsbD 0 = false; decide) f80021050 fun o => ?_
    rw [exec_opimm]; rfl
  have es10 : DetStep B img ⟨e9, eR1⟩ ⟨e10, eR1⟩ := by
    refine detStep_of (by show (0x80021054 : Word).getLsbD 0 = false; decide) f80021054 fun o => ?_
    rw [exec_opimm]; rfl
  have es11 : DetStep B img ⟨e10, eR1⟩ ⟨e11, eR1⟩ := by
    refine detStep_of (by show (0x80021056 : Word).getLsbD 0 = false; decide) f80021056 fun o => ?_
    rw [exec_branch, HBR_11, if_pos rfl, show e10.pc + 0xc#32 = 0x80021062 by rw [show e10.pc = 0x80021056 from rfl]; decide, jump_ok _ _ (by decide)]; rfl
  have es12 : DetStep B img ⟨e11, eR1⟩ ⟨e12, eR1⟩ := by
    refine detStep_of (by show (0x80021062 : Word).getLsbD 0 = false; decide) f80021062 fun o => ?_
    rw [exec_opimm]; rfl
  have es13 : DetStep B img ⟨e12, eR1⟩ ⟨e13, eR1⟩ := by
    refine detStep_of (by show (0x80021064 : Word).getLsbD 0 = false; decide) f80021064 fun o => ?_
    rw [exec_branch, HBR_13]; rfl
  have es14 : DetStep B img ⟨e13, eR1⟩ ⟨e14, eR1⟩ := by
    refine detStep_of (by show (0x80021066 : Word).getLsbD 0 = false; decide) f80021066 fun o => ?_
    rw [exec_op]; rfl
  have es15 : DetStep B img ⟨e14, eR1⟩ ⟨e15, eR1⟩ := by
    refine detStep_of (by show (0x80021068 : Word).getLsbD 0 = false; decide) f80021068 fun o => ?_
    rw [exec_load, interp_load_ram (w := .h) o HAL_15 HIN_15]; rfl
  have es16 : DetStep B img ⟨e15, eR1⟩ ⟨e16, eR1⟩ := by
    refine detStep_of (by show (0x8002106c : Word).getLsbD 0 = false; decide) f8002106c fun o => ?_
    rw [exec_op]; rfl
  have es17 : DetStep B img ⟨e16, eR1⟩ ⟨e17, eR2⟩ := by
    refine detStep_of (by show (0x8002106e : Word).getLsbD 0 = false; decide) f8002106e fun o => ?_
    rw [exec_store, interp_store_ram (w := .h) o HAL_17 HIN_17]; rfl
  have es18 : DetStep B img ⟨e17, eR2⟩ ⟨e18, eR2⟩ := by
    refine detStep_of (by show (0x80021072 : Word).getLsbD 0 = false; decide) f80021072 fun o => ?_
    rw [exec_load, interp_load_ram (w := .w) o HAL_18 HIN_18]; rfl
  have es19 : DetStep B img ⟨e18, eR2⟩ ⟨e19, eR2⟩ := by
    refine detStep_of (by show (0x80021074 : Word).getLsbD 0 = false; decide) f80021074 fun o => ?_
    rw [exec_op]; rfl
  have es20 : DetStep B img ⟨e19, eR2⟩ ⟨e20, eR2⟩ := by
    refine detStep_of (by show (0x80021078 : Word).getLsbD 0 = false; decide) f80021078 fun o => ?_
    rw [exec_opimm]; rfl
  have es21 : DetStep B img ⟨e20, eR2⟩ ⟨e21, eR2⟩ := by
    refine detStep_of (by show (0x8002107a : Word).getLsbD 0 = false; decide) f8002107a fun o => ?_
    rw [exec_op]; rfl
  have es22 : DetStep B img ⟨e21, eR2⟩ ⟨e22, eR2⟩ := by
    refine detStep_of (by show (0x8002107e : Word).getLsbD 0 = false; decide) f8002107e fun o => ?_
    rw [exec_op]; rfl
  have es23 : DetStep B img ⟨e22, eR2⟩ ⟨e23, eR2⟩ := by
    refine detStep_of (by show (0x80021082 : Word).getLsbD 0 = false; decide) f80021082 fun o => ?_
    rw [exec_op]; rfl
  have es24 : DetStep B img ⟨e23, eR2⟩ ⟨e24, eR3⟩ := by
    refine detStep_of (by show (0x80021084 : Word).getLsbD 0 = false; decide) f80021084 fun o => ?_
    rw [exec_store, interp_store_ram (w := .w) o HAL_24 HIN_24]; rfl
  have ek1 : e1.sameCsr g := (Core.sameCsr_wr _ _ _ _)
  have ek2 : e2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek1
  have ek3 : e3.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek2
  have ek4 : e4.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek3
  have ek5 : e5.sameCsr g := (Core.sameCsr_goto _ _).trans ek4
  have ek6 : e6.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek5
  have ek7 : e7.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek6
  have ek8 : e8.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek7
  have ek9 : e9.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek8
  have ek10 : e10.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek9
  have ek11 : e11.sameCsr g := (Core.sameCsr_goto _ _).trans ek10
  have ek12 : e12.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek11
  have ek13 : e13.sameCsr g := (Core.sameCsr_goto _ _).trans ek12
  have ek14 : e14.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek13
  have ek15 : e15.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek14
  have ek16 : e16.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek15
  have ek17 : e17.sameCsr g := (Core.sameCsr_goto _ _).trans ek16
  have ek18 : e18.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek17
  have ek19 : e19.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek18
  have ek20 : e20.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek19
  have ek21 : e21.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek20
  have ek22 : e22.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek21
  have ek23 : e23.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek22
  have ek24 : e24.sameCsr g := (Core.sameCsr_goto _ _).trans ek23
  have erun : QRun B img 24 ⟨g, R0⟩ ⟨e24, eR3⟩ :=
    .step hq es1 (.step (Quiet.of_sameCsr ek1 hq) es2 (.step (Quiet.of_sameCsr ek2 hq) es3 (.step (Quiet.of_sameCsr ek3 hq) es4 (.step (Quiet.of_sameCsr ek4 hq) es5 (.step (Quiet.of_sameCsr ek5 hq) es6 (.step (Quiet.of_sameCsr ek6 hq) es7 (.step (Quiet.of_sameCsr ek7 hq) es8 (.step (Quiet.of_sameCsr ek8 hq) es9 (.step (Quiet.of_sameCsr ek9 hq) es10 (.step (Quiet.of_sameCsr ek10 hq) es11 (.step (Quiet.of_sameCsr ek11 hq) es12 (.step (Quiet.of_sameCsr ek12 hq) es13 (.step (Quiet.of_sameCsr ek13 hq) es14 (.step (Quiet.of_sameCsr ek14 hq) es15 (.step (Quiet.of_sameCsr ek15 hq) es16 (.step (Quiet.of_sameCsr ek16 hq) es17 (.step (Quiet.of_sameCsr ek17 hq) es18 (.step (Quiet.of_sameCsr ek18 hq) es19 (.step (Quiet.of_sameCsr ek19 hq) es20 (.step (Quiet.of_sameCsr ek20 hq) es21 (.step (Quiet.of_sameCsr ek21 hq) es22 (.step (Quiet.of_sameCsr ek22 hq) es23 (.single (Quiet.of_sameCsr ek23 hq) es24)))))))))))))))))))))))
  have nT : ∀ x, ¬ ((g.get 2 + 0x20#32).toNat ≤ x.toNat ∧ x.toNat < (g.get 2 + 0x20#32).toNat + 4) →
      ∀ i < 4, x ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i := by
    intro x hx i hi e; apply hx; subst e; constructor <;> bv_omega
  have r1 : ∀ x, (∀ i < 4, x ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i) → eR1 x = R0 x := by
    intro x hx; show ramWrite R0 (e4.get 2 + 0x00000020#32) (e4.get 0) .w x = R0 x
    rw [show e4.get 2 = g.get 2 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact ramWrite_w_other _ _ _ _ (fun k hk => hx k hk)
  have s0 : eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2) = R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2) :=
    r1 _ (fun i hi => by have := hsep 0 (by decide) i hi; simpa using this)
  have s1 : eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2 + 1) = R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2 + 1) :=
    r1 _ (fun i hi => hsep 1 (by decide) i hi)
  have hv : e16.get 13 = extend .h true (ramRead eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2) .h) := by
    simp only [e16, Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 12 by decide), e15,
      Core.wr_get_self _ (13 : Reg) _ _ (by decide)]; rw [a15]
  have hR2 : eR2 = ramWrite eR1 (g.get 2 + 0x20#32 + 2#32)
      (extend .h true (ramRead eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2) .h)) .h := by
    show ramWrite eR1 (e16.get 12 + 0x00000000#32) (e16.get 13) .h = _
    rw [a17, hv]
  have hb := ramWrite_h_bytes eR1 (g.get 2 + 0x20#32 + 2#32)
    (extend .h true (ramRead eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2) .h))
  have hh := byte_read_h eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2)
  have tb : ∀ k, 2 ≤ k → k < 4 → byteOf (ramRead eR2 (g.get 2 + 0x20#32) .w) k =
      R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 k) := by
    intro k hk1 hk2
    rw [byte_read_k _ _ _ hk2, hR2]
    rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
    · rw [show g.get 2 + 0x20#32 + BitVec.ofNat 32 2 = g.get 2 + 0x20#32 + 2#32 by bv_omega, hb.1,
        byte_sext _ _ (by decide), hh.1, s0]
    · rw [show g.get 2 + 0x20#32 + BitVec.ofNat 32 3 = g.get 2 + 0x20#32 + 2#32 + 1 by bv_omega, hb.2.1,
        byte_sext _ _ (by decide), hh.2, s1]
      exact congrArg R0 (by bv_omega)
  have v23 : e23.get 12 = (ramRead eR2 (g.get 2 + 0x20#32) .w >>> (8 * 2)) ||| (g.get 15 <<< (32 - 8 * 2)) := by
    rw [← bendVal _ _ 2 (by decide)]
    simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, h29, extend]
  have hR3 : eR3 = ramWrite eR2 (g.get 11 + 0xfffffffc#32) (ramRead R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 2) .w) .w := by
    show ramWrite eR2 (e23.get 11 + 0xfffffffc#32) (e23.get 12) .w = _
    rw [show e23.get 11 = g.get 11 by simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], v23]
    refine merge_store_q R0 eR2 _ _ _ _ 2 (by decide) tb (fun j hj => ?_)
    rw [hprev j hj]; exact congrArg R0 (by bv_omega)
  refine ⟨e24, eR3, erun, ⟨rfl, ek24, ⟨eR2, ?_, hR3⟩, ?_⟩⟩
  · intro x hx
    have hn := nT x hx
    have n2 : x ≠ g.get 2 + 0x20#32 + 2#32 := by have := hn 2 (by decide); exact this
    have n3 : x ≠ g.get 2 + 0x20#32 + 2#32 + 1 := by
      have := hn 3 (by decide)
      rwa [show g.get 2 + 0x20#32 + BitVec.ofNat 32 3 = g.get 2 + 0x20#32 + 2#32 + 1 by bv_omega] at this
    rw [hR2, (ramWrite_h_bytes _ _ _).2.2 _ n2 n3]
    exact r1 x hn
  · intro r hr
    have h6' : r ≠ 6 := fun e => hr (by subst e; decide)
    have h9 : r ≠ 9 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h30 : r ≠ 30 := fun e => hr (by subst e; decide)
    simp [e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, h6', h9, h12, h13, h14, h30]

/-- o = 3: one byte into the temporary. -/
theorem bend3 (g : Core) (R0 : Word → BitVec 8) (Lq : Word) (hpc : g.pc = 0x8002103a) (hq : Quiet g)
    (hLq : g.get 30 + g.get 18 = Lq) (h6 : g.get 6 = BitVec.ofNat 32 3) (h29 : g.get 29 = BitVec.ofNat 32 (8 * 3))
    (hprev : ∀ k, k < 3 → byteOf (g.get 15) k = R0 (Lq + BitVec.ofNat 32 k))
    (hL : Lq.toNat % 4 = 0) (hL4 : 4 ≤ Lq.toNat)
    (hsrc : B.inRam (Lq + 0xfffffffc#32 + BitVec.ofNat 32 3) 1 = true)
    (hT : B.inRam (g.get 2 + 0x20#32) 4 = true) (hTa : (g.get 2 + 0x20#32).toNat % 4 = 0)
    (hsep : ∀ j < 1, ∀ i < 4, Lq + 0xfffffffc#32 + BitVec.ofNat 32 3 + BitVec.ofNat 32 j ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i)
    (hD : (g.get 11 + 0xfffffffc#32).toNat % 4 = 0) (hDr : B.inRam (g.get 11 + 0xfffffffc#32) 4 = true) :
    ∃ g' R', QRun B img 23 ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtBT g g' R0 R' Lq 3 := by
  have hTr := (B_ram _ _).mp hT
  let e1 := g.wr 30 (alu .add (g.get 30) (g.get 18)) 0x8002103c
  let e2 := e1.wr 12 (alu .add (e1.get 0) 0x00000000#32) 0x8002103e
  let e3 := e2.wr 14 (alu .add (e2.get 30) (e2.get 6)) 0x80021042
  let e4 := e3.wr 13 (alu .add (e3.get 0) 0x00000004#32) 0x80021044
  let eR1 := ramWrite R0 (e4.get 2 + 0x00000020#32) (e4.get 0) .w
  let e5 := e4.goto 0x80021046
  let e6 := e5.wr 9 (alu .add (e5.get 2) 0x00000020#32) 0x80021048
  let e7 := e6.wr 13 (alu .sub (e6.get 13) (e6.get 6)) 0x8002104c
  let e8 := e7.wr 6 (alu .or (e7.get 9) (e7.get 6)) 0x80021050
  let e9 := e8.wr 9 (alu .and (e8.get 13) 0x00000001#32) 0x80021054
  let e10 := e9.wr 14 (alu .add (e9.get 14) 0xfffffffc#32) 0x80021056
  let e11 := e10.goto 0x80021058
  let e12 := e11.wr 12 (extend .b false (ramRead eR1 (e11.get 14 + 0x00000000#32) .b)) 0x8002105c
  let eR2 := ramWrite eR1 (e12.get 6 + 0x00000000#32) (e12.get 12) .b
  let e13 := e12.goto 0x80021060
  let e14 := e13.wr 12 (alu .add (e13.get 0) 0x00000001#32) 0x80021062
  let e15 := e14.wr 13 (alu .and (e14.get 13) 0x00000002#32) 0x80021064
  let e16 := e15.goto 0x80021072
  let e17 := e16.wr 12 (extend .w true (ramRead eR2 (e16.get 2 + 0x00000020#32) .w)) 0x80021074
  let e18 := e17.wr 13 (alu .sub (e17.get 0) (e17.get 29)) 0x80021078
  let e19 := e18.wr 13 (alu .and (e18.get 13) 0x00000018#32) 0x8002107a
  let e20 := e19.wr 13 (alu .sll (e19.get 15) (e19.get 13)) 0x8002107e
  let e21 := e20.wr 12 (alu .srl (e20.get 12) (e20.get 29)) 0x80021082
  let e22 := e21.wr 12 (alu .or (e21.get 12) (e21.get 13)) 0x80021084
  let eR3 := ramWrite eR2 (e22.get 11 + 0xfffffffc#32) (e22.get 12) .w
  let e23 := e22.goto 0x80021088
  have sp3 : e12.get 6 + 0x00000000#32 = g.get 2 + 0x20#32 + 3#32 := by
    simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; exact or_small _ _ hTa (by decide)
  have src12 : e11.get 14 + 0x00000000#32 = Lq + 0xfffffffc#32 + BitVec.ofNat 32 3 := by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]; bv_omega
  have HIN_5 : B.inRam (e4.get 2 + 0x00000020#32) 4 = true := by
    rw [show e4.get 2 = g.get 2 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hT
  have HAL_5 : (e4.get 2 + 0x00000020#32).toNat % 4 = 0 := by
    rw [show e4.get 2 = g.get 2 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hTa
  have HBR_11 : taken .eq (e10.get 9) (e10.get 0) = false := by
    rw [show e10.get 9 = 1#32 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], Core.get_zero]; decide
  have HIN_12 : B.inRam (e11.get 14 + 0x00000000#32) 1 = true := by
    rw [src12]; exact (B_ram _ _).mpr (by have := (B_ram _ _).mp hsrc; omega)
  have HIN_13 : B.inRam (e12.get 6 + 0x00000000#32) 1 = true := by
    rw [sp3]; exact (B_ram _ _).mpr (by constructor <;> bv_omega)
  have HBR_16 : taken .eq (e15.get 13) (e15.get 0) = true := by
    rw [show e15.get 13 = 0#32 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], Core.get_zero]; decide
  have HIN_17 : B.inRam (e16.get 2 + 0x00000020#32) 4 = true := by
    rw [show e16.get 2 = g.get 2 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hT
  have HAL_17 : (e16.get 2 + 0x00000020#32).toNat % 4 = 0 := by
    rw [show e16.get 2 = g.get 2 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hTa
  have HIN_23 : B.inRam (e22.get 11 + 0xfffffffc#32) 4 = true := by
    rw [show e22.get 11 = g.get 11 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hDr
  have HAL_23 : (e22.get 11 + 0xfffffffc#32).toNat % 4 = 0 := by
    rw [show e22.get 11 = g.get 11 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact hD
  have es1 : DetStep B img ⟨g, R0⟩ ⟨e1, R0⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8002103a) fun o => ?_
    rw [exec_op, hpc]; rfl
  have es2 : DetStep B img ⟨e1, R0⟩ ⟨e2, R0⟩ := by
    refine detStep_of (by show (0x8002103c : Word).getLsbD 0 = false; decide) f8002103c fun o => ?_
    rw [exec_opimm]; rfl
  have es3 : DetStep B img ⟨e2, R0⟩ ⟨e3, R0⟩ := by
    refine detStep_of (by show (0x8002103e : Word).getLsbD 0 = false; decide) f8002103e fun o => ?_
    rw [exec_op]; rfl
  have es4 : DetStep B img ⟨e3, R0⟩ ⟨e4, R0⟩ := by
    refine detStep_of (by show (0x80021042 : Word).getLsbD 0 = false; decide) f80021042 fun o => ?_
    rw [exec_opimm]; rfl
  have es5 : DetStep B img ⟨e4, R0⟩ ⟨e5, eR1⟩ := by
    refine detStep_of (by show (0x80021044 : Word).getLsbD 0 = false; decide) f80021044 fun o => ?_
    rw [exec_store, interp_store_ram (w := .w) o HAL_5 HIN_5]; rfl
  have es6 : DetStep B img ⟨e5, eR1⟩ ⟨e6, eR1⟩ := by
    refine detStep_of (by show (0x80021046 : Word).getLsbD 0 = false; decide) f80021046 fun o => ?_
    rw [exec_opimm]; rfl
  have es7 : DetStep B img ⟨e6, eR1⟩ ⟨e7, eR1⟩ := by
    refine detStep_of (by show (0x80021048 : Word).getLsbD 0 = false; decide) f80021048 fun o => ?_
    rw [exec_op]; rfl
  have es8 : DetStep B img ⟨e7, eR1⟩ ⟨e8, eR1⟩ := by
    refine detStep_of (by show (0x8002104c : Word).getLsbD 0 = false; decide) f8002104c fun o => ?_
    rw [exec_op]; rfl
  have es9 : DetStep B img ⟨e8, eR1⟩ ⟨e9, eR1⟩ := by
    refine detStep_of (by show (0x80021050 : Word).getLsbD 0 = false; decide) f80021050 fun o => ?_
    rw [exec_opimm]; rfl
  have es10 : DetStep B img ⟨e9, eR1⟩ ⟨e10, eR1⟩ := by
    refine detStep_of (by show (0x80021054 : Word).getLsbD 0 = false; decide) f80021054 fun o => ?_
    rw [exec_opimm]; rfl
  have es11 : DetStep B img ⟨e10, eR1⟩ ⟨e11, eR1⟩ := by
    refine detStep_of (by show (0x80021056 : Word).getLsbD 0 = false; decide) f80021056 fun o => ?_
    rw [exec_branch, HBR_11]; rfl
  have es12 : DetStep B img ⟨e11, eR1⟩ ⟨e12, eR1⟩ := by
    refine detStep_of (by show (0x80021058 : Word).getLsbD 0 = false; decide) f80021058 fun o => ?_
    rw [exec_load, interp_load_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_12]; rfl
  have es13 : DetStep B img ⟨e12, eR1⟩ ⟨e13, eR2⟩ := by
    refine detStep_of (by show (0x8002105c : Word).getLsbD 0 = false; decide) f8002105c fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_13]; rfl
  have es14 : DetStep B img ⟨e13, eR2⟩ ⟨e14, eR2⟩ := by
    refine detStep_of (by show (0x80021060 : Word).getLsbD 0 = false; decide) f80021060 fun o => ?_
    rw [exec_opimm]; rfl
  have es15 : DetStep B img ⟨e14, eR2⟩ ⟨e15, eR2⟩ := by
    refine detStep_of (by show (0x80021062 : Word).getLsbD 0 = false; decide) f80021062 fun o => ?_
    rw [exec_opimm]; rfl
  have es16 : DetStep B img ⟨e15, eR2⟩ ⟨e16, eR2⟩ := by
    refine detStep_of (by show (0x80021064 : Word).getLsbD 0 = false; decide) f80021064 fun o => ?_
    rw [exec_branch, HBR_16, if_pos rfl, show e15.pc + 0xe#32 = 0x80021072 by rw [show e15.pc = 0x80021064 from rfl]; decide, jump_ok _ _ (by decide)]; rfl
  have es17 : DetStep B img ⟨e16, eR2⟩ ⟨e17, eR2⟩ := by
    refine detStep_of (by show (0x80021072 : Word).getLsbD 0 = false; decide) f80021072 fun o => ?_
    rw [exec_load, interp_load_ram (w := .w) o HAL_17 HIN_17]; rfl
  have es18 : DetStep B img ⟨e17, eR2⟩ ⟨e18, eR2⟩ := by
    refine detStep_of (by show (0x80021074 : Word).getLsbD 0 = false; decide) f80021074 fun o => ?_
    rw [exec_op]; rfl
  have es19 : DetStep B img ⟨e18, eR2⟩ ⟨e19, eR2⟩ := by
    refine detStep_of (by show (0x80021078 : Word).getLsbD 0 = false; decide) f80021078 fun o => ?_
    rw [exec_opimm]; rfl
  have es20 : DetStep B img ⟨e19, eR2⟩ ⟨e20, eR2⟩ := by
    refine detStep_of (by show (0x8002107a : Word).getLsbD 0 = false; decide) f8002107a fun o => ?_
    rw [exec_op]; rfl
  have es21 : DetStep B img ⟨e20, eR2⟩ ⟨e21, eR2⟩ := by
    refine detStep_of (by show (0x8002107e : Word).getLsbD 0 = false; decide) f8002107e fun o => ?_
    rw [exec_op]; rfl
  have es22 : DetStep B img ⟨e21, eR2⟩ ⟨e22, eR2⟩ := by
    refine detStep_of (by show (0x80021082 : Word).getLsbD 0 = false; decide) f80021082 fun o => ?_
    rw [exec_op]; rfl
  have es23 : DetStep B img ⟨e22, eR2⟩ ⟨e23, eR3⟩ := by
    refine detStep_of (by show (0x80021084 : Word).getLsbD 0 = false; decide) f80021084 fun o => ?_
    rw [exec_store, interp_store_ram (w := .w) o HAL_23 HIN_23]; rfl
  have ek1 : e1.sameCsr g := (Core.sameCsr_wr _ _ _ _)
  have ek2 : e2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek1
  have ek3 : e3.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek2
  have ek4 : e4.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek3
  have ek5 : e5.sameCsr g := (Core.sameCsr_goto _ _).trans ek4
  have ek6 : e6.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek5
  have ek7 : e7.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek6
  have ek8 : e8.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek7
  have ek9 : e9.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek8
  have ek10 : e10.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek9
  have ek11 : e11.sameCsr g := (Core.sameCsr_goto _ _).trans ek10
  have ek12 : e12.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek11
  have ek13 : e13.sameCsr g := (Core.sameCsr_goto _ _).trans ek12
  have ek14 : e14.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek13
  have ek15 : e15.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek14
  have ek16 : e16.sameCsr g := (Core.sameCsr_goto _ _).trans ek15
  have ek17 : e17.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek16
  have ek18 : e18.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek17
  have ek19 : e19.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek18
  have ek20 : e20.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek19
  have ek21 : e21.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek20
  have ek22 : e22.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans ek21
  have ek23 : e23.sameCsr g := (Core.sameCsr_goto _ _).trans ek22
  have erun : QRun B img 23 ⟨g, R0⟩ ⟨e23, eR3⟩ :=
    .step hq es1 (.step (Quiet.of_sameCsr ek1 hq) es2 (.step (Quiet.of_sameCsr ek2 hq) es3 (.step (Quiet.of_sameCsr ek3 hq) es4 (.step (Quiet.of_sameCsr ek4 hq) es5 (.step (Quiet.of_sameCsr ek5 hq) es6 (.step (Quiet.of_sameCsr ek6 hq) es7 (.step (Quiet.of_sameCsr ek7 hq) es8 (.step (Quiet.of_sameCsr ek8 hq) es9 (.step (Quiet.of_sameCsr ek9 hq) es10 (.step (Quiet.of_sameCsr ek10 hq) es11 (.step (Quiet.of_sameCsr ek11 hq) es12 (.step (Quiet.of_sameCsr ek12 hq) es13 (.step (Quiet.of_sameCsr ek13 hq) es14 (.step (Quiet.of_sameCsr ek14 hq) es15 (.step (Quiet.of_sameCsr ek15 hq) es16 (.step (Quiet.of_sameCsr ek16 hq) es17 (.step (Quiet.of_sameCsr ek17 hq) es18 (.step (Quiet.of_sameCsr ek18 hq) es19 (.step (Quiet.of_sameCsr ek19 hq) es20 (.step (Quiet.of_sameCsr ek20 hq) es21 (.step (Quiet.of_sameCsr ek21 hq) es22 (.single (Quiet.of_sameCsr ek22 hq) es23))))))))))))))))))))))
  have nT : ∀ x, ¬ ((g.get 2 + 0x20#32).toNat ≤ x.toNat ∧ x.toNat < (g.get 2 + 0x20#32).toNat + 4) →
      ∀ i < 4, x ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i := by
    intro x hx i hi e; apply hx; subst e; constructor <;> bv_omega
  have r1 : ∀ x, (∀ i < 4, x ≠ g.get 2 + 0x20#32 + BitVec.ofNat 32 i) → eR1 x = R0 x := by
    intro x hx; show ramWrite R0 (e4.get 2 + 0x00000020#32) (e4.get 0) .w x = R0 x
    rw [show e4.get 2 = g.get 2 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq]]; exact ramWrite_w_other _ _ _ _ (fun k hk => hx k hk)
  have s0 : eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 3) = R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 3) :=
    r1 _ (fun i hi => by have := hsep 0 (by decide) i hi; simpa using this)
  have hR2 : eR2 = ramPut eR1 (g.get 2 + 0x20#32 + 3#32) (eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 3)) := by
    show ramWrite eR1 (e12.get 6 + 0x00000000#32) (e12.get 12) .b = _
    rw [sp3, show e12.get 12 = extend .b false (ramRead eR1 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 3) .b) by
      simp only [e12, Core.wr_get_self _ (12 : Reg) _ _ (by decide)]; rw [src12], copyByte]
  have tb : ∀ k, 3 ≤ k → k < 4 → byteOf (ramRead eR2 (g.get 2 + 0x20#32) .w) k =
      R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 k) := by
    intro k hk1 hk2
    have hk : k = 3 := by omega
    subst hk
    rw [byte_read_k _ _ _ hk2, hR2, show g.get 2 + 0x20#32 + BitVec.ofNat 32 3 = g.get 2 + 0x20#32 + 3#32 by bv_omega,
      ramPut_eq]
    exact s0
  have v22 : e22.get 12 = (ramRead eR2 (g.get 2 + 0x20#32) .w >>> (8 * 3)) ||| (g.get 15 <<< (32 - 8 * 3)) := by
    rw [← bendVal _ _ 3 (by decide)]
    simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, h29, extend]
  have hR3 : eR3 = ramWrite eR2 (g.get 11 + 0xfffffffc#32) (ramRead R0 (Lq + 0xfffffffc#32 + BitVec.ofNat 32 3) .w) .w := by
    show ramWrite eR2 (e22.get 11 + 0xfffffffc#32) (e22.get 12) .w = _
    rw [show e22.get 11 = g.get 11 by simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu, h6, hLq], v22]
    refine merge_store_q R0 eR2 _ _ _ _ 3 (by decide) tb (fun j hj => ?_)
    rw [hprev j hj]; exact congrArg R0 (by bv_omega)
  refine ⟨e23, eR3, erun, ⟨rfl, ek23, ⟨eR2, ?_, hR3⟩, ?_⟩⟩
  · intro x hx
    have hn := nT x hx
    have n3 : x ≠ g.get 2 + 0x20#32 + 3#32 := by have := hn 3 (by decide); exact this
    rw [hR2, ramPut_ne _ n3]
    exact r1 x hn
  · intro r hr
    have h6' : r ≠ 6 := fun e => hr (by subst e; decide)
    have h9 : r ≠ 9 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h30 : r ≠ 30 := fun e => hr (by subst e; decide)
    simp [e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, h6', h9, h12, h13, h14, h30]

end E5R.Rmk
