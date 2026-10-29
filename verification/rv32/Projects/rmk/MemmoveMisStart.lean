/-
  memmove's misaligned forward path, the block before the shift/merge
  loop (pinned RMK image): the first source word is built in the stack
  temporary at sp+0x14 (zeroed, then the 4-o source bytes copied by byte
  and/or halfword), loaded into a5, then t3 := 8·o, a1 := src - o
  (aligned), a2 := t5 + 4, a2 := (-t3) & 0x18; ends at the loop head
  0x80020f2e. Three instruction sequences, one per misalignment o.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.MemmoveMisLoop

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

theorem sext_low (v : Word) : extend .h true v &&& 0xffff#32 = v &&& 0xffff#32 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [extend, BitVec.getElem_and]
  by_cases h : i < 16
  · have k : (0xffff#32 : Word)[i] = true := by
      revert i; decide
    simp [k, BitVec.getElem_signExtend, h]
    exact BitVec.getLsbD_eq_getElem hi
  · have k : (0xffff#32 : Word)[i] = false := by
      revert h hi; revert i; decide
    simp [k]

theorem byte_low (x : Word) (k : Nat) (hk : k < 2) : byteOf x k = byteOf (x &&& 0xffff#32) k := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf, BitVec.toNat_ofNat, BitVec.toNat_and]
  rw [show (65535 % 2 ^ 32 : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp <;> omega

theorem byte_sext (v : Word) (k : Nat) (hk : k < 2) : byteOf (extend .h true v) k = byteOf v k := by
  rw [byte_low _ k hk, sext_low, ← byte_low _ k hk]

/-- What the start block establishes, at the loop head 0x80020f2e. -/
structure AtLoop (c g : Core) (R R' : Word → BitVec 8) (o : Nat) : Prop where
  pc : g.pc = 0x80020f2e
  csr : g.sameCsr c
  t3 : g.get 28 = BitVec.ofNat 32 (8 * o)
  a2 : g.get 12 = (0 - BitVec.ofNat 32 (8 * o)) &&& 0x18#32
  a1 : g.get 11 = c.get 5 - BitVec.ofNat 32 o
  prev : ∀ k, o ≤ k → k < 4 → byteOf (g.get 15) k = R' (c.get 5 - BitVec.ofNat 32 o + BitVec.ofNat 32 k)
  ram : ∀ x, ¬ ((c.get 2 + 0x14#32).toNat ≤ x.toNat ∧ x.toNat < (c.get 2 + 0x14#32).toNat + 4) → R' x = R x
  frame : ∀ r : Reg, r.val ∉ [11, 12, 14, 15, 28] → g.get r = c.get r

theorem or_small (x y : Word) (hx : x.toNat % 4 = 0) (hy : y.toNat < 4) : x ||| y = x + y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_add]
  have hxl := x.isLt
  have e : x.toNat = 2 ^ 2 * (x.toNat / 4) := by omega
  rw [e, ← Nat.two_pow_add_eq_or_of_lt (by simpa using hy)]
  omega

/-- Misalignment 3: one source byte into the temporary. -/
theorem start3 (c : Core) (R : Word → BitVec 8) (hpc : c.pc = 0x80020e64) (hq : Quiet c)
    (h6 : c.get 6 = BitVec.ofNat 32 3) (hsr : B.inRam (c.get 5) 1 = true)
    (hT : (c.get 2 + 0x14#32).toNat % 4 = 0) (hTr : B.inRam (c.get 2 + 0x14#32) 4 = true)
    (hsep : (c.get 5).toNat < (c.get 2 + 0x14#32).toNat ∨ (c.get 2 + 0x14#32).toNat + 4 ≤ (c.get 5).toNat)
    (hlp : (c.get 30 + 0x4#32).ult (c.get 13) = true) :
    ∃ g R', QRun B img 20 ⟨c, R⟩ ⟨g, R'⟩ ∧ AtLoop c g R R' 3 := by
  let c1 := c.wr 11 (alu .add (c.get 0) 0x0#32) 0x80020e66
  let c2 := c1.wr 12 (alu .add (c1.get 0) 0x4#32) 0x80020e68
  let R1 := ramWrite R (c2.get 2 + 0x14#32) (c2.get 0) .w
  let c3 := c2.goto 0x80020e6a
  let c4 := c3.wr 14 (alu .sub (c3.get 12) (c3.get 6)) 0x80020e6e
  let c5 := c4.wr 12 (alu .add (c4.get 2) 0x14#32) 0x80020e70
  let c6 := c5.wr 15 (alu .and (c5.get 14) 0x1#32) 0x80020e74
  let c7 := c6.wr 12 (alu .or (c6.get 12) (c6.get 6)) 0x80020e78
  let c8 := c7.goto 0x80020efa
  let c9 := c8.wr 11 (extend .b false (ramRead R1 (c8.get 5 + 0x0#32) .b)) 0x80020efe
  let R2 := ramWrite R1 (c9.get 12 + 0x0#32) (c9.get 11) .b
  let c10 := c9.goto 0x80020f02
  let c11 := c10.wr 11 (alu .add (c10.get 0) 0x1#32) 0x80020f04
  let c12 := c11.wr 14 (alu .and (c11.get 14) 0x2#32) 0x80020f06
  let c13 := c12.goto 0x80020e7e
  let c14 := c13.wr 15 (extend .w true (ramRead R2 (c13.get 2 + 0x14#32) .w)) 0x80020e80
  let c15 := c14.wr 28 (alu .sll (c14.get 6) 0x3#32) 0x80020e84
  let c16 := c15.wr 12 (alu .add (c15.get 30) 0x4#32) 0x80020e88
  let c17 := c16.wr 11 (alu .sub (c16.get 5) (c16.get 6)) 0x80020e8c
  let c18 := c17.goto 0x80020f28
  let c19 := c18.wr 12 (alu .sub (c18.get 0) (c18.get 28)) 0x80020f2c
  let c20 := c19.wr 12 (alu .and (c19.get 12) 0x18#32) 0x80020f2e
  -- values
  have g2 : c2.get 2 = c.get 2 := by simp [c2, c1, Core.wr_get_ne]
  have g4_2 : c4.get 2 = c.get 2 := by simp [c4, c3, c2, c1, Core.wr_get_ne]
  have g13_2 : c13.get 2 = c.get 2 := by
    simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have g6 : ∀ d : Core, (d = c3 ∨ d = c6 ∨ d = c14 ∨ d = c16) → d.get 6 = BitVec.ofNat 32 3 := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl <;>
      simp [c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h6]
  have g5 : ∀ d : Core, (d = c8 ∨ d = c16) → d.get 5 = c.get 5 := by
    intro d hd; rcases hd with rfl | rfl <;>
      simp [c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v14 : c4.get 14 = 1 := by
    simp only [c4, Core.wr_get_self _ (14 : Reg) _ _ (by decide)]
    rw [g6 c3 (by simp)]; simp [c3, c2, Core.wr_get_ne, Core.wr_get_self, alu]
  have v15 : c7.get 15 = 1 := by
    simp only [c7, c6, Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 12 by decide),
      Core.wr_get_self _ (15 : Reg) _ _ (by decide)]
    rw [show c5.get 14 = 1 by simp only [c5, Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 12 by decide)]; exact v14]
    decide
  have v12 : c9.get 12 = (c.get 2 + 0x14#32) + BitVec.ofNat 32 3 := by
    simp only [c9, c8, c7, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 11 by decide), Core.goto_get,
      Core.wr_get_self _ (12 : Reg) _ _ (by decide)]
    rw [g6 c6 (by simp)]
    simp only [c6, c5, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 15 by decide),
      Core.wr_get_self _ (12 : Reg) _ _ (by decide), g4_2, alu]
    exact or_small _ _ hT (by decide)
  have v11 : c9.get 11 = extend .b false (ramRead R1 (c.get 5 + 0x0#32) .b) := by
    simp only [c9, Core.wr_get_self _ (11 : Reg) _ _ (by decide)]; rw [g5 c8 (by simp)]
  have v14b : c12.get 14 = 0 := by
    simp only [c12, Core.wr_get_self _ (14 : Reg) _ _ (by decide), c11, c10, c9, c8, c7, c6, c5,
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 11 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 12 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 15 by decide), Core.goto_get]
    rw [v14]; decide
  have v30 : c15.get 30 = c.get 30 := by
    simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v13 : c17.get 13 = c.get 13 := by
    simp [c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v12b : c17.get 12 = c.get 30 + 0x4#32 := by
    simp only [c17, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 11 by decide), c16,
      Core.wr_get_self _ (12 : Reg) _ _ (by decide)]
    rw [v30]; rfl
  have v28 : c18.get 28 = BitVec.ofNat 32 (8 * 3) := by
    simp only [c18, c17, c16, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 11 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 12 by decide), c15,
      Core.wr_get_self _ (28 : Reg) _ _ (by decide)]
    rw [show c14.get 6 = BitVec.ofNat 32 3 from g6 c14 (by simp)]; decide
  -- RAM facts
  have hsr0 : B.inRam (c.get 5 + 0x0#32) 1 = true := by simpa using hsr
  have hT3 : B.inRam ((c.get 2 + 0x14#32) + BitVec.ofNat 32 3 + 0x0#32) 1 = true := by
    rw [B_ram] at *; constructor <;> bv_omega
  -- steps
  have q : ∀ d : Core, d.sameCsr c → Quiet d := fun d h => Quiet.of_sameCsr h hq
  have s1 : DetStep B img ⟨c, R⟩ ⟨c1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020e64) fun o => ?_
    rw [exec_opimm, hpc]; rfl
  have s2 : DetStep B img ⟨c1, R⟩ ⟨c2, R⟩ := by
    refine detStep_of (by show (0x80020e66 : Word).getLsbD 0 = false; decide) f80020e66 fun o => ?_
    rw [exec_opimm]; rfl
  have s3 : DetStep B img ⟨c2, R⟩ ⟨c3, R1⟩ := by
    refine detStep_of (by show (0x80020e68 : Word).getLsbD 0 = false; decide) f80020e68 fun o => ?_
    rw [exec_store, show c2.get 2 + 0x14#32 = (c.get 2 + 0x14#32) by rw [g2]]
    rw [interp_store_ram (w := .w) o hT hTr]; rfl
  have s4 : DetStep B img ⟨c3, R1⟩ ⟨c4, R1⟩ := by
    refine detStep_of (by show (0x80020e6a : Word).getLsbD 0 = false; decide) f80020e6a fun o => ?_
    rw [exec_op]; rfl
  have s5 : DetStep B img ⟨c4, R1⟩ ⟨c5, R1⟩ := by
    refine detStep_of (by show (0x80020e6e : Word).getLsbD 0 = false; decide) f80020e6e fun o => ?_
    rw [exec_opimm]; rfl
  have s6 : DetStep B img ⟨c5, R1⟩ ⟨c6, R1⟩ := by
    refine detStep_of (by show (0x80020e70 : Word).getLsbD 0 = false; decide) f80020e70 fun o => ?_
    rw [exec_opimm]; rfl
  have s7 : DetStep B img ⟨c6, R1⟩ ⟨c7, R1⟩ := by
    refine detStep_of (by show (0x80020e74 : Word).getLsbD 0 = false; decide) f80020e74 fun o => ?_
    rw [exec_op]; rfl
  have s8 : DetStep B img ⟨c7, R1⟩ ⟨c8, R1⟩ := by
    refine detStep_of (by show (0x80020e78 : Word).getLsbD 0 = false; decide) f80020e78 fun o => ?_
    rw [exec_branch, v15, Core.get_zero]
    simp only [taken, show ((1 : Word) != 0) = true by decide, if_true]
    rw [show c7.pc + 0x82#32 = 0x80020efa by rw [show c7.pc = 0x80020e78 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s9 : DetStep B img ⟨c8, R1⟩ ⟨c9, R1⟩ := by
    refine detStep_of (by show (0x80020efa : Word).getLsbD 0 = false; decide) f80020efa fun o => ?_
    rw [exec_load, g5 c8 (by simp), interp_load_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) hsr0]
    rw [← g5 c8 (by simp)]; rfl
  have s10 : DetStep B img ⟨c9, R1⟩ ⟨c10, R2⟩ := by
    refine detStep_of (by show (0x80020efe : Word).getLsbD 0 = false; decide) f80020efe fun o => ?_
    rw [exec_store, v12, interp_store_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) hT3,
      ← v12]; rfl
  have s11 : DetStep B img ⟨c10, R2⟩ ⟨c11, R2⟩ := by
    refine detStep_of (by show (0x80020f02 : Word).getLsbD 0 = false; decide) f80020f02 fun o => ?_
    rw [exec_opimm]; rfl
  have s12 : DetStep B img ⟨c11, R2⟩ ⟨c12, R2⟩ := by
    refine detStep_of (by show (0x80020f04 : Word).getLsbD 0 = false; decide) f80020f04 fun o => ?_
    rw [exec_opimm]; rfl
  have s13 : DetStep B img ⟨c12, R2⟩ ⟨c13, R2⟩ := by
    refine detStep_of (by show (0x80020f06 : Word).getLsbD 0 = false; decide) f80020f06 fun o => ?_
    rw [exec_branch, v14b, Core.get_zero]
    simp only [taken, beq_self_eq_true, if_true]
    rw [show c12.pc + 0xffffff78#32 = 0x80020e7e by rw [show c12.pc = 0x80020f06 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s14 : DetStep B img ⟨c13, R2⟩ ⟨c14, R2⟩ := by
    refine detStep_of (by show (0x80020e7e : Word).getLsbD 0 = false; decide) f80020e7e fun o => ?_
    rw [exec_load, g13_2]
    have hTr' : B.inRam (c.get 2 + 0x14#32) 4 = true := hTr
    rw [interp_load_ram (w := .w) o hT hTr', ← g13_2]; rfl
  have s15 : DetStep B img ⟨c14, R2⟩ ⟨c15, R2⟩ := by
    refine detStep_of (by show (0x80020e80 : Word).getLsbD 0 = false; decide) f80020e80 fun o => ?_
    rw [exec_opimm]; rfl
  have s16 : DetStep B img ⟨c15, R2⟩ ⟨c16, R2⟩ := by
    refine detStep_of (by show (0x80020e84 : Word).getLsbD 0 = false; decide) f80020e84 fun o => ?_
    rw [exec_opimm]; rfl
  have s17 : DetStep B img ⟨c16, R2⟩ ⟨c17, R2⟩ := by
    refine detStep_of (by show (0x80020e88 : Word).getLsbD 0 = false; decide) f80020e88 fun o => ?_
    rw [exec_op]; rfl
  have s18 : DetStep B img ⟨c17, R2⟩ ⟨c18, R2⟩ := by
    refine detStep_of (by show (0x80020e8c : Word).getLsbD 0 = false; decide) f80020e8c fun o => ?_
    rw [exec_branch, v12b, v13]
    simp only [taken, hlp, if_true]
    rw [show c17.pc + 0x9c#32 = 0x80020f28 by rw [show c17.pc = 0x80020e8c from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s19 : DetStep B img ⟨c18, R2⟩ ⟨c19, R2⟩ := by
    refine detStep_of (by show (0x80020f28 : Word).getLsbD 0 = false; decide) f80020f28 fun o => ?_
    rw [exec_op]; rfl
  have s20 : DetStep B img ⟨c19, R2⟩ ⟨c20, R2⟩ := by
    refine detStep_of (by show (0x80020f2c : Word).getLsbD 0 = false; decide) f80020f2c fun o => ?_
    rw [exec_opimm]; rfl
  have k1 : c1.sameCsr c := (Core.sameCsr_wr _ _ _ _)
  have k2 : c2.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : c3.sameCsr c := (Core.sameCsr_goto _ _).trans k2
  have k4 : c4.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : c5.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : c7.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k6
  have k8 : c8.sameCsr c := (Core.sameCsr_goto _ _).trans k7
  have k9 : c9.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : c10.sameCsr c := (Core.sameCsr_goto _ _).trans k9
  have k11 : c11.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k10
  have k12 : c12.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k11
  have k13 : c13.sameCsr c := (Core.sameCsr_goto _ _).trans k12
  have k14 : c14.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k13
  have k15 : c15.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k14
  have k16 : c16.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k15
  have k17 : c17.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k16
  have k18 : c18.sameCsr c := (Core.sameCsr_goto _ _).trans k17
  have k19 : c19.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k18
  have k20 : c20.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k19
  have run : QRun B img 20 ⟨c, R⟩ ⟨c20, R2⟩ :=
    .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4
    (.step (q _ k4) s5 (.step (q _ k5) s6 (.step (q _ k6) s7
    (.step (q _ k7) s8 (.step (q _ k8) s9 (.step (q _ k9) s10
    (.step (q _ k10) s11 (.step (q _ k11) s12 (.step (q _ k12) s13
    (.step (q _ k13) s14 (.step (q _ k14) s15 (.step (q _ k15) s16
    (.step (q _ k16) s17 (.step (q _ k17) s18 (.step (q _ k18) s19
    (.single (q _ k19) s20)))))))))))))))))))
  have hR1 : ∀ x, ¬ ((c.get 2 + 0x14#32).toNat ≤ x.toNat ∧ x.toNat < (c.get 2 + 0x14#32).toNat + 4) →
      R1 x = R x := by
    intro x hx
    show ramWrite R (c2.get 2 + 0x14#32) (c2.get 0) .w x = R x
    rw [g2]; apply ramWrite_w_other; intro k hk; have := (B_ram _ _).mp hTr; bv_omega
  have hR2 : R2 = ramPut R1 ((c.get 2 + 0x14#32) + BitVec.ofNat 32 3) (R1 (c.get 5)) := by
    show ramWrite R1 (c9.get 12 + 0x0#32) (c9.get 11) .b = _
    rw [v12, v11, BitVec.add_zero, BitVec.add_zero, copyByte]
  refine ⟨c20, R2, run, ⟨rfl, k20, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [c20, c19, Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 12 by decide)]; exact v28
  · simp only [c20, c19, Core.wr_get_self _ (12 : Reg) _ _ (by decide), Core.get_zero, v28, alu]
  · simp only [c20, c19, c18, Core.wr_get_ne _ _ _ _ _ (show (11 : Reg) ≠ 12 by decide), Core.goto_get, c17,
      Core.wr_get_self _ (11 : Reg) _ _ (by decide), alu]
    rw [g5 c16 (by simp), g6 c16 (by simp)]
  · intro k hk1 hk2
    have hk : k = 3 := by omega
    subst hk
    have e15 : c20.get 15 = ramRead R2 (c.get 2 + 0x14#32) .w := by
      simp only [c20, c19, c18, c17, c16, c15, Core.goto_get,
        Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 12 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 11 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 28 by decide), c14,
        Core.wr_get_self _ (15 : Reg) _ _ (by decide)]
      rw [g13_2]; rfl
    rw [e15, byte_read_k _ _ _ (by decide), hR2, show c.get 5 - BitVec.ofNat 32 3 + BitVec.ofNat 32 3 = c.get 5 by
      bv_omega]
    simp only [ramPut, if_pos rfl]
    have hne : c.get 5 ≠ (c.get 2 + 0x14#32) + BitVec.ofNat 32 3 := by bv_omega
    rw [if_neg hne]; simp
  · intro x hx
    rw [hR2]; simp only [ramPut]
    rw [if_neg (by intro e; apply hx; subst e; have := (B_ram _ _).mp hTr; constructor <;> bv_omega)]
    exact hR1 x hx
  · intro r hr
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h15 : r ≠ 15 := fun e => hr (by subst e; decide)
    have h28 : r ≠ 28 := fun e => hr (by subst e; decide)
    simp [c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1,
      Core.wr_get_ne, h11, h12, h14, h15, h28]

theorem byte_read_h (R : Word → BitVec 8) (x : Word) :
    byteOf (ramRead R x .h) 0 = R x ∧ byteOf (ramRead R x .h) 1 = R (x + 1) := by
  have h0 := (R x).isLt; have h1 := (R (x + 1)).isLt
  constructor <;> apply BitVec.eq_of_toNat_eq <;> simp only [byteOf, ramRead, BitVec.toNat_ofNat] <;> omega

/-- Misalignment 2: one source halfword into the temporary. -/
theorem start2 (c : Core) (R : Word → BitVec 8) (hpc : c.pc = 0x80020e64) (hq : Quiet c)
    (h6 : c.get 6 = BitVec.ofNat 32 2) (hsr : B.inRam (c.get 5) 2 = true) (hS2 : (c.get 5).toNat % 2 = 0)
    (hT : (c.get 2 + 0x14#32).toNat % 4 = 0) (hTr : B.inRam (c.get 2 + 0x14#32) 4 = true)
    (hsep : (c.get 5).toNat + 2 ≤ (c.get 2 + 0x14#32).toNat ∨ (c.get 2 + 0x14#32).toNat + 4 ≤ (c.get 5).toNat)
    (hlp : (c.get 30 + 0x4#32).ult (c.get 13) = true) :
    ∃ g R', QRun B img 21 ⟨c, R⟩ ⟨g, R'⟩ ∧ AtLoop c g R R' 2 := by
  let c1 := c.wr 11 (alu .add (c.get 0) 0x0#32) 0x80020e66
  let c2 := c1.wr 12 (alu .add (c1.get 0) 0x4#32) 0x80020e68
  let R1 := ramWrite R (c2.get 2 + 0x14#32) (c2.get 0) .w
  let c3 := c2.goto 0x80020e6a
  let c4 := c3.wr 14 (alu .sub (c3.get 12) (c3.get 6)) 0x80020e6e
  let c5 := c4.wr 12 (alu .add (c4.get 2) 0x14#32) 0x80020e70
  let c6 := c5.wr 15 (alu .and (c5.get 14) 0x1#32) 0x80020e74
  let c7 := c6.wr 12 (alu .or (c6.get 12) (c6.get 6)) 0x80020e78
  let c8 := c7.goto 0x80020e7a
  let c9 := c8.wr 14 (alu .and (c8.get 14) 0x2#32) 0x80020e7c
  let c10 := c9.goto 0x80020f08
  let c11 := c10.wr 14 (alu .add (c10.get 5) (c10.get 11)) 0x80020f0c
  let c12 := c11.wr 14 (extend .h true (ramRead R1 (c11.get 14 + 0x0#32) .h)) 0x80020f10
  let c13 := c12.wr 11 (alu .add (c12.get 11) (c12.get 12)) 0x80020f12
  let R2 := ramWrite R1 (c13.get 11 + 0x0#32) (c13.get 14) .h
  let c14 := c13.goto 0x80020f16
  let c15 := c14.wr 15 (extend .w true (ramRead R2 (c14.get 2 + 0x14#32) .w)) 0x80020f18
  let c16 := c15.wr 28 (alu .sll (c15.get 6) 0x3#32) 0x80020f1c
  let c17 := c16.wr 12 (alu .add (c16.get 30) 0x4#32) 0x80020f20
  let c18 := c17.wr 11 (alu .sub (c17.get 5) (c17.get 6)) 0x80020f24
  let c19 := c18.goto 0x80020f28
  let c20 := c19.wr 12 (alu .sub (c19.get 0) (c19.get 28)) 0x80020f2c
  let c21 := c20.wr 12 (alu .and (c20.get 12) 0x18#32) 0x80020f2e
  have g2 : c2.get 2 = c.get 2 := by simp [c2, c1, Core.wr_get_ne]
  have g4_2 : c4.get 2 = c.get 2 := by simp [c4, c3, c2, c1, Core.wr_get_ne]
  have g14_2 : c14.get 2 = c.get 2 := by
    simp [c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have g6 : ∀ d : Core, (d = c3 ∨ d = c6 ∨ d = c15 ∨ d = c17) → d.get 6 = BitVec.ofNat 32 2 := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl <;>
      simp [c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h6]
  have g5 : ∀ d : Core, (d = c10 ∨ d = c17) → d.get 5 = c.get 5 := by
    intro d hd; rcases hd with rfl | rfl <;>
      simp [c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v14 : c4.get 14 = 2 := by
    simp only [c4, Core.wr_get_self _ (14 : Reg) _ _ (by decide)]
    rw [g6 c3 (by simp)]; simp [c3, c2, Core.wr_get_self, alu]
  have v15 : c7.get 15 = 0 := by
    simp only [c7, c6, Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 12 by decide),
      Core.wr_get_self _ (15 : Reg) _ _ (by decide)]
    rw [show c5.get 14 = 2 by simp only [c5, Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 12 by decide)]; exact v14]
    decide
  have v12 : c13.get 12 = (c.get 2 + 0x14#32) + BitVec.ofNat 32 2 := by
    simp only [c13, c12, c11, c10, c9, c8, c7, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 11 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 14 by decide), Core.goto_get,
      Core.wr_get_self _ (12 : Reg) _ _ (by decide)]
    rw [g6 c6 (by simp)]
    simp only [c6, c5, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 15 by decide),
      Core.wr_get_self _ (12 : Reg) _ _ (by decide), g4_2, alu]
    exact or_small _ _ hT (by decide)
  have v11 : c12.get 11 = 0 := by
    simp [c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, Core.wr_get_self, alu]
  have v9 : c9.get 14 = 2 := by
    simp only [c9, Core.wr_get_self _ (14 : Reg) _ _ (by decide), c8, c7, c6, c5, Core.goto_get,
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 12 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 15 by decide)]
    rw [v14]; decide
  have v11a : c11.get 14 = c.get 5 := by
    simp only [c11, Core.wr_get_self _ (14 : Reg) _ _ (by decide)]
    rw [g5 c10 (by simp)]
    simp [c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, Core.wr_get_self, alu]
  have v13_11 : c13.get 11 = (c.get 2 + 0x14#32) + BitVec.ofNat 32 2 := by
    simp only [c13, Core.wr_get_self _ (11 : Reg) _ _ (by decide)]
    rw [v11, show c12.get 12 = c13.get 12 by simp [c13, Core.wr_get_ne], v12]; simp [alu]
  have v13_14 : c13.get 14 = extend .h true (ramRead R1 (c.get 5 + 0x0#32) .h) := by
    simp only [c13, c12, Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 11 by decide),
      Core.wr_get_self _ (14 : Reg) _ _ (by decide)]
    rw [v11a]
  have v30 : c16.get 30 = c.get 30 := by
    simp [c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v13 : c18.get 13 = c.get 13 := by
    simp [c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v12b : c18.get 12 = c.get 30 + 0x4#32 := by
    simp only [c18, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 11 by decide), c17,
      Core.wr_get_self _ (12 : Reg) _ _ (by decide)]
    rw [v30]; rfl
  have v28 : c19.get 28 = BitVec.ofNat 32 (8 * 2) := by
    simp only [c19, c18, c17, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 11 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 12 by decide), c16,
      Core.wr_get_self _ (28 : Reg) _ _ (by decide)]
    rw [show c15.get 6 = BitVec.ofNat 32 2 from g6 c15 (by simp)]; decide
  have hsr0 : B.inRam (c.get 5 + 0x0#32) 2 = true := by simpa using hsr
  have hT2 : B.inRam ((c.get 2 + 0x14#32) + BitVec.ofNat 32 2 + 0x0#32) 2 = true := by
    rw [B_ram] at *; constructor <;> bv_omega
  have q : ∀ d : Core, d.sameCsr c → Quiet d := fun d h => Quiet.of_sameCsr h hq
  have s1 : DetStep B img ⟨c, R⟩ ⟨c1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020e64) fun o => ?_
    rw [exec_opimm, hpc]; rfl
  have s2 : DetStep B img ⟨c1, R⟩ ⟨c2, R⟩ := by
    refine detStep_of (by show (0x80020e66 : Word).getLsbD 0 = false; decide) f80020e66 fun o => ?_
    rw [exec_opimm]; rfl
  have s3 : DetStep B img ⟨c2, R⟩ ⟨c3, R1⟩ := by
    refine detStep_of (by show (0x80020e68 : Word).getLsbD 0 = false; decide) f80020e68 fun o => ?_
    rw [exec_store, show c2.get 2 + 0x14#32 = c.get 2 + 0x14#32 by rw [g2]]
    rw [interp_store_ram (w := .w) o hT hTr]; rfl
  have s4 : DetStep B img ⟨c3, R1⟩ ⟨c4, R1⟩ := by
    refine detStep_of (by show (0x80020e6a : Word).getLsbD 0 = false; decide) f80020e6a fun o => ?_
    rw [exec_op]; rfl
  have s5 : DetStep B img ⟨c4, R1⟩ ⟨c5, R1⟩ := by
    refine detStep_of (by show (0x80020e6e : Word).getLsbD 0 = false; decide) f80020e6e fun o => ?_
    rw [exec_opimm]; rfl
  have s6 : DetStep B img ⟨c5, R1⟩ ⟨c6, R1⟩ := by
    refine detStep_of (by show (0x80020e70 : Word).getLsbD 0 = false; decide) f80020e70 fun o => ?_
    rw [exec_opimm]; rfl
  have s7 : DetStep B img ⟨c6, R1⟩ ⟨c7, R1⟩ := by
    refine detStep_of (by show (0x80020e74 : Word).getLsbD 0 = false; decide) f80020e74 fun o => ?_
    rw [exec_op]; rfl
  have s8 : DetStep B img ⟨c7, R1⟩ ⟨c8, R1⟩ := by
    refine detStep_of (by show (0x80020e78 : Word).getLsbD 0 = false; decide) f80020e78 fun o => ?_
    rw [exec_branch, v15, Core.get_zero]
    simp only [taken, show ((0 : Word) != 0) = false by decide, Bool.false_eq_true, if_false]; rfl
  have s9 : DetStep B img ⟨c8, R1⟩ ⟨c9, R1⟩ := by
    refine detStep_of (by show (0x80020e7a : Word).getLsbD 0 = false; decide) f80020e7a fun o => ?_
    rw [exec_opimm]; rfl
  have s10 : DetStep B img ⟨c9, R1⟩ ⟨c10, R1⟩ := by
    refine detStep_of (by show (0x80020e7c : Word).getLsbD 0 = false; decide) f80020e7c fun o => ?_
    rw [exec_branch, v9, Core.get_zero]
    simp only [taken, show ((2 : Word) != 0) = true by decide, if_true]
    rw [show c9.pc + 0x8c#32 = 0x80020f08 by rw [show c9.pc = 0x80020e7c from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s11 : DetStep B img ⟨c10, R1⟩ ⟨c11, R1⟩ := by
    refine detStep_of (by show (0x80020f08 : Word).getLsbD 0 = false; decide) f80020f08 fun o => ?_
    rw [exec_op]; rfl
  have s12 : DetStep B img ⟨c11, R1⟩ ⟨c12, R1⟩ := by
    refine detStep_of (by show (0x80020f0c : Word).getLsbD 0 = false; decide) f80020f0c fun o => ?_
    rw [exec_load, v11a, interp_load_ram (w := .h) o (by simp only [Width.bytes]; bv_omega) hsr0, ← v11a]; rfl
  have s13 : DetStep B img ⟨c12, R1⟩ ⟨c13, R1⟩ := by
    refine detStep_of (by show (0x80020f10 : Word).getLsbD 0 = false; decide) f80020f10 fun o => ?_
    rw [exec_op]; rfl
  have s14 : DetStep B img ⟨c13, R1⟩ ⟨c14, R2⟩ := by
    refine detStep_of (by show (0x80020f12 : Word).getLsbD 0 = false; decide) f80020f12 fun o => ?_
    rw [exec_store, v13_11, interp_store_ram (w := .h) o (by simp only [Width.bytes]; bv_omega) hT2,
      ← v13_11]; rfl
  have s15 : DetStep B img ⟨c14, R2⟩ ⟨c15, R2⟩ := by
    refine detStep_of (by show (0x80020f16 : Word).getLsbD 0 = false; decide) f80020f16 fun o => ?_
    rw [exec_load, g14_2]
    rw [interp_load_ram (w := .w) o hT hTr, ← g14_2]; rfl
  have s16 : DetStep B img ⟨c15, R2⟩ ⟨c16, R2⟩ := by
    refine detStep_of (by show (0x80020f18 : Word).getLsbD 0 = false; decide) f80020f18 fun o => ?_
    rw [exec_opimm]; rfl
  have s17 : DetStep B img ⟨c16, R2⟩ ⟨c17, R2⟩ := by
    refine detStep_of (by show (0x80020f1c : Word).getLsbD 0 = false; decide) f80020f1c fun o => ?_
    rw [exec_opimm]; rfl
  have s18 : DetStep B img ⟨c17, R2⟩ ⟨c18, R2⟩ := by
    refine detStep_of (by show (0x80020f20 : Word).getLsbD 0 = false; decide) f80020f20 fun o => ?_
    rw [exec_op]; rfl
  have s19 : DetStep B img ⟨c18, R2⟩ ⟨c19, R2⟩ := by
    refine detStep_of (by show (0x80020f24 : Word).getLsbD 0 = false; decide) f80020f24 fun o => ?_
    rw [exec_branch, v12b, v13]
    simp only [taken, hlp, Bool.not_true, Bool.false_eq_true, if_false]; rfl
  have s20 : DetStep B img ⟨c19, R2⟩ ⟨c20, R2⟩ := by
    refine detStep_of (by show (0x80020f28 : Word).getLsbD 0 = false; decide) f80020f28 fun o => ?_
    rw [exec_op]; rfl
  have s21 : DetStep B img ⟨c20, R2⟩ ⟨c21, R2⟩ := by
    refine detStep_of (by show (0x80020f2c : Word).getLsbD 0 = false; decide) f80020f2c fun o => ?_
    rw [exec_opimm]; rfl
  have k1 : c1.sameCsr c := (Core.sameCsr_wr _ _ _ _)
  have k2 : c2.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : c3.sameCsr c := (Core.sameCsr_goto _ _).trans k2
  have k4 : c4.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : c5.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : c7.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k6
  have k8 : c8.sameCsr c := (Core.sameCsr_goto _ _).trans k7
  have k9 : c9.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : c10.sameCsr c := (Core.sameCsr_goto _ _).trans k9
  have k11 : c11.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k10
  have k12 : c12.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k11
  have k13 : c13.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k12
  have k14 : c14.sameCsr c := (Core.sameCsr_goto _ _).trans k13
  have k15 : c15.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k14
  have k16 : c16.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k15
  have k17 : c17.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k16
  have k18 : c18.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k17
  have k19 : c19.sameCsr c := (Core.sameCsr_goto _ _).trans k18
  have k20 : c20.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k19
  have k21 : c21.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k20
  have run : QRun B img 21 ⟨c, R⟩ ⟨c21, R2⟩ :=
    .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5 (.step (q _ k5) s6 (.step (q _ k6) s7 (.step (q _ k7) s8 (.step (q _ k8) s9 (.step (q _ k9) s10 (.step (q _ k10) s11 (.step (q _ k11) s12 (.step (q _ k12) s13 (.step (q _ k13) s14 (.step (q _ k14) s15 (.step (q _ k15) s16 (.step (q _ k16) s17 (.step (q _ k17) s18 (.step (q _ k18) s19 (.step (q _ k19) s20 (.single (q _ k20) s21))))))))))))))))))))
  have hR1 : ∀ x, ¬ ((c.get 2 + 0x14#32).toNat ≤ x.toNat ∧ x.toNat < (c.get 2 + 0x14#32).toNat + 4) →
      R1 x = R x := by
    intro x hx
    show ramWrite R (c2.get 2 + 0x14#32) (c2.get 0) .w x = R x
    rw [g2]; apply ramWrite_w_other; intro k hk; have := (B_ram _ _).mp hTr; bv_omega
  obtain ⟨hb0, hb1⟩ := byte_read_h R1 (c.get 5)
  have hR2 : R2 = ramPut (ramPut R1 ((c.get 2 + 0x14#32) + BitVec.ofNat 32 2) (R1 (c.get 5)))
      ((c.get 2 + 0x14#32) + BitVec.ofNat 32 2 + 1) (R1 (c.get 5 + 1)) := by
    show ramWrite R1 (c13.get 11 + 0x0#32) (c13.get 14) .h = _
    rw [v13_11, v13_14, BitVec.add_zero]
    simp only [ramWrite, byte_sext _ 0 (by decide), byte_sext _ 1 (by decide), hb0, hb1, BitVec.add_zero]
  refine ⟨c21, R2, run, ⟨rfl, k21, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [c21, c20, Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 12 by decide)]; exact v28
  · simp only [c21, c20, Core.wr_get_self _ (12 : Reg) _ _ (by decide), Core.get_zero, v28, alu]
  · simp only [c21, c20, c19, Core.wr_get_ne _ _ _ _ _ (show (11 : Reg) ≠ 12 by decide), Core.goto_get, c18,
      Core.wr_get_self _ (11 : Reg) _ _ (by decide), alu]
    rw [g5 c17 (by simp), g6 c17 (by simp)]
  · intro k hk1 hk2
    have e15 : c21.get 15 = ramRead R2 (c.get 2 + 0x14#32) .w := by
      simp only [c21, c20, c19, c18, c17, c16, Core.goto_get,
        Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 12 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 11 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 28 by decide), c15,
        Core.wr_get_self _ (15 : Reg) _ _ (by decide)]
      rw [g14_2]; rfl
    have hTr' := (B_ram _ _).mp hTr
    rw [e15, byte_read_k _ _ _ hk2, hR2]
    simp only [ramPut]
    have hsep' := hsep
    rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl <;>
    · repeat' split
      all_goals first | (exfalso; bv_omega) | (refine congrArg R1 ?_; bv_omega) | (exfalso; simp_all) | rfl
  · intro x hx
    rw [hR2]; simp only [ramPut]
    have hTr' := (B_ram _ _).mp hTr
    rw [if_neg (by intro e; apply hx; subst e; constructor <;> bv_omega),
      if_neg (by intro e; apply hx; subst e; constructor <;> bv_omega)]
    exact hR1 x hx
  · intro r hr
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h15 : r ≠ 15 := fun e => hr (by subst e; decide)
    have h28 : r ≠ 28 := fun e => hr (by subst e; decide)
    simp [c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1,
      Core.wr_get_ne, h11, h12, h14, h15, h28]

end E5R.Rmk
