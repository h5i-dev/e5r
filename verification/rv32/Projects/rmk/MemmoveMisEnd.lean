/-
  memmove's misaligned forward path, the final destination word
  (pinned RMK image), 0x80020f4c..0x80020fb2: the last o source bytes are
  loaded (o = 1, 3 through the stack temporaries sp+0x10 / sp+0xe), merged
  with the previous source word and stored at t5; then 0x80020fb6.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.MemmoveMisStart

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-- What the end block leaves: the source word at a1 + o stored at t5, the
    two stack temporaries possibly changed, nothing else. -/
structure AtTail (g g' : Core) (R0 R' : Word → BitVec 8) (o : Nat) : Prop where
  pc : g'.pc = 0x80020fb6
  csr : g'.sameCsr g
  ram : ∃ Rt : Word → BitVec 8, (∀ x, x ≠ g.get 2 + 0x10#32 → x ≠ g.get 2 + 0xe#32 → Rt x = R0 x) ∧
    R' = ramWrite Rt (g.get 30) (ramRead R0 (g.get 11 + BitVec.ofNat 32 o) .w) .w
  frame : ∀ r : Reg, r.val ∉ [6, 7, 11, 12, 14, 29] → g'.get r = g.get r

theorem byte0_ext (R : Word → BitVec 8) (a : Word) : byteOf (extend .b false (ramRead R a .b)) 0 = R a :=
  lbu_byte R a

/-- o = 2: two bytes loaded directly. -/
theorem end2 (g : Core) (R0 : Word → BitVec 8) (hpc : g.pc = 0x80020f4c) (hq : Quiet g)
    (h6 : g.get 6 = BitVec.ofNat 32 2) (h28 : g.get 28 = BitVec.ofNat 32 (8 * 2))
    (h5 : (g.get 5).toNat % 2 = 0)
    (hprev : ∀ k, 2 ≤ k → k < 4 → byteOf (g.get 15) k = R0 (g.get 11 + BitVec.ofNat 32 k))
    (hsrc : B.inRam (g.get 11 + 4#32) 2 = true)
    (ht10 : B.inRam (g.get 2 + 0x10#32) 1 = true) (ht0e : B.inRam (g.get 2 + 0xe#32) 1 = true)
    (hsep : ∀ j < 2, g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0x10#32 ∧
      g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0xe#32)
    (hD : (g.get 30).toNat % 4 = 0) (hDr : B.inRam (g.get 30) 4 = true) :
    ∃ g' R', QRun B img 21 ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtTail g g' R0 R' 2 := by
  let R1 := ramWrite R0 (g.get 2 + 0x10#32) (g.get 0) .b
  let c1 := g.goto 0x80020f50
  let c2 := c1.wr 12 (alu .add (c1.get 0) 0x1#32) 0x80020f52
  let R2 := ramWrite R1 (c2.get 2 + 0xe#32) (c2.get 0) .b
  let c3 := c2.goto 0x80020f56
  let c4 := c3.goto 0x80020f7e
  let c5 := c4.wr 6 (extend .b false (ramRead R2 (c4.get 11 + 0x4#32) .b)) 0x80020f82
  let c6 := c5.wr 7 (extend .b false (ramRead R2 (c5.get 11 + 0x5#32) .b)) 0x80020f86
  let c7 := c6.wr 29 (alu .add (c6.get 0) 0x2#32) 0x80020f88
  let R3 := ramWrite R2 (c7.get 2 + 0x10#32) (c7.get 6) .b
  let c8 := c7.goto 0x80020f8c
  let c9 := c8.wr 7 (alu .sll (c8.get 7) 0x8#32) 0x80020f8e
  let c10 := c9.wr 12 (alu .add (c9.get 2) 0xe#32) 0x80020f92
  let c11 := c10.wr 14 (alu .and (c10.get 5) 0x1#32) 0x80020f96
  let c12 := c11.goto 0x80020f98
  let c13 := c12.wr 11 (alu .add (c12.get 0) 0x0#32) 0x80020f9a
  let c14 := c13.wr 11 (alu .or (c13.get 7) (c13.get 11)) 0x80020f9e
  let c15 := c14.wr 12 (alu .srl (c14.get 15) (c14.get 28)) 0x80020fa2
  let c16 := c15.wr 14 (alu .sub (c15.get 0) (c15.get 28)) 0x80020fa6
  let c17 := c16.wr 11 (alu .or (c16.get 11) (c16.get 6)) 0x80020faa
  let c18 := c17.wr 14 (alu .and (c17.get 14) 0x18#32) 0x80020fac
  let c19 := c18.wr 11 (alu .sll (c18.get 11) (c18.get 14)) 0x80020fb0
  let c20 := c19.wr 11 (alu .or (c19.get 11) (c19.get 12)) 0x80020fb2
  let R4 := ramWrite R3 (g.get 30) (c20.get 11) .w
  let c21 := c20.goto 0x80020fb6
  have g2 : ∀ d : Core, (d = c2 ∨ d = c7) → d.get 2 = g.get 2 := by
    intro d hd; rcases hd with rfl | rfl <;> simp [c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have g11 : ∀ d : Core, (d = c4 ∨ d = c5) → d.get 11 = g.get 11 := by
    intro d hd; rcases hd with rfl | rfl <;> simp [c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v12 : c3.get 12 = 1 := by simp [c3, c2, Core.wr_get_self, alu]
  have v6 : c3.get 6 = BitVec.ofNat 32 2 := by simp [c3, c2, c1, Core.wr_get_ne, h6]
  have v14 : c11.get 14 = 0 := by
    simp only [c11, Core.wr_get_self _ (14 : Reg) _ _ (by decide), alu]
    have : c10.get 5 = g.get 5 := by simp [c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
    rw [this]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x1#32 : Word).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h5
  have v28 : ∀ d : Core, (d = c14 ∨ d = c15) → d.get 28 = BitVec.ofNat 32 (8 * 2) := by
    intro d hd; rcases hd with rfl | rfl <;>
      simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h28]
  let b0 := extend .b false (ramRead R2 (g.get 11 + 0x4#32) .b)
  let b1 := extend .b false (ramRead R2 (g.get 11 + 0x5#32) .b)
  have vb0 : c16.get 6 = b0 := by
    simp only [c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, Core.goto_get,
      Core.wr_get_ne _ _ _ _ _ (show (6 : Reg) ≠ 14 by decide), Core.wr_get_ne _ _ _ _ _ (show (6 : Reg) ≠ 12 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (6 : Reg) ≠ 11 by decide), Core.wr_get_ne _ _ _ _ _ (show (6 : Reg) ≠ 7 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (6 : Reg) ≠ 29 by decide), c5, Core.wr_get_self _ (6 : Reg) _ _ (by decide)]
    rw [g11 c4 (by simp)]
  have vval : c20.get 11 = (g.get 15 >>> (8 * 2)) ||| (((b1 <<< 8) ||| ((0 : Word) <<< 16) ||| b0) <<< (32 - 8 * 2)) := by
    have e5 : c5.get 11 = g.get 11 := g11 c5 (by simp)
    have e4 : c4.get 11 = g.get 11 := g11 c4 (by simp)
    simp (config := { decide := true }) only [c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8,
      c7, c6, Core.goto_get, Core.wr_get, alu, e5, if_true, if_false]
    have f6 : c5.get 6 = b0 := by simp [c5, Core.wr_get_self, e4, b0]
    have f28 : c5.get 28 = BitVec.ofNat 32 (8 * 2) := by simp [c5, c4, c3, c2, c1, Core.wr_get_ne, h28]
    have f15 : c5.get 15 = g.get 15 := by simp [c5, c4, c3, c2, c1, Core.wr_get_ne]
    obtain ⟨e1, e2⟩ := shifts 2 (by decide)
    rw [f6, f28, f15, e1, e2, show (8#32 : Word).toNat % 32 = 8 from rfl,
      show (0 : Word) <<< 16 = 0 from rfl, show (0 : Word) + 0#32 = 0 from rfl]
    exact BitVec.or_comm _ _
  have hsr := (B_ram _ _).mp hsrc
  have hs0 : B.inRam (g.get 11 + 0x4#32) 1 = true := by rw [B_ram]; constructor <;> bv_omega
  have hs1 : B.inRam (g.get 11 + 0x5#32) 1 = true := by rw [B_ram]; constructor <;> bv_omega
  have q : ∀ d : Core, d.sameCsr g → Quiet d := fun d h => Quiet.of_sameCsr h hq
  have m1 : ∀ x : Word, x.toNat % (Width.b).bytes = 0 := fun x => by simp only [Width.bytes, Nat.mod_one]
  have s1 : DetStep B img ⟨g, R0⟩ ⟨c1, R1⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020f4c) fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (m1 _) ht10, hpc]; rfl
  have s2 : DetStep B img ⟨c1, R1⟩ ⟨c2, R1⟩ := by
    refine detStep_of (by show (0x80020f50 : Word).getLsbD 0 = false; decide) f80020f50 fun o => ?_
    rw [exec_opimm]; rfl
  have s3 : DetStep B img ⟨c2, R1⟩ ⟨c3, R2⟩ := by
    refine detStep_of (by show (0x80020f52 : Word).getLsbD 0 = false; decide) f80020f52 fun o => ?_
    rw [exec_store, g2 c2 (by simp), interp_store_ram (w := .b) o (m1 _) ht0e, ← g2 c2 (by simp)]; rfl
  have s4 : DetStep B img ⟨c3, R2⟩ ⟨c4, R2⟩ := by
    refine detStep_of (by show (0x80020f56 : Word).getLsbD 0 = false; decide) f80020f56 fun o => ?_
    rw [exec_branch, v6, v12]
    simp only [taken, show (BitVec.ofNat 32 2 != (1 : Word)) = true by decide, if_true]
    rw [show c3.pc + 0x28#32 = 0x80020f7e by rw [show c3.pc = 0x80020f56 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s5 : DetStep B img ⟨c4, R2⟩ ⟨c5, R2⟩ := by
    refine detStep_of (by show (0x80020f7e : Word).getLsbD 0 = false; decide) f80020f7e fun o => ?_
    rw [exec_load, g11 c4 (by simp), interp_load_ram (w := .b) o (m1 _) hs0, ← g11 c4 (by simp)]; rfl
  have s6 : DetStep B img ⟨c5, R2⟩ ⟨c6, R2⟩ := by
    refine detStep_of (by show (0x80020f82 : Word).getLsbD 0 = false; decide) f80020f82 fun o => ?_
    rw [exec_load, g11 c5 (by simp), interp_load_ram (w := .b) o (m1 _) hs1, ← g11 c5 (by simp)]; rfl
  have s7 : DetStep B img ⟨c6, R2⟩ ⟨c7, R2⟩ := by
    refine detStep_of (by show (0x80020f86 : Word).getLsbD 0 = false; decide) f80020f86 fun o => ?_
    rw [exec_opimm]; rfl
  have s8 : DetStep B img ⟨c7, R2⟩ ⟨c8, R3⟩ := by
    refine detStep_of (by show (0x80020f88 : Word).getLsbD 0 = false; decide) f80020f88 fun o => ?_
    rw [exec_store, g2 c7 (by simp), interp_store_ram (w := .b) o (m1 _) ht10, ← g2 c7 (by simp)]; rfl
  have s9 : DetStep B img ⟨c8, R3⟩ ⟨c9, R3⟩ := by
    refine detStep_of (by show (0x80020f8c : Word).getLsbD 0 = false; decide) f80020f8c fun o => ?_
    rw [exec_opimm]; rfl
  have s10 : DetStep B img ⟨c9, R3⟩ ⟨c10, R3⟩ := by
    refine detStep_of (by show (0x80020f8e : Word).getLsbD 0 = false; decide) f80020f8e fun o => ?_
    rw [exec_opimm]; rfl
  have s11 : DetStep B img ⟨c10, R3⟩ ⟨c11, R3⟩ := by
    refine detStep_of (by show (0x80020f92 : Word).getLsbD 0 = false; decide) f80020f92 fun o => ?_
    rw [exec_opimm]; rfl
  have s12 : DetStep B img ⟨c11, R3⟩ ⟨c12, R3⟩ := by
    refine detStep_of (by show (0x80020f96 : Word).getLsbD 0 = false; decide) f80020f96 fun o => ?_
    rw [exec_branch, v14, Core.get_zero]
    simp only [taken, show ((0 : Word) != 0) = false by decide, Bool.false_eq_true, if_false]; rfl
  have s13 : DetStep B img ⟨c12, R3⟩ ⟨c13, R3⟩ := by
    refine detStep_of (by show (0x80020f98 : Word).getLsbD 0 = false; decide) f80020f98 fun o => ?_
    rw [exec_opimm]; rfl
  have s14 : DetStep B img ⟨c13, R3⟩ ⟨c14, R3⟩ := by
    refine detStep_of (by show (0x80020f9a : Word).getLsbD 0 = false; decide) f80020f9a fun o => ?_
    rw [exec_op]; rfl
  have s15 : DetStep B img ⟨c14, R3⟩ ⟨c15, R3⟩ := by
    refine detStep_of (by show (0x80020f9e : Word).getLsbD 0 = false; decide) f80020f9e fun o => ?_
    rw [exec_op]; rfl
  have s16 : DetStep B img ⟨c15, R3⟩ ⟨c16, R3⟩ := by
    refine detStep_of (by show (0x80020fa2 : Word).getLsbD 0 = false; decide) f80020fa2 fun o => ?_
    rw [exec_op]; rfl
  have s17 : DetStep B img ⟨c16, R3⟩ ⟨c17, R3⟩ := by
    refine detStep_of (by show (0x80020fa6 : Word).getLsbD 0 = false; decide) f80020fa6 fun o => ?_
    rw [exec_op]; rfl
  have s18 : DetStep B img ⟨c17, R3⟩ ⟨c18, R3⟩ := by
    refine detStep_of (by show (0x80020faa : Word).getLsbD 0 = false; decide) f80020faa fun o => ?_
    rw [exec_opimm]; rfl
  have s19 : DetStep B img ⟨c18, R3⟩ ⟨c19, R3⟩ := by
    refine detStep_of (by show (0x80020fac : Word).getLsbD 0 = false; decide) f80020fac fun o => ?_
    rw [exec_op]; rfl
  have s20 : DetStep B img ⟨c19, R3⟩ ⟨c20, R3⟩ := by
    refine detStep_of (by show (0x80020fb0 : Word).getLsbD 0 = false; decide) f80020fb0 fun o => ?_
    rw [exec_op]; rfl
  have v30 : c20.get 30 = g.get 30 := by simp [c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have s21 : DetStep B img ⟨c20, R3⟩ ⟨c21, R4⟩ := by
    refine detStep_of (by show (0x80020fb2 : Word).getLsbD 0 = false; decide) f80020fb2 fun o => ?_
    rw [exec_store, v30, BitVec.add_zero, interp_store_ram (w := .w) o hD hDr]; rfl
  have k1 : c1.sameCsr g := (Core.sameCsr_goto _ _)
  have k2 : c2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : c3.sameCsr g := (Core.sameCsr_goto _ _).trans k2
  have k4 : c4.sameCsr g := (Core.sameCsr_goto _ _).trans k3
  have k5 : c5.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : c7.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k6
  have k8 : c8.sameCsr g := (Core.sameCsr_goto _ _).trans k7
  have k9 : c9.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : c10.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k9
  have k11 : c11.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k10
  have k12 : c12.sameCsr g := (Core.sameCsr_goto _ _).trans k11
  have k13 : c13.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k12
  have k14 : c14.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k13
  have k15 : c15.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k14
  have k16 : c16.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k15
  have k17 : c17.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k16
  have k18 : c18.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k17
  have k19 : c19.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k18
  have k20 : c20.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k19
  have k21 : c21.sameCsr g := (Core.sameCsr_goto _ _).trans k20
  have run : QRun B img 21 ⟨g, R0⟩ ⟨c21, R4⟩ :=
    .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5 (.step (q _ k5) s6 (.step (q _ k6) s7 (.step (q _ k7) s8 (.step (q _ k8) s9 (.step (q _ k9) s10 (.step (q _ k10) s11 (.step (q _ k11) s12 (.step (q _ k12) s13 (.step (q _ k13) s14 (.step (q _ k14) s15 (.step (q _ k15) s16 (.step (q _ k16) s17 (.step (q _ k17) s18 (.step (q _ k18) s19 (.step (q _ k19) s20 (.single (q _ k20) s21))))))))))))))))))))
  have hR2 : ∀ x, x ≠ g.get 2 + 0x10#32 → x ≠ g.get 2 + 0xe#32 → R2 x = R0 x := by
    intro x h1 h2
    show ramWrite (ramWrite R0 (g.get 2 + 0x10#32) (g.get 0) .b) (c2.get 2 + 0xe#32) (c2.get 0) .b x = R0 x
    rw [g2 c2 (by simp)]; simp only [ramWrite, ramPut, if_neg h1, if_neg h2]
  have hR3 : ∀ x, x ≠ g.get 2 + 0x10#32 → x ≠ g.get 2 + 0xe#32 → R3 x = R0 x := by
    intro x h1 h2
    show ramWrite R2 (c7.get 2 + 0x10#32) (c7.get 6) .b x = R0 x
    rw [g2 c7 (by simp)]; simp only [ramWrite, ramPut, if_neg h1]; exact hR2 x h1 h2
  refine ⟨c21, R4, run, ⟨rfl, k21, ⟨R3, hR3, ?_⟩, ?_⟩⟩
  · show ramWrite R3 (g.get 30) (c20.get 11) .w = _
    rw [vval]
    obtain ⟨a0, a1, -⟩ := asm_byte b0 b1 0 (lbu_lt _ _) (lbu_lt _ _) (by decide)
    apply merge_store_q R0 R3 _ _ _ _ 2 (by decide) hprev
    intro j hj
    have hs0 := hsep 0 (by decide)
    have hs1 := hsep 1 (by decide)
    rw [show g.get 11 + 4#32 + BitVec.ofNat 32 0 = g.get 11 + 0x4#32 by bv_omega] at hs0
    rw [show g.get 11 + 4#32 + BitVec.ofNat 32 1 = g.get 11 + 0x5#32 by bv_omega] at hs1
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [a0, lbu_byte, hR2 _ hs0.1 hs0.2]; congr 1; bv_omega
    · rw [a1, lbu_byte, hR2 _ hs1.1 hs1.2]; congr 1; bv_omega
  · intro r hr
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h7 : r ≠ 7 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h29 : r ≠ 29 := fun e => hr (by subst e; decide)
    simp [c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h6, h7, h11, h12, h14, h29]

/-- o = 3: two bytes loaded directly, the third through the temporary sp+0xe. -/
theorem end3 (g : Core) (R0 : Word → BitVec 8) (hpc : g.pc = 0x80020f4c) (hq : Quiet g)
    (h6 : g.get 6 = BitVec.ofNat 32 3) (h28 : g.get 28 = BitVec.ofNat 32 (8 * 3))
    (h5 : (g.get 5).toNat % 2 = 1)
    (hprev : ∀ k, 3 ≤ k → k < 4 → byteOf (g.get 15) k = R0 (g.get 11 + BitVec.ofNat 32 k))
    (hsrc : B.inRam (g.get 11 + 4#32) 3 = true)
    (ht10 : B.inRam (g.get 2 + 0x10#32) 1 = true) (ht0e : B.inRam (g.get 2 + 0xe#32) 1 = true)
    (hsep : ∀ j < 3, g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0x10#32 ∧
      g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0xe#32)
    (hD : (g.get 30).toNat % 4 = 0) (hDr : B.inRam (g.get 30) 4 = true) :
    ∃ g' R', QRun B img 27 ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtTail g g' R0 R' 3 := by
  let R1 := ramWrite R0 (g.get 2 + 0x10#32) (g.get 0) .b
  let c1 := g.goto 0x80020f50
  let c2 := c1.wr 12 (alu .add (c1.get 0) 0x1#32) 0x80020f52
  let R2 := ramWrite R1 (c2.get 2 + 0xe#32) (c2.get 0) .b
  let c3 := c2.goto 0x80020f56
  let c4 := c3.goto 0x80020f7e
  let c5 := c4.wr 6 (extend .b false (ramRead R2 (c4.get 11 + 0x4#32) .b)) 0x80020f82
  let c6 := c5.wr 7 (extend .b false (ramRead R2 (c5.get 11 + 0x5#32) .b)) 0x80020f86
  let c7 := c6.wr 29 (alu .add (c6.get 0) 0x2#32) 0x80020f88
  let R3 := ramWrite R2 (c7.get 2 + 0x10#32) (c7.get 6) .b
  let c8 := c7.goto 0x80020f8c
  let c9 := c8.wr 7 (alu .sll (c8.get 7) 0x8#32) 0x80020f8e
  let c10 := c9.wr 12 (alu .add (c9.get 2) 0xe#32) 0x80020f92
  let c11 := c10.wr 14 (alu .and (c10.get 5) 0x1#32) 0x80020f96
  let c12 := c11.goto 0x80020f68
  let c13 := c12.wr 11 (alu .add (c12.get 11) (c12.get 29)) 0x80020f6a
  let c14 := c13.wr 11 (extend .b false (ramRead R3 (c13.get 11 + 0x4#32) .b)) 0x80020f6e
  let R4 := ramWrite R3 (g.get 2 + 0xe#32) (c14.get 11) .b
  let c15 := c14.goto 0x80020f72
  let c16 := c15.wr 11 (extend .b false (ramRead R4 (c15.get 2 + 0xe#32) .b)) 0x80020f76
  let c17 := c16.wr 6 (extend .b false (ramRead R4 (c16.get 2 + 0x10#32) .b)) 0x80020f7a
  let c18 := c17.wr 11 (alu .sll (c17.get 11) 0x10#32) 0x80020f7c
  let c19 := c18.goto 0x80020f9a
  let c20 := c19.wr 11 (alu .or (c19.get 7) (c19.get 11)) 0x80020f9e
  let c21 := c20.wr 12 (alu .srl (c20.get 15) (c20.get 28)) 0x80020fa2
  let c22 := c21.wr 14 (alu .sub (c21.get 0) (c21.get 28)) 0x80020fa6
  let c23 := c22.wr 11 (alu .or (c22.get 11) (c22.get 6)) 0x80020faa
  let c24 := c23.wr 14 (alu .and (c23.get 14) 0x18#32) 0x80020fac
  let c25 := c24.wr 11 (alu .sll (c24.get 11) (c24.get 14)) 0x80020fb0
  let c26 := c25.wr 11 (alu .or (c25.get 11) (c25.get 12)) 0x80020fb2
  let R5 := ramWrite R4 (g.get 30) (c26.get 11) .w
  let c27 := c26.goto 0x80020fb6
  have g2 : ∀ d : Core, (d = c2 ∨ d = c7 ∨ d = c9 ∨ d = c15 ∨ d = c16) → d.get 2 = g.get 2 := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      simp [c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have g11 : ∀ d : Core, (d = c4 ∨ d = c5) → d.get 11 = g.get 11 := by
    intro d hd; rcases hd with rfl | rfl <;> simp [c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v12 : c3.get 12 = 1 := by simp [c3, c2, Core.wr_get_self, alu]
  have v6 : c3.get 6 = BitVec.ofNat 32 3 := by simp [c3, c2, c1, Core.wr_get_ne, h6]
  have v14 : c11.get 14 = 1 := by
    simp only [c11, Core.wr_get_self _ (14 : Reg) _ _ (by decide), alu]
    have : c10.get 5 = g.get 5 := by simp [c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
    rw [this]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x1#32 : Word).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h5
  have v13 : c13.get 11 = g.get 11 + 2 := by
    simp (config := { decide := true }) only [c13, c12, c11, c10, c9, c8, c7, Core.goto_get, Core.wr_get, alu,
      if_true, if_false]
    have : c6.get 11 = g.get 11 := by simp [c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
    rw [this, Core.get_zero]; bv_omega
  have v14_12 : c14.get 12 = g.get 2 + 0xe#32 := by
    simp (config := { decide := true }) only [c14, c13, c12, c11, c10, Core.goto_get, Core.wr_get, alu,
      if_true, if_false]
    rw [g2 c9 (by simp)]
  let b0 := extend .b false (ramRead R2 (g.get 11 + 0x4#32) .b)
  let b1 := extend .b false (ramRead R2 (g.get 11 + 0x5#32) .b)
  let b2 := extend .b false (ramRead R4 (g.get 2 + 0xe#32) .b)
  let b0' := extend .b false (ramRead R4 (g.get 2 + 0x10#32) .b)
  have vval : c26.get 11 = (g.get 15 >>> (8 * 3)) ||| (((b1 <<< 8) ||| (b2 <<< 16) ||| b0') <<< (32 - 8 * 3)) := by
    have e5 : c5.get 11 = g.get 11 := g11 c5 (by simp)
    have e4 : c4.get 11 = g.get 11 := g11 c4 (by simp)
    have e15 : c15.get 2 = g.get 2 := g2 c15 (by simp)
    have e16 : c16.get 2 = g.get 2 := g2 c16 (by simp)
    simp (config := { decide := true }) only [c26, c25, c24, c23, c22, c21, c20, c19, c18, c17, c16, Core.goto_get,
      Core.wr_get, alu, e15, e16, if_true, if_false]
    have f28 : c15.get 28 = BitVec.ofNat 32 (8 * 3) := by
      simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h28]
    have f15 : c15.get 15 = g.get 15 := by
      simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
    have f7 : c15.get 7 = b1 <<< 8 := by
      simp (config := { decide := true }) only [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, Core.goto_get,
        Core.wr_get, alu, e5, if_true, if_false]; rfl
    obtain ⟨e1, e2⟩ := shifts 3 (by decide)
    rw [f28, f15, f7, e1, e2, show (0x10#32 : Word).toNat % 32 = 16 from rfl]
    exact BitVec.or_comm _ _
  have hsr := (B_ram _ _).mp hsrc
  have hs0 : B.inRam (g.get 11 + 0x4#32) 1 = true := by rw [B_ram]; constructor <;> bv_omega
  have hs1 : B.inRam (g.get 11 + 0x5#32) 1 = true := by rw [B_ram]; constructor <;> bv_omega
  have hs2 : B.inRam (g.get 11 + 2 + 0x4#32) 1 = true := by rw [B_ram]; constructor <;> bv_omega
  have q : ∀ d : Core, d.sameCsr g → Quiet d := fun d h => Quiet.of_sameCsr h hq
  have m1 : ∀ x : Word, x.toNat % (Width.b).bytes = 0 := fun x => by simp only [Width.bytes, Nat.mod_one]
  have s1 : DetStep B img ⟨g, R0⟩ ⟨c1, R1⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020f4c) fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (m1 _) ht10, hpc]; rfl
  have s2 : DetStep B img ⟨c1, R1⟩ ⟨c2, R1⟩ := by
    refine detStep_of (by show (0x80020f50 : Word).getLsbD 0 = false; decide) f80020f50 fun o => ?_
    rw [exec_opimm]; rfl
  have s3 : DetStep B img ⟨c2, R1⟩ ⟨c3, R2⟩ := by
    refine detStep_of (by show (0x80020f52 : Word).getLsbD 0 = false; decide) f80020f52 fun o => ?_
    rw [exec_store, g2 c2 (by simp), interp_store_ram (w := .b) o (m1 _) ht0e, ← g2 c2 (by simp)]; rfl
  have s4 : DetStep B img ⟨c3, R2⟩ ⟨c4, R2⟩ := by
    refine detStep_of (by show (0x80020f56 : Word).getLsbD 0 = false; decide) f80020f56 fun o => ?_
    rw [exec_branch, v6, v12]
    simp only [taken, show (BitVec.ofNat 32 3 != (1 : Word)) = true by decide, if_true]
    rw [show c3.pc + 0x28#32 = 0x80020f7e by rw [show c3.pc = 0x80020f56 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s5 : DetStep B img ⟨c4, R2⟩ ⟨c5, R2⟩ := by
    refine detStep_of (by show (0x80020f7e : Word).getLsbD 0 = false; decide) f80020f7e fun o => ?_
    rw [exec_load, g11 c4 (by simp), interp_load_ram (w := .b) o (m1 _) hs0, ← g11 c4 (by simp)]; rfl
  have s6 : DetStep B img ⟨c5, R2⟩ ⟨c6, R2⟩ := by
    refine detStep_of (by show (0x80020f82 : Word).getLsbD 0 = false; decide) f80020f82 fun o => ?_
    rw [exec_load, g11 c5 (by simp), interp_load_ram (w := .b) o (m1 _) hs1, ← g11 c5 (by simp)]; rfl
  have s7 : DetStep B img ⟨c6, R2⟩ ⟨c7, R2⟩ := by
    refine detStep_of (by show (0x80020f86 : Word).getLsbD 0 = false; decide) f80020f86 fun o => ?_
    rw [exec_opimm]; rfl
  have s8 : DetStep B img ⟨c7, R2⟩ ⟨c8, R3⟩ := by
    refine detStep_of (by show (0x80020f88 : Word).getLsbD 0 = false; decide) f80020f88 fun o => ?_
    rw [exec_store, g2 c7 (by simp), interp_store_ram (w := .b) o (m1 _) ht10, ← g2 c7 (by simp)]; rfl
  have s9 : DetStep B img ⟨c8, R3⟩ ⟨c9, R3⟩ := by
    refine detStep_of (by show (0x80020f8c : Word).getLsbD 0 = false; decide) f80020f8c fun o => ?_
    rw [exec_opimm]; rfl
  have s10 : DetStep B img ⟨c9, R3⟩ ⟨c10, R3⟩ := by
    refine detStep_of (by show (0x80020f8e : Word).getLsbD 0 = false; decide) f80020f8e fun o => ?_
    rw [exec_opimm]; rfl
  have s11 : DetStep B img ⟨c10, R3⟩ ⟨c11, R3⟩ := by
    refine detStep_of (by show (0x80020f92 : Word).getLsbD 0 = false; decide) f80020f92 fun o => ?_
    rw [exec_opimm]; rfl
  have s12 : DetStep B img ⟨c11, R3⟩ ⟨c12, R3⟩ := by
    refine detStep_of (by show (0x80020f96 : Word).getLsbD 0 = false; decide) f80020f96 fun o => ?_
    rw [exec_branch, v14, Core.get_zero]
    simp only [taken, show ((1 : Word) != 0) = true by decide, if_true]
    rw [show c11.pc + 0xffffffd2#32 = 0x80020f68 by rw [show c11.pc = 0x80020f96 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s13 : DetStep B img ⟨c12, R3⟩ ⟨c13, R3⟩ := by
    refine detStep_of (by show (0x80020f68 : Word).getLsbD 0 = false; decide) f80020f68 fun o => ?_
    rw [exec_op]; rfl
  have s14 : DetStep B img ⟨c13, R3⟩ ⟨c14, R3⟩ := by
    refine detStep_of (by show (0x80020f6a : Word).getLsbD 0 = false; decide) f80020f6a fun o => ?_
    rw [exec_load, v13, interp_load_ram (w := .b) o (m1 _) hs2, ← v13]; rfl
  have s15 : DetStep B img ⟨c14, R3⟩ ⟨c15, R4⟩ := by
    refine detStep_of (by show (0x80020f6e : Word).getLsbD 0 = false; decide) f80020f6e fun o => ?_
    rw [exec_store, v14_12, BitVec.add_zero, interp_store_ram (w := .b) o (m1 _) ht0e]; rfl
  have s16 : DetStep B img ⟨c15, R4⟩ ⟨c16, R4⟩ := by
    refine detStep_of (by show (0x80020f72 : Word).getLsbD 0 = false; decide) f80020f72 fun o => ?_
    rw [exec_load, g2 c15 (by simp), interp_load_ram (w := .b) o (m1 _) ht0e, ← g2 c15 (by simp)]; rfl
  have s17 : DetStep B img ⟨c16, R4⟩ ⟨c17, R4⟩ := by
    refine detStep_of (by show (0x80020f76 : Word).getLsbD 0 = false; decide) f80020f76 fun o => ?_
    rw [exec_load, g2 c16 (by simp), interp_load_ram (w := .b) o (m1 _) ht10, ← g2 c16 (by simp)]; rfl
  have s18 : DetStep B img ⟨c17, R4⟩ ⟨c18, R4⟩ := by
    refine detStep_of (by show (0x80020f7a : Word).getLsbD 0 = false; decide) f80020f7a fun o => ?_
    rw [exec_opimm]; rfl
  have s19 : DetStep B img ⟨c18, R4⟩ ⟨c19, R4⟩ := by
    refine detStep_of (by show (0x80020f7c : Word).getLsbD 0 = false; decide) f80020f7c fun o => ?_
    rw [exec_jal, Core.set_zero,
      show c18.pc + 0x1e#32 = 0x80020f9a by rw [show c18.pc = 0x80020f7c from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s20 : DetStep B img ⟨c19, R4⟩ ⟨c20, R4⟩ := by
    refine detStep_of (by show (0x80020f9a : Word).getLsbD 0 = false; decide) f80020f9a fun o => ?_
    rw [exec_op]; rfl
  have s21 : DetStep B img ⟨c20, R4⟩ ⟨c21, R4⟩ := by
    refine detStep_of (by show (0x80020f9e : Word).getLsbD 0 = false; decide) f80020f9e fun o => ?_
    rw [exec_op]; rfl
  have s22 : DetStep B img ⟨c21, R4⟩ ⟨c22, R4⟩ := by
    refine detStep_of (by show (0x80020fa2 : Word).getLsbD 0 = false; decide) f80020fa2 fun o => ?_
    rw [exec_op]; rfl
  have s23 : DetStep B img ⟨c22, R4⟩ ⟨c23, R4⟩ := by
    refine detStep_of (by show (0x80020fa6 : Word).getLsbD 0 = false; decide) f80020fa6 fun o => ?_
    rw [exec_op]; rfl
  have s24 : DetStep B img ⟨c23, R4⟩ ⟨c24, R4⟩ := by
    refine detStep_of (by show (0x80020faa : Word).getLsbD 0 = false; decide) f80020faa fun o => ?_
    rw [exec_opimm]; rfl
  have s25 : DetStep B img ⟨c24, R4⟩ ⟨c25, R4⟩ := by
    refine detStep_of (by show (0x80020fac : Word).getLsbD 0 = false; decide) f80020fac fun o => ?_
    rw [exec_op]; rfl
  have s26 : DetStep B img ⟨c25, R4⟩ ⟨c26, R4⟩ := by
    refine detStep_of (by show (0x80020fb0 : Word).getLsbD 0 = false; decide) f80020fb0 fun o => ?_
    rw [exec_op]; rfl
  have v30 : c26.get 30 = g.get 30 := by simp [c27, c26, c25, c24, c23, c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have s27 : DetStep B img ⟨c26, R4⟩ ⟨c27, R5⟩ := by
    refine detStep_of (by show (0x80020fb2 : Word).getLsbD 0 = false; decide) f80020fb2 fun o => ?_
    rw [exec_store, v30, BitVec.add_zero, interp_store_ram (w := .w) o hD hDr]; rfl
  have k1 : c1.sameCsr g := (Core.sameCsr_goto _ _)
  have k2 : c2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : c3.sameCsr g := (Core.sameCsr_goto _ _).trans k2
  have k4 : c4.sameCsr g := (Core.sameCsr_goto _ _).trans k3
  have k5 : c5.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : c7.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k6
  have k8 : c8.sameCsr g := (Core.sameCsr_goto _ _).trans k7
  have k9 : c9.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : c10.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k9
  have k11 : c11.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k10
  have k12 : c12.sameCsr g := (Core.sameCsr_goto _ _).trans k11
  have k13 : c13.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k12
  have k14 : c14.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k13
  have k15 : c15.sameCsr g := (Core.sameCsr_goto _ _).trans k14
  have k16 : c16.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k15
  have k17 : c17.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k16
  have k18 : c18.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k17
  have k19 : c19.sameCsr g := (Core.sameCsr_goto _ _).trans k18
  have k20 : c20.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k19
  have k21 : c21.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k20
  have k22 : c22.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k21
  have k23 : c23.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k22
  have k24 : c24.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k23
  have k25 : c25.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k24
  have k26 : c26.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k25
  have k27 : c27.sameCsr g := (Core.sameCsr_goto _ _).trans k26
  have run : QRun B img 27 ⟨g, R0⟩ ⟨c27, R5⟩ :=
    .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5 (.step (q _ k5) s6 (.step (q _ k6) s7 (.step (q _ k7) s8 (.step (q _ k8) s9 (.step (q _ k9) s10 (.step (q _ k10) s11 (.step (q _ k11) s12 (.step (q _ k12) s13 (.step (q _ k13) s14 (.step (q _ k14) s15 (.step (q _ k15) s16 (.step (q _ k16) s17 (.step (q _ k17) s18 (.step (q _ k18) s19 (.step (q _ k19) s20 (.step (q _ k20) s21 (.step (q _ k21) s22 (.step (q _ k22) s23 (.step (q _ k23) s24 (.step (q _ k24) s25 (.step (q _ k25) s26 (.single (q _ k26) s27))))))))))))))))))))))))))
  have tne : g.get 2 + 0x10#32 ≠ g.get 2 + 0xe#32 := by bv_omega
  have hR2 : ∀ x, x ≠ g.get 2 + 0x10#32 → x ≠ g.get 2 + 0xe#32 → R2 x = R0 x := by
    intro x h1 h2
    show ramWrite (ramWrite R0 (g.get 2 + 0x10#32) (g.get 0) .b) (c2.get 2 + 0xe#32) (c2.get 0) .b x = R0 x
    rw [g2 c2 (by simp)]; simp only [ramWrite, ramPut, if_neg h1, if_neg h2]
  have hR3 : ∀ x, x ≠ g.get 2 + 0x10#32 → x ≠ g.get 2 + 0xe#32 → R3 x = R0 x := by
    intro x h1 h2
    show ramWrite R2 (c7.get 2 + 0x10#32) (c7.get 6) .b x = R0 x
    rw [g2 c7 (by simp)]; simp only [ramWrite, ramPut, if_neg h1]; exact hR2 x h1 h2
  have hR4 : ∀ x, x ≠ g.get 2 + 0x10#32 → x ≠ g.get 2 + 0xe#32 → R4 x = R0 x := by
    intro x h1 h2
    show ramWrite R3 (g.get 2 + 0xe#32) (c14.get 11) .b x = R0 x
    simp only [ramWrite, ramPut, if_neg h2]; exact hR3 x h1 h2
  refine ⟨c27, R5, run, ⟨rfl, k27, ⟨R4, hR4, ?_⟩, ?_⟩⟩
  · show ramWrite R4 (g.get 30) (c26.get 11) .w = _
    rw [vval]
    obtain ⟨a0, a1, a2⟩ := asm_byte b0' b1 b2 (lbu_lt _ _) (lbu_lt _ _) (lbu_lt _ _)
    apply merge_store_q R0 R4 _ _ _ _ 3 (by decide) hprev
    intro j hj
    have hs0 := hsep 0 (by decide)
    have hs1 := hsep 1 (by decide)
    have hs2 := hsep 2 (by decide)
    rw [show g.get 11 + 4#32 + BitVec.ofNat 32 0 = g.get 11 + 0x4#32 by bv_omega] at hs0
    rw [show g.get 11 + 4#32 + BitVec.ofNat 32 1 = g.get 11 + 0x5#32 by bv_omega] at hs1
    rw [show g.get 11 + 4#32 + BitVec.ofNat 32 2 = g.get 11 + 2 + 0x4#32 by bv_omega] at hs2
    have r4_10 : R4 (g.get 2 + 0x10#32) = R3 (g.get 2 + 0x10#32) := by
      show ramWrite R3 (g.get 2 + 0xe#32) (c14.get 11) .b _ = _
      simp only [ramWrite, ramPut, if_neg tne]
    have r3_10 : R3 (g.get 2 + 0x10#32) = byteOf (c7.get 6) 0 := by
      show ramWrite R2 (c7.get 2 + 0x10#32) (c7.get 6) .b _ = _
      rw [g2 c7 (by simp)]; simp only [ramWrite, ramPut, if_pos rfl, ite_true]
    have c7_6 : c7.get 6 = b0 := by simp [c7, c6, c5, Core.wr_get_ne, Core.wr_get_self, g11 c4 (by simp), b0]
    have r4_e : R4 (g.get 2 + 0xe#32) = byteOf (c14.get 11) 0 := by
      show ramWrite R3 (g.get 2 + 0xe#32) (c14.get 11) .b _ = _
      simp only [ramWrite, ramPut, if_pos rfl, ite_true]
    have c14_11 : c14.get 11 = extend .b false (ramRead R3 (g.get 11 + 2 + 0x4#32) .b) := by
      simp only [c14, Core.wr_get_self _ (11 : Reg) _ _ (by decide)]; rw [v13]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [a0, lbu_byte, r4_10, r3_10, c7_6, lbu_byte, hR2 _ hs0.1 hs0.2]; congr 1; bv_omega
    · rw [a1, lbu_byte, hR2 _ hs1.1 hs1.2]; congr 1; bv_omega
    · rw [a2, lbu_byte, r4_e, c14_11, lbu_byte, hR3 _ hs2.1 hs2.2]; congr 1; bv_omega
  · intro r hr
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h7 : r ≠ 7 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h29 : r ≠ 29 := fun e => hr (by subst e; decide)
    simp [c27, c26, c25, c24, c23, c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h6, h7, h11, h12, h14, h29]

/-- o = 1: one byte, through the temporary sp+0x10. -/
theorem end1 (g : Core) (R0 : Word → BitVec 8) (hpc : g.pc = 0x80020f4c) (hq : Quiet g)
    (h6 : g.get 6 = BitVec.ofNat 32 1) (h28 : g.get 28 = BitVec.ofNat 32 (8 * 1))
    (h5 : (g.get 5).toNat % 2 = 1)
    (hprev : ∀ k, 1 ≤ k → k < 4 → byteOf (g.get 15) k = R0 (g.get 11 + BitVec.ofNat 32 k))
    (hsrc : B.inRam (g.get 11 + 4#32) 1 = true)
    (ht10 : B.inRam (g.get 2 + 0x10#32) 1 = true) (ht0e : B.inRam (g.get 2 + 0xe#32) 1 = true)
    (hsep : ∀ j < 1, g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0x10#32 ∧
      g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0xe#32)
    (hD : (g.get 30).toNat % 4 = 0) (hDr : B.inRam (g.get 30) 4 = true) :
    ∃ g' R', QRun B img 25 ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtTail g g' R0 R' 1 := by
  let R1 := ramWrite R0 (g.get 2 + 0x10#32) (g.get 0) .b
  let c1 := g.goto 0x80020f50
  let c2 := c1.wr 12 (alu .add (c1.get 0) 0x1#32) 0x80020f52
  let R2 := ramWrite R1 (c2.get 2 + 0xe#32) (c2.get 0) .b
  let c3 := c2.goto 0x80020f56
  let c4 := c3.goto 0x80020f5a
  let c5 := c4.wr 6 (alu .add (c4.get 0) 0x0#32) 0x80020f5c
  let c6 := c5.wr 7 (alu .add (c5.get 0) 0x0#32) 0x80020f5e
  let c7 := c6.wr 29 (alu .add (c6.get 0) 0x0#32) 0x80020f60
  let c8 := c7.wr 12 (alu .add (c7.get 2) 0x10#32) 0x80020f62
  let c9 := c8.wr 14 (alu .and (c8.get 5) 0x1#32) 0x80020f66
  let c10 := c9.goto 0x80020f68
  let c11 := c10.wr 11 (alu .add (c10.get 11) (c10.get 29)) 0x80020f6a
  let c12 := c11.wr 11 (extend .b false (ramRead R2 (c11.get 11 + 0x4#32) .b)) 0x80020f6e
  let R3 := ramWrite R2 (g.get 2 + 0x10#32) (c12.get 11) .b
  let c13 := c12.goto 0x80020f72
  let c14 := c13.wr 11 (extend .b false (ramRead R3 (c13.get 2 + 0xe#32) .b)) 0x80020f76
  let c15 := c14.wr 6 (extend .b false (ramRead R3 (c14.get 2 + 0x10#32) .b)) 0x80020f7a
  let c16 := c15.wr 11 (alu .sll (c15.get 11) 0x10#32) 0x80020f7c
  let c17 := c16.goto 0x80020f9a
  let c18 := c17.wr 11 (alu .or (c17.get 7) (c17.get 11)) 0x80020f9e
  let c19 := c18.wr 12 (alu .srl (c18.get 15) (c18.get 28)) 0x80020fa2
  let c20 := c19.wr 14 (alu .sub (c19.get 0) (c19.get 28)) 0x80020fa6
  let c21 := c20.wr 11 (alu .or (c20.get 11) (c20.get 6)) 0x80020faa
  let c22 := c21.wr 14 (alu .and (c21.get 14) 0x18#32) 0x80020fac
  let c23 := c22.wr 11 (alu .sll (c22.get 11) (c22.get 14)) 0x80020fb0
  let c24 := c23.wr 11 (alu .or (c23.get 11) (c23.get 12)) 0x80020fb2
  let R4 := ramWrite R3 (g.get 30) (c24.get 11) .w
  let c25 := c24.goto 0x80020fb6
  have g2 : ∀ d : Core, (d = c2 ∨ d = c7 ∨ d = c13 ∨ d = c14) → d.get 2 = g.get 2 := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl <;>
      simp [c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have v12 : c3.get 12 = 1 := by simp [c3, c2, Core.wr_get_self, alu]
  have v6 : c3.get 6 = BitVec.ofNat 32 1 := by simp [c3, c2, c1, Core.wr_get_ne, h6]
  have v14 : c9.get 14 = 1 := by
    simp only [c9, Core.wr_get_self _ (14 : Reg) _ _ (by decide), alu]
    have : c8.get 5 = g.get 5 := by simp [c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
    rw [this]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x1#32 : Word).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h5
  have v11 : c11.get 11 = g.get 11 := by
    simp (config := { decide := true }) only [c11, c10, c9, c8, c7, Core.goto_get, Core.wr_get, alu,
      if_true, if_false]
    have : c6.get 11 = g.get 11 := by simp [c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
    rw [this, Core.get_zero]; bv_omega
  have v12_12 : c12.get 12 = g.get 2 + 0x10#32 := by
    simp (config := { decide := true }) only [c12, c11, c10, c9, c8, Core.goto_get, Core.wr_get, alu,
      if_true, if_false]
    rw [g2 c7 (by simp)]
  let x := extend .b false (ramRead R3 (g.get 2 + 0x10#32) .b)
  let z := extend .b false (ramRead R3 (g.get 2 + 0xe#32) .b)
  have vval : c24.get 11 = (g.get 15 >>> (8 * 1)) ||| ((((0 : Word) <<< 8) ||| (z <<< 16) ||| x) <<< (32 - 8 * 1)) := by
    have e13 : c13.get 2 = g.get 2 := g2 c13 (by simp)
    have e14 : c14.get 2 = g.get 2 := g2 c14 (by simp)
    simp (config := { decide := true }) only [c24, c23, c22, c21, c20, c19, c18, c17, c16, c15, c14, Core.goto_get,
      Core.wr_get, alu, e13, e14, if_true, if_false]
    have f28 : c13.get 28 = BitVec.ofNat 32 (8 * 1) := by
      simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h28]
    have f15 : c13.get 15 = g.get 15 := by
      simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
    have f7 : c13.get 7 = 0 := by
      simp (config := { decide := true }) only [c13, c12, c11, c10, c9, c8, c7, c6, Core.goto_get,
        Core.wr_get, alu, if_true, if_false]; rfl
    obtain ⟨e1, e2⟩ := shifts 1 (by decide)
    rw [f28, f15, f7, e1, e2, show (0x10#32 : Word).toNat % 32 = 16 from rfl, show (0 : Word) <<< 8 = 0 from rfl]
    exact BitVec.or_comm _ _
  have hsr := (B_ram _ _).mp hsrc
  have hs0 : B.inRam (g.get 11 + 0x4#32) 1 = true := by simpa using hsrc
  have q : ∀ d : Core, d.sameCsr g → Quiet d := fun d h => Quiet.of_sameCsr h hq
  have m1 : ∀ x : Word, x.toNat % (Width.b).bytes = 0 := fun x => by simp only [Width.bytes, Nat.mod_one]
  have s1 : DetStep B img ⟨g, R0⟩ ⟨c1, R1⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020f4c) fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (m1 _) ht10, hpc]; rfl
  have s2 : DetStep B img ⟨c1, R1⟩ ⟨c2, R1⟩ := by
    refine detStep_of (by show (0x80020f50 : Word).getLsbD 0 = false; decide) f80020f50 fun o => ?_
    rw [exec_opimm]; rfl
  have s3 : DetStep B img ⟨c2, R1⟩ ⟨c3, R2⟩ := by
    refine detStep_of (by show (0x80020f52 : Word).getLsbD 0 = false; decide) f80020f52 fun o => ?_
    rw [exec_store, g2 c2 (by simp), interp_store_ram (w := .b) o (m1 _) ht0e, ← g2 c2 (by simp)]; rfl
  have s4 : DetStep B img ⟨c3, R2⟩ ⟨c4, R2⟩ := by
    refine detStep_of (by show (0x80020f56 : Word).getLsbD 0 = false; decide) f80020f56 fun o => ?_
    rw [exec_branch, v6, v12]
    simp only [taken, show (BitVec.ofNat 32 1 != (1 : Word)) = false by decide, Bool.false_eq_true, if_false]
    rfl
  have s5 : DetStep B img ⟨c4, R2⟩ ⟨c5, R2⟩ := by
    refine detStep_of (by show (0x80020f5a : Word).getLsbD 0 = false; decide) f80020f5a fun o => ?_
    rw [exec_opimm]; rfl
  have s6 : DetStep B img ⟨c5, R2⟩ ⟨c6, R2⟩ := by
    refine detStep_of (by show (0x80020f5c : Word).getLsbD 0 = false; decide) f80020f5c fun o => ?_
    rw [exec_opimm]; rfl
  have s7 : DetStep B img ⟨c6, R2⟩ ⟨c7, R2⟩ := by
    refine detStep_of (by show (0x80020f5e : Word).getLsbD 0 = false; decide) f80020f5e fun o => ?_
    rw [exec_opimm]; rfl
  have s8 : DetStep B img ⟨c7, R2⟩ ⟨c8, R2⟩ := by
    refine detStep_of (by show (0x80020f60 : Word).getLsbD 0 = false; decide) f80020f60 fun o => ?_
    rw [exec_opimm]; rfl
  have s9 : DetStep B img ⟨c8, R2⟩ ⟨c9, R2⟩ := by
    refine detStep_of (by show (0x80020f62 : Word).getLsbD 0 = false; decide) f80020f62 fun o => ?_
    rw [exec_opimm]; rfl
  have s10 : DetStep B img ⟨c9, R2⟩ ⟨c10, R2⟩ := by
    refine detStep_of (by show (0x80020f66 : Word).getLsbD 0 = false; decide) f80020f66 fun o => ?_
    rw [exec_branch, v14, Core.get_zero]
    simp only [taken, show ((1 : Word) == 0) = false by decide, Bool.false_eq_true, if_false]; rfl
  have s11 : DetStep B img ⟨c10, R2⟩ ⟨c11, R2⟩ := by
    refine detStep_of (by show (0x80020f68 : Word).getLsbD 0 = false; decide) f80020f68 fun o => ?_
    rw [exec_op]; rfl
  have s12 : DetStep B img ⟨c11, R2⟩ ⟨c12, R2⟩ := by
    refine detStep_of (by show (0x80020f6a : Word).getLsbD 0 = false; decide) f80020f6a fun o => ?_
    rw [exec_load, v11, interp_load_ram (w := .b) o (m1 _) hs0, ← v11]; rfl
  have s13 : DetStep B img ⟨c12, R2⟩ ⟨c13, R3⟩ := by
    refine detStep_of (by show (0x80020f6e : Word).getLsbD 0 = false; decide) f80020f6e fun o => ?_
    rw [exec_store, v12_12, BitVec.add_zero, interp_store_ram (w := .b) o (m1 _) ht10]; rfl
  have s14 : DetStep B img ⟨c13, R3⟩ ⟨c14, R3⟩ := by
    refine detStep_of (by show (0x80020f72 : Word).getLsbD 0 = false; decide) f80020f72 fun o => ?_
    rw [exec_load, g2 c13 (by simp), interp_load_ram (w := .b) o (m1 _) ht0e, ← g2 c13 (by simp)]; rfl
  have s15 : DetStep B img ⟨c14, R3⟩ ⟨c15, R3⟩ := by
    refine detStep_of (by show (0x80020f76 : Word).getLsbD 0 = false; decide) f80020f76 fun o => ?_
    rw [exec_load, g2 c14 (by simp), interp_load_ram (w := .b) o (m1 _) ht10, ← g2 c14 (by simp)]; rfl
  have s16 : DetStep B img ⟨c15, R3⟩ ⟨c16, R3⟩ := by
    refine detStep_of (by show (0x80020f7a : Word).getLsbD 0 = false; decide) f80020f7a fun o => ?_
    rw [exec_opimm]; rfl
  have s17 : DetStep B img ⟨c16, R3⟩ ⟨c17, R3⟩ := by
    refine detStep_of (by show (0x80020f7c : Word).getLsbD 0 = false; decide) f80020f7c fun o => ?_
    rw [exec_jal, Core.set_zero,
      show c16.pc + 0x1e#32 = 0x80020f9a by rw [show c16.pc = 0x80020f7c from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s18 : DetStep B img ⟨c17, R3⟩ ⟨c18, R3⟩ := by
    refine detStep_of (by show (0x80020f9a : Word).getLsbD 0 = false; decide) f80020f9a fun o => ?_
    rw [exec_op]; rfl
  have s19 : DetStep B img ⟨c18, R3⟩ ⟨c19, R3⟩ := by
    refine detStep_of (by show (0x80020f9e : Word).getLsbD 0 = false; decide) f80020f9e fun o => ?_
    rw [exec_op]; rfl
  have s20 : DetStep B img ⟨c19, R3⟩ ⟨c20, R3⟩ := by
    refine detStep_of (by show (0x80020fa2 : Word).getLsbD 0 = false; decide) f80020fa2 fun o => ?_
    rw [exec_op]; rfl
  have s21 : DetStep B img ⟨c20, R3⟩ ⟨c21, R3⟩ := by
    refine detStep_of (by show (0x80020fa6 : Word).getLsbD 0 = false; decide) f80020fa6 fun o => ?_
    rw [exec_op]; rfl
  have s22 : DetStep B img ⟨c21, R3⟩ ⟨c22, R3⟩ := by
    refine detStep_of (by show (0x80020faa : Word).getLsbD 0 = false; decide) f80020faa fun o => ?_
    rw [exec_opimm]; rfl
  have s23 : DetStep B img ⟨c22, R3⟩ ⟨c23, R3⟩ := by
    refine detStep_of (by show (0x80020fac : Word).getLsbD 0 = false; decide) f80020fac fun o => ?_
    rw [exec_op]; rfl
  have s24 : DetStep B img ⟨c23, R3⟩ ⟨c24, R3⟩ := by
    refine detStep_of (by show (0x80020fb0 : Word).getLsbD 0 = false; decide) f80020fb0 fun o => ?_
    rw [exec_op]; rfl
  have v30 : c24.get 30 = g.get 30 := by simp [c25, c24, c23, c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]
  have s25 : DetStep B img ⟨c24, R3⟩ ⟨c25, R4⟩ := by
    refine detStep_of (by show (0x80020fb2 : Word).getLsbD 0 = false; decide) f80020fb2 fun o => ?_
    rw [exec_store, v30, BitVec.add_zero, interp_store_ram (w := .w) o hD hDr]; rfl
  have k1 : c1.sameCsr g := (Core.sameCsr_goto _ _)
  have k2 : c2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : c3.sameCsr g := (Core.sameCsr_goto _ _).trans k2
  have k4 : c4.sameCsr g := (Core.sameCsr_goto _ _).trans k3
  have k5 : c5.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : c7.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k6
  have k8 : c8.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k7
  have k9 : c9.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : c10.sameCsr g := (Core.sameCsr_goto _ _).trans k9
  have k11 : c11.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k10
  have k12 : c12.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k11
  have k13 : c13.sameCsr g := (Core.sameCsr_goto _ _).trans k12
  have k14 : c14.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k13
  have k15 : c15.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k14
  have k16 : c16.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k15
  have k17 : c17.sameCsr g := (Core.sameCsr_goto _ _).trans k16
  have k18 : c18.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k17
  have k19 : c19.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k18
  have k20 : c20.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k19
  have k21 : c21.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k20
  have k22 : c22.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k21
  have k23 : c23.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k22
  have k24 : c24.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k23
  have k25 : c25.sameCsr g := (Core.sameCsr_goto _ _).trans k24
  have run : QRun B img 25 ⟨g, R0⟩ ⟨c25, R4⟩ :=
    .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5 (.step (q _ k5) s6 (.step (q _ k6) s7 (.step (q _ k7) s8 (.step (q _ k8) s9 (.step (q _ k9) s10 (.step (q _ k10) s11 (.step (q _ k11) s12 (.step (q _ k12) s13 (.step (q _ k13) s14 (.step (q _ k14) s15 (.step (q _ k15) s16 (.step (q _ k16) s17 (.step (q _ k17) s18 (.step (q _ k18) s19 (.step (q _ k19) s20 (.step (q _ k20) s21 (.step (q _ k21) s22 (.step (q _ k22) s23 (.step (q _ k23) s24 (.single (q _ k24) s25))))))))))))))))))))))))
  have tne : g.get 2 + 0x10#32 ≠ g.get 2 + 0xe#32 := by bv_omega
  have hR2 : ∀ y, y ≠ g.get 2 + 0x10#32 → y ≠ g.get 2 + 0xe#32 → R2 y = R0 y := by
    intro y h1 h2
    show ramWrite (ramWrite R0 (g.get 2 + 0x10#32) (g.get 0) .b) (c2.get 2 + 0xe#32) (c2.get 0) .b y = R0 y
    rw [g2 c2 (by simp)]; simp only [ramWrite, ramPut, if_neg h1, if_neg h2]
  have hR3 : ∀ y, y ≠ g.get 2 + 0x10#32 → y ≠ g.get 2 + 0xe#32 → R3 y = R0 y := by
    intro y h1 h2
    show ramWrite R2 (g.get 2 + 0x10#32) (c12.get 11) .b y = R0 y
    simp only [ramWrite, ramPut, if_neg h1]; exact hR2 y h1 h2
  refine ⟨c25, R4, run, ⟨rfl, k25, ⟨R3, hR3, ?_⟩, ?_⟩⟩
  · show ramWrite R3 (g.get 30) (c24.get 11) .w = _
    rw [vval]
    obtain ⟨a0, -, -⟩ := asm_byte x 0 z (lbu_lt _ _) (by decide) (lbu_lt _ _)
    apply merge_store_q R0 R3 _ _ _ _ 1 (by decide) hprev
    intro j hj
    have hs := hsep 0 (by decide)
    rw [show g.get 11 + 4#32 + BitVec.ofNat 32 0 = g.get 11 + 0x4#32 by bv_omega] at hs
    have r3 : R3 (g.get 2 + 0x10#32) = byteOf (c12.get 11) 0 := by
      show ramWrite R2 (g.get 2 + 0x10#32) (c12.get 11) .b _ = _
      simp only [ramWrite, ramPut, if_pos rfl, ite_true]
    have c12_11 : c12.get 11 = extend .b false (ramRead R2 (g.get 11 + 0x4#32) .b) := by
      simp only [c12, Core.wr_get_self _ (11 : Reg) _ _ (by decide)]; rw [v11]
    rcases (by omega : j = 0) with rfl
    rw [a0, lbu_byte, r3, c12_11, lbu_byte, hR2 _ hs.1 hs.2]; congr 1; bv_omega
  · intro r hr
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h7 : r ≠ 7 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h29 : r ≠ 29 := fun e => hr (by subst e; decide)
    simp [c25, c24, c23, c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne, h6, h7, h11, h12, h14, h29]

end E5R.Rmk
