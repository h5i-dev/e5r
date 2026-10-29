/-
  The emitted memmove, forward direction, n ≥ 16, source and destination
  congruent mod 4 (SPECIALIZATION: the misaligned shift/merge path, taken
  when they are not, is separate).

  Original e5r code, Apache-2.0.

    0x80020e20 li a3,16; bltu a2,a3 (not taken)
    0x80020e26 neg a3,a0; andi a6,a3,3; add t5,a0,a6; bgeu a0,t5 -> 0x80020e4c
    0x80020e36 mv a5,a6; mv a3,a0; mv a4,a1; head loop            -> 0x80020e4c
    0x80020e4c add t0,a1,a6; sub a6,a2,a6; andi a7,a6,-4; andi t1,t0,3;
               add a3,t5,a7; beqz t1 -> 0x80020ebc
    0x80020ebc bgeu t5,a3 (not taken); mv a1,t0; word loop; j      -> 0x80020fb6
    0x80020fb6 add a1,t0,a7; andi a2,a6,3; add a4,a3,a2; bgeu a3,a4 -> exit | byte loop
-/
import Projects.rmk.MemmoveBigLoops
import Projects.rmk.MemmoveSmall

set_option maxRecDepth 100000

namespace E5R.Rmk.Memmove
open E5R E5R.Rmk E5R.Rmk.MemmoveFetch

theorem and3 (x : Word) : (x &&& 3#32).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and, show (3#32 : Word).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem andm4 (y : Word) : (y &&& 0xfffffffc#32).toNat = y.toNat - y.toNat % 4 := by
  have key : ∀ i (h : i < 32), ((0xfffffffc#32 : Word)[i] && (3#32 : Word)[i]) = false := by decide
  have key2 : ∀ i (h : i < 32), ((0xfffffffc#32 : Word)[i] || (3#32 : Word)[i]) = true := by decide
  have hz : (y &&& 0xfffffffc#32) &&& (y &&& 3#32) = 0#32 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    have := key i hi
    simp only [BitVec.getElem_and, BitVec.getElem_zero]
    cases y[i] <;> simp_all
  have hy : (y &&& 0xfffffffc#32) + (y &&& 3#32) = y := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ hz]
    apply BitVec.eq_of_getElem_eq; intro i hi
    have := key2 i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    cases y[i] <;> simp_all
  have := BitVec.toNat_add_of_and_eq_zero hz
  rw [hy, and3] at this
  omega

theorem alu_and (a b : Word) : alu .and a b = a &&& b := rfl

/-- Bytes the head loop copies to align the destination. -/
def headN (d : Word) : Word := (0 - d) &&& 3#32

theorem headN_lt (d : Word) : (headN d).toNat < 4 := by
  unfold headN; rw [and3]; omega

theorem headN_al (d : Word) : (d + headN d).toNat % 4 = 0 := by
  have := and3 (0 - d); unfold headN; bv_omega

/-! ## 0x80020daa (forward taken) to 0x80020e4c: the destination aligned -/

/-- The core at 0x80020e4c. -/
structure AtMid (c g : Core) : Prop where
  pc : g.pc = 0x80020e4c
  csr : g.sameCsr c
  r10 : g.get 10 = c.get 10
  r11 : g.get 11 = c.get 11
  r12 : g.get 12 = c.get 12
  r16 : g.get 16 = headN (c.get 10)
  r30 : g.get 30 = c.get 10 + headN (c.get 10)
  sp : g.get 2 = c.get 2 + 0xffffffd0#32
  frame : ∀ r : Reg, r.val ∉ [2, 6, 9, 13, 14, 15, 16, 30] → g.get r = c.get r

theorem big_entry (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : 16 ≤ (c.get 12).toNat) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = false)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true) :
    ∃ k g, QRun B img k ⟨pro c, R0⟩ ⟨g, fwd R0 (c.get 11) (c.get 10) (headN (c.get 10)).toNat⟩ ∧
      AtMid c g := by
  let P := pro c
  have qP : Quiet P := Quiet.of_sameCsr (pro_sameCsr c) hq
  have g10 : P.get 10 = c.get 10 := pro_get c 10 (by decide) (by decide) (by decide)
  have g11 : P.get 11 = c.get 11 := pro_get c 11 (by decide) (by decide) (by decide)
  have g12 : P.get 12 = c.get 12 := pro_get c 12 (by decide) (by decide) (by decide)
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hH := headN_lt (c.get 10)
  let d1 := P.goto 0x80020e20
  let d2 := d1.wr 13 (alu .add 0 0x10#32) 0x80020e22
  let d3 := d2.goto 0x80020e26
  let d4 := d3.wr 13 (alu .sub 0 (c.get 10)) 0x80020e2a
  let d5 := d4.wr 16 (headN (c.get 10)) 0x80020e2e
  let d6 := d5.wr 30 (alu .add (c.get 10) (headN (c.get 10))) 0x80020e32
  have q1 : Quiet d1 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) qP
  have q2 : Quiet d2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet d3 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q2
  have q4 : Quiet d4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet d5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet d6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have cs6 : d6.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_goto _ _).trans (pro_sameCsr c))))))
  have s0 : DetStep B img ⟨P, R0⟩ ⟨d1, R0⟩ := by
    refine detStep_of (by show (0x80020daa : Word).getLsbD 0 = false; decide) f80020daa fun o => ?_
    rw [exec_branch, pro_get13, g12]
    simp only [taken, alu_sub, hdir, Bool.not_false, if_true]
    rw [show P.pc + 0x76#32 = 0x80020e20 by rw [show P.pc = 0x80020daa from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s1 : DetStep B img ⟨d1, R0⟩ ⟨d2, R0⟩ := by
    refine detStep_of (by show (0x80020e20 : Word).getLsbD 0 = false; decide) f80020e20 fun o => ?_
    rw [exec_opimm, Core.get_zero]; rfl
  have s2 : DetStep B img ⟨d2, R0⟩ ⟨d3, R0⟩ := by
    refine detStep_of (by show (0x80020e22 : Word).getLsbD 0 = false; decide) f80020e22 fun o => ?_
    rw [exec_branch]
    have e12 : d2.get 12 = c.get 12 := by simp [d2, d1, Core.wr_get_ne, g12]
    have e13 : d2.get 13 = alu .add 0 0x10#32 := by simp [d2, Core.wr_get_self]
    have hnt : (c.get 12).ult (alu .add 0 0x10#32) = false := by
      rw [alu_add]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
    rw [e12, e13]; simp only [taken, hnt, Bool.false_eq_true, if_false]; rfl
  have s3 : DetStep B img ⟨d3, R0⟩ ⟨d4, R0⟩ := by
    refine detStep_of (by show (0x80020e26 : Word).getLsbD 0 = false; decide) f80020e26 fun o => ?_
    rw [exec_op, Core.get_zero]
    have : d3.get 10 = c.get 10 := by simp [d3, d2, d1, Core.wr_get_ne, g10]
    rw [this]; rfl
  have s4 : DetStep B img ⟨d4, R0⟩ ⟨d5, R0⟩ := by
    refine detStep_of (by show (0x80020e2a : Word).getLsbD 0 = false; decide) f80020e2a fun o => ?_
    rw [exec_opimm]
    have : d4.get 13 = alu .sub 0 (c.get 10) := by simp [d4, Core.wr_get_self]
    rw [this]; rfl
  have s5 : DetStep B img ⟨d5, R0⟩ ⟨d6, R0⟩ := by
    refine detStep_of (by show (0x80020e2e : Word).getLsbD 0 = false; decide) f80020e2e fun o => ?_
    rw [exec_op]
    have h10 : d5.get 10 = c.get 10 := by simp [d5, d4, d3, d2, d1, Core.wr_get_ne, g10]
    have h16 : d5.get 16 = (headN (c.get 10)) := by simp [d5, Core.wr_get_self]
    rw [h10, h16]; rfl
  have hpre : QRun B img 6 ⟨P, R0⟩ ⟨d6, R0⟩ :=
    .step qP s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.step q4 s4 (.single q5 s5)))))
  have f6 : ∀ r : Reg, r.val ∉ [2, 6, 13, 16, 30] → d6.get r = c.get r := by
    intro r hr
    have h2 : r ≠ 2 := fun e => hr (by subst e; decide)
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h16 : r ≠ 16 := fun e => hr (by subst e; decide)
    have h30 : r ≠ 30 := fun e => hr (by subst e; decide)
    simp only [d6, d5, d4, d3, d2, d1, Core.wr_get_ne _ _ _ _ _ h30, Core.wr_get_ne _ _ _ _ _ h16,
      Core.wr_get_ne _ _ _ _ _ h13, Core.goto_get]
    exact pro_get c r h2 h6 h13
  have d6sp : d6.get 2 = c.get 2 + 0xffffffd0#32 := by
    simp only [d6, d5, d4, d3, d2, d1, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 30 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 16 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 13 by decide), Core.goto_get]
    exact pro_get2 c
  have d6_10 : d6.get 10 = c.get 10 := f6 10 (by decide)
  have d6_11 : d6.get 11 = c.get 11 := f6 11 (by decide)
  have d6_12 : d6.get 12 = c.get 12 := f6 12 (by decide)
  have d6_16 : d6.get 16 = (headN (c.get 10)) := by simp [d6, d5, Core.wr_get_ne, Core.wr_get_self]
  have d6_30 : d6.get 30 = c.get 10 + (headN (c.get 10)) := by simp [d6, Core.wr_get_self, alu_add]
  by_cases hz : (headN (c.get 10)).toNat = 0
  · -- already aligned: bgeu a0,t5 taken
    have s6 : DetStep B img ⟨d6, R0⟩ ⟨d6.goto 0x80020e4c, R0⟩ := by
      refine detStep_of (by show (0x80020e32 : Word).getLsbD 0 = false; decide) f80020e32 fun o => ?_
      rw [exec_branch, d6_10, d6_30]
      have hnt : (c.get 10).ult (c.get 10 + (headN (c.get 10))) = false := by
        simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      simp only [taken, hnt, Bool.not_false, if_true]
      rw [show d6.pc + 0x1a#32 = 0x80020e4c by rw [show d6.pc = 0x80020e32 from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨7, d6.goto 0x80020e4c, ?_, ⟨rfl, (Core.sameCsr_goto _ _).trans cs6, d6_10, d6_11, d6_12,
      d6_16, d6_30, d6sp, fun r hr => by rw [Core.goto_get]; exact f6 r (fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))⟩⟩
    rw [hz]; exact hpre.trans (.single q6 s6)
  · -- head loop
    let e1 := d6.goto 0x80020e36
    let e2 := e1.wr 15 (alu .add 0 (headN (c.get 10))) 0x80020e38
    let e3 := e2.wr 13 (alu .add 0 (c.get 10)) 0x80020e3a
    let e4 := e3.wr 14 (alu .add 0 (c.get 11)) 0x80020e3c
    have r1 : Quiet e1 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q6
    have r2 : Quiet e2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) r1
    have r3 : Quiet e3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) r2
    have r4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) r3
    have s6 : DetStep B img ⟨d6, R0⟩ ⟨e1, R0⟩ := by
      refine detStep_of (by show (0x80020e32 : Word).getLsbD 0 = false; decide) f80020e32 fun o => ?_
      rw [exec_branch, d6_10, d6_30]
      have ht : (c.get 10).ult (c.get 10 + (headN (c.get 10))) = true := by
        simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      simp only [taken, ht, Bool.not_true, Bool.false_eq_true, if_false]; rfl
    have s7 : DetStep B img ⟨e1, R0⟩ ⟨e2, R0⟩ := by
      refine detStep_of (by show (0x80020e36 : Word).getLsbD 0 = false; decide) f80020e36 fun o => ?_
      rw [exec_op, Core.get_zero, show e1.get 16 = (headN (c.get 10)) from d6_16]; rfl
    have s8 : DetStep B img ⟨e2, R0⟩ ⟨e3, R0⟩ := by
      refine detStep_of (by show (0x80020e38 : Word).getLsbD 0 = false; decide) f80020e38 fun o => ?_
      rw [exec_op, Core.get_zero]
      have : e2.get 10 = c.get 10 := by simp [e2, e1, Core.wr_get_ne, d6_10]
      rw [this]; rfl
    have s9 : DetStep B img ⟨e3, R0⟩ ⟨e4, R0⟩ := by
      refine detStep_of (by show (0x80020e3a : Word).getLsbD 0 = false; decide) f80020e3a fun o => ?_
      rw [exec_op, Core.get_zero]
      have : e3.get 11 = c.get 11 := by simp [e3, e2, e1, Core.wr_get_ne, d6_11]
      rw [this]; rfl
    let k := (headN (c.get 10)).toNat - 1
    have hk : k + 1 = (headN (c.get 10)).toNat := by omega
    have l15 : e4.get 15 = BitVec.ofNat 32 (k + 1) := by
      simp [e4, e3, e2, Core.wr_get_ne, Core.wr_get_self, alu_add, hk]
    have l14 : e4.get 14 = c.get 11 := by simp [e4, Core.wr_get_self, alu_add]
    have l13 : e4.get 13 = c.get 10 := by simp [e4, e3, Core.wr_get_ne, Core.wr_get_self, alu_add]
    obtain ⟨m, g, hr, hpc, hcs, h13, h14, hfr⟩ := head_loop k e4 R0 rfl r4 l15 (by omega)
      (by rw [l14, hk, B_ram]; omega) (by rw [l13, hk, B_ram]; omega)
    have ge : ∀ r : Reg, r ≠ 9 → r ≠ 13 → r ≠ 14 → r ≠ 15 → g.get r = d6.get r := by
      intro r a b d e
      rw [hfr r a b d e]
      simp [e4, e3, e2, e1, Core.wr_get_ne, b, d, e]
    refine ⟨6 + 1 + 3 + m, g, ?_, ⟨hpc, hcs.trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans cs6)))),
      by rw [ge 10 (by decide) (by decide) (by decide) (by decide), d6_10],
      by rw [ge 11 (by decide) (by decide) (by decide) (by decide), d6_11],
      by rw [ge 12 (by decide) (by decide) (by decide) (by decide), d6_12],
      by rw [ge 16 (by decide) (by decide) (by decide) (by decide), d6_16],
      by rw [ge 30 (by decide) (by decide) (by decide) (by decide), d6_30],
      by rw [ge 2 (by decide) (by decide) (by decide) (by decide), d6sp], ?_⟩⟩
    · rw [l14, l13, hk] at hr
      exact (hpre.trans (.step q6 s6 (.step r1 s7 (.step r2 s8 (.single r3 s9))))).trans hr
    · intro r hr
      have h9 : r ≠ 9 := fun e => hr (by subst e; decide)
      have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
      have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
      have h15 : r ≠ 15 := fun e => hr (by subst e; decide)
      rw [ge r h9 h13 h14 h15]
      exact f6 r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))

end E5R.Rmk.Memmove
