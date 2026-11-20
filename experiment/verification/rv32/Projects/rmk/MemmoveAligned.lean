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

/-! ## 0x80020e4c to the epilogue, source aligned too -/

/-- Word bytes after the head. -/
def wordsN (c : Core) : Word := (c.get 12 - headN (c.get 10)) &&& 0xfffffffc#32
/-- Tail bytes after the words. -/
def tailN (c : Core) : Word := (c.get 12 - headN (c.get 10)) &&& 3#32

theorem fwd_congr {R : Word → BitVec 8} {s s' d d' : Word} {k : Nat} (hs : s = s') (hd : d = d') :
    fwd R s d k = fwd R s' d' k := by rw [hs, hd]

theorem big_aligned (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : 16 ≤ (c.get 12).toNat) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = false)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true)
    (hcong : (c.get 11).toNat % 4 = (c.get 10).toNat % 4) :
    ∃ k e, QRun B img k ⟨pro c, R0⟩ ⟨e, fwd R0 (c.get 11) (c.get 10) (c.get 12).toNat⟩ ∧
      e.pc = 0x800210b0 ∧ Frame c e [5, 9, 11, 12, 13, 14, 15, 16, 17, 30] := by
  obtain ⟨k1, g, hr1, hm⟩ := big_entry c R0 hq hn hdir hd hs
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hH := headN_lt (c.get 10)
  have hHal := headN_al (c.get 10)
  have hW : (wordsN c).toNat = (c.get 12 - headN (c.get 10)).toNat - (c.get 12 - headN (c.get 10)).toNat % 4 :=
    andm4 _
  have hT : (tailN c).toNat = (c.get 12 - headN (c.get 10)).toNat % 4 := and3 _
  have hsH : (c.get 11 + headN (c.get 10)).toNat % 4 = 0 := by bv_omega
  have hdirN : (c.get 10).toNat ≤ (c.get 11).toNat ∨ (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat := by
    simp only [BitVec.ult, decide_eq_false_iff_not] at hdir; bv_omega
  have qg : Quiet g := Quiet.of_sameCsr hm.csr hq
  let R1 := fwd R0 (c.get 11) (c.get 10) (headN (c.get 10)).toNat
  let g1 := g.wr 5 (alu .add (c.get 11) (headN (c.get 10))) 0x80020e50
  let g2 := g1.wr 16 (alu .sub (c.get 12) (headN (c.get 10))) 0x80020e54
  let g3 := g2.wr 17 (wordsN c) 0x80020e58
  let g4 := g3.wr 6 (alu .and (alu .add (c.get 11) (headN (c.get 10))) 3#32) 0x80020e5c
  let g5 := g4.wr 13 (alu .add (c.get 10 + (headN (c.get 10))) (wordsN c)) 0x80020e60
  let g6 := g5.goto 0x80020ebc
  let g7 := g6.goto 0x80020ec0
  let g8 := g7.wr 11 (alu .add 0 (alu .add (c.get 11) (headN (c.get 10)))) 0x80020ec2
  have q1 : Quiet g1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qg
  have q2 : Quiet g2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet g3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet g4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet g5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet g6 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
  have q7 : Quiet g7 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q6
  have q8 : Quiet g8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have cs8 : g8.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        hm.csr)))))))
  have s1 : DetStep B img ⟨g, R1⟩ ⟨g1, R1⟩ := by
    refine detStep_of (by rw [hm.pc]; decide) (by rw [hm.pc]; exact f80020e4c) fun o => ?_
    rw [exec_op, hm.r11, hm.r16, hm.pc]; rfl
  have s2 : DetStep B img ⟨g1, R1⟩ ⟨g2, R1⟩ := by
    refine detStep_of (by show (0x80020e50 : Word).getLsbD 0 = false; decide) f80020e50 fun o => ?_
    rw [exec_op]
    have h12 : g1.get 12 = c.get 12 := by simp [g1, Core.wr_get_ne, hm.r12]
    have h16 : g1.get 16 = (headN (c.get 10)) := by simp [g1, Core.wr_get_ne, hm.r16]
    rw [h12, h16]; rfl
  have s3 : DetStep B img ⟨g2, R1⟩ ⟨g3, R1⟩ := by
    refine detStep_of (by show (0x80020e54 : Word).getLsbD 0 = false; decide) f80020e54 fun o => ?_
    rw [exec_opimm]
    have : g2.get 16 = alu .sub (c.get 12) (headN (c.get 10)) := by simp [g2, Core.wr_get_self]
    rw [this]; rfl
  have s4 : DetStep B img ⟨g3, R1⟩ ⟨g4, R1⟩ := by
    refine detStep_of (by show (0x80020e58 : Word).getLsbD 0 = false; decide) f80020e58 fun o => ?_
    rw [exec_opimm]
    have : g3.get 5 = alu .add (c.get 11) (headN (c.get 10)) := by simp [g3, g2, g1, Core.wr_get_ne, Core.wr_get_self]
    rw [this]; rfl
  have s5 : DetStep B img ⟨g4, R1⟩ ⟨g5, R1⟩ := by
    refine detStep_of (by show (0x80020e5c : Word).getLsbD 0 = false; decide) f80020e5c fun o => ?_
    rw [exec_op]
    have h30 : g4.get 30 = c.get 10 + (headN (c.get 10)) := by simp [g4, g3, g2, g1, Core.wr_get_ne, hm.r30]
    have h17 : g4.get 17 = (wordsN c) := by simp [g4, g3, Core.wr_get_ne, Core.wr_get_self]
    rw [h30, h17]; rfl
  have s6 : DetStep B img ⟨g5, R1⟩ ⟨g6, R1⟩ := by
    refine detStep_of (by show (0x80020e60 : Word).getLsbD 0 = false; decide) f80020e60 fun o => ?_
    rw [exec_branch]
    have h6 : g5.get 6 = alu .and (alu .add (c.get 11) (headN (c.get 10))) 3#32 := by
      simp [g5, g4, Core.wr_get_ne, Core.wr_get_self]
    have hz : alu .and (alu .add (c.get 11) (headN (c.get 10))) 3#32 = 0 := by
      rw [alu_and, alu_add]; apply BitVec.eq_of_toNat_eq; rw [and3]; simpa using hsH
    rw [h6, hz]; simp only [taken, Core.get_zero, beq_self_eq_true, if_true]
    rw [show g5.pc + 0x5c#32 = 0x80020ebc by rw [show g5.pc = 0x80020e60 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s7 : DetStep B img ⟨g6, R1⟩ ⟨g7, R1⟩ := by
    refine detStep_of (by show (0x80020ebc : Word).getLsbD 0 = false; decide) f80020ebc fun o => ?_
    rw [exec_branch]
    have h30 : g6.get 30 = c.get 10 + (headN (c.get 10)) := by simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, hm.r30]
    have h13 : g6.get 13 = alu .add (c.get 10 + (headN (c.get 10))) (wordsN c) := by simp [g6, g5, Core.wr_get_self]
    have hnt : (c.get 10 + (headN (c.get 10))).ult (alu .add (c.get 10 + (headN (c.get 10))) (wordsN c)) = true := by
      rw [alu_add]; simp only [BitVec.ult, decide_eq_true_iff]
      bv_omega
    rw [h30, h13]; simp only [taken, hnt, Bool.not_true, Bool.false_eq_true, if_false]; rfl
  have s8 : DetStep B img ⟨g7, R1⟩ ⟨g8, R1⟩ := by
    refine detStep_of (by show (0x80020ec0 : Word).getLsbD 0 = false; decide) f80020ec0 fun o => ?_
    rw [exec_op, Core.get_zero]
    have : g7.get 5 = alu .add (c.get 11) (headN (c.get 10)) := by simp [g7, g6, g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self]
    rw [this]; rfl
  have hmid : QRun B img 8 ⟨g, R1⟩ ⟨g8, R1⟩ :=
    .step qg s1 (.step q1 s2 (.step q2 s3 (.step q3 s4 (.step q4 s5 (.step q5 s6 (.step q6 s7 (.single q7 s8)))))))
  -- word loop
  have hWv : (wordsN c).toNat = (c.get 12 - (headN (c.get 10))).toNat - (c.get 12 - (headN (c.get 10))).toNat % 4 := hW
  have hTv : (tailN c).toNat = (c.get 12 - (headN (c.get 10))).toNat % 4 := hT
  have hnH : (c.get 12 - (headN (c.get 10))).toNat = (c.get 12).toNat - (headN (c.get 10)).toNat := by bv_omega
  let j := (wordsN c).toNat / 4 - 1
  have hj : 4 * (j + 1) = (wordsN c).toNat := by omega
  have l11 : g8.get 11 = c.get 11 + (headN (c.get 10)) := by simp [g8, Core.wr_get_self, alu_add]
  have l30 : g8.get 30 = c.get 10 + (headN (c.get 10)) := by simp [g8, g7, g6, g5, g4, g3, g2, g1, Core.wr_get_ne, hm.r30]
  have l13 : g8.get 13 = c.get 10 + (headN (c.get 10)) + (wordsN c) := by simp [g8, g7, g6, g5, Core.wr_get_ne, Core.wr_get_self, alu_add]
  obtain ⟨m2, g9, hr2, hpc9, hcs9, hfr9⟩ := word_loop j g8 R1 rfl q8
    (by rw [l13, l30, hj]; bv_omega) (by rw [l30, hj]; bv_omega) (by rw [l11]; exact hsH) (by rw [l30]; exact hHal)
    (by rw [l11, B_ram, hj]; constructor <;> bv_omega) (by rw [l30, B_ram, hj]; constructor <;> bv_omega)
  rw [l11, l30] at hr2
  let R2 := words R1 (c.get 11 + (headN (c.get 10))) (c.get 10 + (headN (c.get 10))) (j + 1)
  have qg9 : Quiet g9 := Quiet.of_sameCsr hcs9 q8
  have g9r : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 30 → g9.get r = g8.get r := hfr9
  -- tail dispatch
  let t1 := g9.wr 11 (alu .add (c.get 11 + (headN (c.get 10))) (wordsN c)) 0x80020fba
  let t2 := t1.wr 12 (tailN c) 0x80020fbe
  let t3 := t2.wr 14 (alu .add (c.get 10 + (headN (c.get 10)) + (wordsN c)) (tailN c)) 0x80020fc2
  have p1 : Quiet t1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qg9
  have p2 : Quiet t2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) p1
  have p3 : Quiet t3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) p2
  have u1 : DetStep B img ⟨g9, R2⟩ ⟨t1, R2⟩ := by
    refine detStep_of (by rw [hpc9]; decide) (by rw [hpc9]; exact f80020fb6) fun o => ?_
    rw [exec_op, g9r 5 (by decide) (by decide) (by decide), g9r 17 (by decide) (by decide) (by decide), hpc9]
    have h5 : g8.get 5 = c.get 11 + (headN (c.get 10)) := by simp [g8, g7, g6, g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self, alu_add]
    have h17 : g8.get 17 = (wordsN c) := by simp [g8, g7, g6, g5, g4, g3, Core.wr_get_ne, Core.wr_get_self]
    rw [h5, h17]; rfl
  have u2 : DetStep B img ⟨t1, R2⟩ ⟨t2, R2⟩ := by
    refine detStep_of (by show (0x80020fba : Word).getLsbD 0 = false; decide) f80020fba fun o => ?_
    rw [exec_opimm]
    have : t1.get 16 = c.get 12 - (headN (c.get 10)) := by
      simp only [t1, Core.wr_get_ne _ _ _ _ _ (show (16 : Reg) ≠ 11 by decide)]
      rw [g9r 16 (by decide) (by decide) (by decide)]
      simp [g8, g7, g6, g5, g4, g3, g2, Core.wr_get_ne, Core.wr_get_self, alu_sub]
    rw [this]; rfl
  have u3 : DetStep B img ⟨t2, R2⟩ ⟨t3, R2⟩ := by
    refine detStep_of (by show (0x80020fbe : Word).getLsbD 0 = false; decide) f80020fbe fun o => ?_
    rw [exec_op]
    have h13 : t2.get 13 = c.get 10 + (headN (c.get 10)) + (wordsN c) := by
      simp only [t2, t1, Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 11 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 12 by decide)]
      rw [g9r 13 (by decide) (by decide) (by decide), l13]
    have h12 : t2.get 12 = (tailN c) := by simp [t2, Core.wr_get_self]
    rw [h13, h12]; rfl
  have hpre : QRun B img (k1 + 8 + m2 + 3) ⟨pro c, R0⟩ ⟨t3, R2⟩ :=
    ((hr1.trans hmid).trans hr2).trans (.step qg9 u1 (.step p1 u2 (.single p2 u3)))
  have t3_13 : t3.get 13 = c.get 10 + (headN (c.get 10)) + (wordsN c) := by
    simp only [t3, t2, t1, Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 11 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 12 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 14 by decide)]
    rw [g9r 13 (by decide) (by decide) (by decide), l13]
  have t3_14 : t3.get 14 = alu .add (c.get 10 + (headN (c.get 10)) + (wordsN c)) (tailN c) := by simp [t3, Core.wr_get_self]
  have t3_11 : t3.get 11 = c.get 11 + (headN (c.get 10)) + (wordsN c) := by simp [t3, t2, t1, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have t3_12 : t3.get 12 = (tailN c) := by simp [t3, t2, Core.wr_get_ne, Core.wr_get_self]
  have cs3 : t3.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (hcs9.trans cs8)))
  -- the frame of everything so far
  have f3 : ∀ r : Reg, r.val ∉ [2, 6, 5, 9, 11, 12, 13, 14, 15, 16, 17, 30] → t3.get r = c.get r := by
    intro r hr
    have h5 : r ≠ 5 := fun e => hr (by subst e; decide)
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h16 : r ≠ 16 := fun e => hr (by subst e; decide)
    have h17 : r ≠ 17 := fun e => hr (by subst e; decide)
    have h30 : r ≠ 30 := fun e => hr (by subst e; decide)
    simp only [t3, t2, t1, Core.wr_get_ne _ _ _ _ _ h14, Core.wr_get_ne _ _ _ _ _ h12,
      Core.wr_get_ne _ _ _ _ _ h11]
    rw [g9r r h11 h12 h30]
    simp only [g8, g7, g6, g5, g4, g3, g2, g1, Core.wr_get_ne _ _ _ _ _ h11, Core.wr_get_ne _ _ _ _ _ h13,
      Core.wr_get_ne _ _ _ _ _ h6, Core.wr_get_ne _ _ _ _ _ h17, Core.wr_get_ne _ _ _ _ _ h16,
      Core.wr_get_ne _ _ _ _ _ h5, Core.goto_get]
    exact hm.frame r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))
  have t3sp : t3.get 2 = c.get 2 + 0xffffffd0#32 := by
    simp only [t3, t2, t1, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 14 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 12 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 11 by decide)]
    rw [g9r 2 (by decide) (by decide) (by decide)]
    simp only [g8, g7, g6, g5, g4, g3, g2, g1, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 11 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 13 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 6 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 17 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 16 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 5 by decide), Core.goto_get]
    exact hm.sp
  -- the RAM: head, words, tail are one forward copy
  have hR2 : R2 = fwd R0 (c.get 11) (c.get 10) ((headN (c.get 10)).toNat + (wordsN c).toNat) := by
    show words R1 (c.get 11 + (headN (c.get 10))) (c.get 10 + (headN (c.get 10))) (j + 1) = _
    rw [words_eq_fwd (j + 1) R1 _ _ (by bv_omega) (by bv_omega) (by bv_omega), hj, fwd_add]
    exact fwd_congr (by bv_omega) (by bv_omega)
  have hfin : ∀ R : Word → BitVec 8,
      fwd R2 (c.get 11 + (headN (c.get 10)) + (wordsN c)) (c.get 10 + (headN (c.get 10)) + (wordsN c)) (tailN c).toNat = fwd R0 (c.get 11) (c.get 10) (c.get 12).toNat := by
    intro _
    rw [hR2, show (c.get 12).toNat = ((headN (c.get 10)).toNat + (wordsN c).toNat) + (tailN c).toNat by omega, fwd_add ((headN (c.get 10)).toNat + (wordsN c).toNat)]
    exact fwd_congr (by bv_omega) (by bv_omega)
  by_cases hz : (tailN c).toNat = 0
  · have u4 : DetStep B img ⟨t3, R2⟩ ⟨t3.goto 0x800210b0, R2⟩ := by
      refine detStep_of (by show (0x80020fc2 : Word).getLsbD 0 = false; decide) f80020fc2 fun o => ?_
      rw [exec_branch, t3_13, t3_14]
      have hnt : (c.get 10 + (headN (c.get 10)) + (wordsN c)).ult (alu .add (c.get 10 + (headN (c.get 10)) + (wordsN c)) (tailN c)) = false := by
        rw [alu_add]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      simp only [taken, hnt, Bool.not_false, if_true]
      rw [show t3.pc + 0xee#32 = 0x800210b0 by rw [show t3.pc = 0x80020fc2 from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨k1 + 8 + m2 + 3 + 1, t3.goto 0x800210b0, ?_, rfl, (Core.sameCsr_goto _ _).trans cs3, by simpa using t3sp,
      fun r hr => by rw [Core.goto_get]; exact f3 r (fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))⟩
    have := hpre.trans (.single p3 u4)
    rw [← hfin R0, hz]; exact this
  · have u4 : DetStep B img ⟨t3, R2⟩ ⟨t3.goto 0x80020fc6, R2⟩ := by
      refine detStep_of (by show (0x80020fc2 : Word).getLsbD 0 = false; decide) f80020fc2 fun o => ?_
      rw [exec_branch, t3_13, t3_14]
      have ht : (c.get 10 + (headN (c.get 10)) + (wordsN c)).ult (alu .add (c.get 10 + (headN (c.get 10)) + (wordsN c)) (tailN c)) = true := by
        rw [alu_add]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      simp only [taken, ht, Bool.not_true, Bool.false_eq_true, if_false]; rfl
    have p4 : Quiet (t3.goto 0x80020fc6) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) p3
    let kk := (tailN c).toNat - 1
    have hkk : kk + 1 = (tailN c).toNat := by omega
    obtain ⟨m3, e, hr3, hpe, hcse, hfre⟩ := fwd_loop kk (t3.goto 0x80020fc6) R2 rfl p4
      (by rw [Core.goto_get, t3_12, hkk]; simp) (by omega)
      (by rw [Core.goto_get, t3_11, hkk, B_ram]; constructor <;> bv_omega)
      (by rw [Core.goto_get, t3_13, hkk, B_ram]; constructor <;> bv_omega)
    refine ⟨k1 + 8 + m2 + 3 + 1 + m3, e, ?_, hpe, hcse.trans ((Core.sameCsr_goto _ _).trans cs3), ?_, ?_⟩
    · rw [Core.goto_get, Core.goto_get, t3_11, t3_13, hkk] at hr3
      rw [← hfin R0]; exact (hpre.trans (.single p3 u4)).trans hr3
    · rw [hfre 2 (by decide) (by decide) (by decide) (by decide), Core.goto_get]; exact t3sp
    · intro r hr
      have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
      have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
      have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
      have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
      rw [hfre r h11 h12 h13 h14, Core.goto_get]
      exact f3 r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))

end E5R.Rmk.Memmove
