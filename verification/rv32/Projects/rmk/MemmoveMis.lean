/-
  memmove, forward direction, n ≥ 16, source and destination NOT
  congruent mod 4: the misaligned shift/merge path composed (pinned RMK
  image). Its stack temporaries (sp+0x14..0x17, sp+0x10, sp+0xe of the
  callee frame) are the only bytes besides the destination it writes.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.MemmoveMisEnd
import Projects.rmk.MemmoveAligned

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-! ## Copies ignore bytes they neither read nor write -/

theorem fwd_frame (Z : Word → Prop) : ∀ (k : Nat) (R1 R2 : Word → BitVec 8) (s d : Word),
    (∀ y, ¬ Z y → R1 y = R2 y) → (∀ i < k, ¬ Z (s + BitVec.ofNat 32 i)) → (∀ i < k, ¬ Z (d + BitVec.ofNat 32 i)) →
    ∀ y, ¬ Z y → fwd R1 s d k y = fwd R2 s d k y
  | 0, R1, R2, s, d, h, _, _, y, hy => h y hy
  | k+1, R1, R2, s, d, h, hs, hd, y, hy => by
    simp only [fwd]
    apply fwd_frame Z k _ _ (s + 1) (d + 1)
    · intro y' hy'
      simp only [ramPut]
      split
      · exact h s (by simpa using hs 0 (by omega))
      · exact h y' hy'
    · intro i hi; have := hs (i + 1) (by omega); rwa [show s + 1 + BitVec.ofNat 32 i = s + BitVec.ofNat 32 (i + 1) by bv_omega]
    · intro i hi; have := hd (i + 1) (by omega); rwa [show d + 1 + BitVec.ofNat 32 i = d + BitVec.ofNat 32 (i + 1) by bv_omega]
    · exact hy

/-- `word_spec` with the stored word read from another RAM. -/
theorem word_spec2 (R R2 : Word → BitVec 8) (s d x : Word) (hd : d.toNat + 4 < 2 ^ 32) :
    ramWrite R d (ramRead R2 s .w) .w x =
      if d.toNat ≤ x.toNat ∧ x.toNat < d.toNat + 4 then R2 (s + (x - d)) else R x := by
  obtain ⟨b0, b1, b2, b3⟩ := byte_read R2 s
  simp only [ramWrite, ramPut, b0, b1, b2, b3]
  repeat' split
  all_goals first | (exfalso; bv_omega) | (refine congrArg R2 ?_; bv_omega) | rfl

/-! ## The shared tail: 0x80020fb6 (a1 := t0 + a7; a2 := a6 & 3; byte loop or exit) -/

theorem tail_dispatch (t : Core) (R : Word → BitVec 8) (hpc : t.pc = 0x80020fb6) (hq : Quiet t)
    (hX : B.inRam (t.get 5 + t.get 17) (t.get 16 &&& 3#32).toNat = true)
    (hE : B.inRam (t.get 13) (t.get 16 &&& 3#32).toNat = true) :
    ∃ k e, QRun B img k ⟨t, R⟩ ⟨e, fwd R (t.get 5 + t.get 17) (t.get 13) (t.get 16 &&& 3#32).toNat⟩ ∧
      e.pc = 0x800210b0 ∧ e.sameCsr t ∧ ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → e.get r = t.get r := by
  have hT := Memmove.and3 (t.get 16)
  let t1 := t.wr 11 (alu .add (t.get 5) (t.get 17)) 0x80020fba
  let t2 := t1.wr 12 (alu .and (t1.get 16) 0x3#32) 0x80020fbe
  let t3 := t2.wr 14 (alu .add (t2.get 13) (t2.get 12)) 0x80020fc2
  have k1 : t1.sameCsr t := Core.sameCsr_wr _ _ _ _
  have k2 : t2.sameCsr t := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : t3.sameCsr t := (Core.sameCsr_wr _ _ _ _).trans k2
  have u1 : DetStep B img ⟨t, R⟩ ⟨t1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020fb6) fun o => ?_
    rw [exec_op, hpc]; rfl
  have u2 : DetStep B img ⟨t1, R⟩ ⟨t2, R⟩ := by
    refine detStep_of (by show (0x80020fba : Word).getLsbD 0 = false; decide) f80020fba fun o => ?_
    rw [exec_opimm]; rfl
  have u3 : DetStep B img ⟨t2, R⟩ ⟨t3, R⟩ := by
    refine detStep_of (by show (0x80020fbe : Word).getLsbD 0 = false; decide) f80020fbe fun o => ?_
    rw [exec_op]; rfl
  have v13 : t3.get 13 = t.get 13 := by simp [t3, t2, t1, Core.wr_get_ne]
  have v14 : t3.get 14 = t.get 13 + (t.get 16 &&& 3#32) := by
    simp [t3, t2, t1, Core.wr_get_ne, Core.wr_get_self, alu]
  have v11 : t3.get 11 = t.get 5 + t.get 17 := by simp [t3, t2, t1, Core.wr_get_ne, Core.wr_get_self, alu]
  have v12 : t3.get 12 = (t.get 16 &&& 3#32) := by simp [t3, t2, t1, Core.wr_get_ne, Core.wr_get_self, alu]
  have hEr := (B_ram _ _).mp hE
  have pre : QRun B img 3 ⟨t, R⟩ ⟨t3, R⟩ := .step hq u1 (.step (Quiet.of_sameCsr k1 hq) u2
    (.single (Quiet.of_sameCsr k2 hq) u3))
  have q3 : Quiet t3 := Quiet.of_sameCsr k3 hq
  have fr3 : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 14 → t3.get r = t.get r := by
    intro r a b d; simp [t3, t2, t1, Core.wr_get_ne, a, b, d]
  by_cases hz : (t.get 16 &&& 3#32).toNat = 0
  · have u4 : DetStep B img ⟨t3, R⟩ ⟨t3.goto 0x800210b0, R⟩ := by
      refine detStep_of (by show (0x80020fc2 : Word).getLsbD 0 = false; decide) f80020fc2 fun o => ?_
      rw [exec_branch, v13, v14]
      have hnt : (t.get 13).ult (t.get 13 + (t.get 16 &&& 3#32)) = false := by
        simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      simp only [taken, hnt, Bool.not_false, if_true]
      rw [show t3.pc + 0xee#32 = 0x800210b0 by rw [show t3.pc = 0x80020fc2 from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨4, t3.goto 0x800210b0, ?_, rfl, (Core.sameCsr_goto _ _).trans k3, fun r a b d e => by
      rw [Core.goto_get]; exact fr3 r a b e⟩
    show QRun B img 4 ⟨t, R⟩ ⟨_, fwd R _ _ (t.get 16 &&& 3#32).toNat⟩
    rw [hz]; exact pre.trans (.single q3 u4)
  · have u4 : DetStep B img ⟨t3, R⟩ ⟨t3.goto 0x80020fc6, R⟩ := by
      refine detStep_of (by show (0x80020fc2 : Word).getLsbD 0 = false; decide) f80020fc2 fun o => ?_
      rw [exec_branch, v13, v14]
      have ht : (t.get 13).ult (t.get 13 + (t.get 16 &&& 3#32)) = true := by
        simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      simp only [taken, ht, Bool.not_true, Bool.false_eq_true, if_false]; rfl
    have q4 : Quiet (t3.goto 0x80020fc6) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q3
    let kk := (t.get 16 &&& 3#32).toNat - 1
    have hkk : kk + 1 = (t.get 16 &&& 3#32).toNat := by omega
    obtain ⟨m, e, hr, hpe, hcse, hfre⟩ := fwd_loop kk (t3.goto 0x80020fc6) R rfl q4
      (by rw [Core.goto_get, v12, hkk]; simp) (by omega)
      (by rw [Core.goto_get, v11, hkk]; exact hX) (by rw [Core.goto_get, v13, hkk]; exact hE)
    refine ⟨3 + 1 + m, e, ?_, hpe, hcse.trans ((Core.sameCsr_goto _ _).trans k3), fun r a b d f => ?_⟩
    · rw [Core.goto_get, Core.goto_get, v11, v13, hkk] at hr
      exact (pre.trans (.single q3 u4)).trans hr
    · rw [hfre r a b d f, Core.goto_get]; exact fr3 r a b f

/-! ## 0x80020e4c to 0x80020e64 (source not word-aligned after the head) -/

structure AtMis (g h : Core) : Prop where
  pc : h.pc = 0x80020e64
  csr : h.sameCsr g
  r5 : h.get 5 = g.get 11 + g.get 16
  r16 : h.get 16 = g.get 12 - g.get 16
  r17 : h.get 17 = (g.get 12 - g.get 16) &&& 0xfffffffc#32
  r6 : h.get 6 = (g.get 11 + g.get 16) &&& 3#32
  r13 : h.get 13 = g.get 30 + ((g.get 12 - g.get 16) &&& 0xfffffffc#32)
  frame : ∀ r : Reg, r.val ∉ [5, 6, 13, 16, 17] → h.get r = g.get r

theorem mis_mid (g : Core) (R : Word → BitVec 8) (hpc : g.pc = 0x80020e4c) (hq : Quiet g)
    (hmis : ((g.get 11 + g.get 16) &&& 3#32) ≠ 0) :
    ∃ h, QRun B img 6 ⟨g, R⟩ ⟨h, R⟩ ∧ AtMis g h := by
  let g1 := g.wr 5 (alu .add (g.get 11) (g.get 16)) 0x80020e50
  let g2 := g1.wr 16 (alu .sub (g1.get 12) (g1.get 16)) 0x80020e54
  let g3 := g2.wr 17 (alu .and (g2.get 16) 0xfffffffc#32) 0x80020e58
  let g4 := g3.wr 6 (alu .and (g3.get 5) 0x3#32) 0x80020e5c
  let g5 := g4.wr 13 (alu .add (g4.get 30) (g4.get 17)) 0x80020e60
  let g6 := g5.goto 0x80020e64
  have k1 : g1.sameCsr g := Core.sameCsr_wr _ _ _ _
  have k2 : g2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : g3.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k2
  have k4 : g4.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : g5.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : g6.sameCsr g := (Core.sameCsr_goto _ _).trans k5
  have q : ∀ d : Core, d.sameCsr g → Quiet d := fun d h => Quiet.of_sameCsr h hq
  have s1 : DetStep B img ⟨g, R⟩ ⟨g1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020e4c) fun o => ?_
    rw [exec_op, hpc]; rfl
  have s2 : DetStep B img ⟨g1, R⟩ ⟨g2, R⟩ := by
    refine detStep_of (by show (0x80020e50 : Word).getLsbD 0 = false; decide) f80020e50 fun o => ?_
    rw [exec_op]; rfl
  have s3 : DetStep B img ⟨g2, R⟩ ⟨g3, R⟩ := by
    refine detStep_of (by show (0x80020e54 : Word).getLsbD 0 = false; decide) f80020e54 fun o => ?_
    rw [exec_opimm]; rfl
  have s4 : DetStep B img ⟨g3, R⟩ ⟨g4, R⟩ := by
    refine detStep_of (by show (0x80020e58 : Word).getLsbD 0 = false; decide) f80020e58 fun o => ?_
    rw [exec_opimm]; rfl
  have s5 : DetStep B img ⟨g4, R⟩ ⟨g5, R⟩ := by
    refine detStep_of (by show (0x80020e5c : Word).getLsbD 0 = false; decide) f80020e5c fun o => ?_
    rw [exec_op]; rfl
  have v6 : g5.get 6 = (g.get 11 + g.get 16) &&& 3#32 := by
    simp [g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self, alu]
  have s6 : DetStep B img ⟨g5, R⟩ ⟨g6, R⟩ := by
    refine detStep_of (by show (0x80020e60 : Word).getLsbD 0 = false; decide) f80020e60 fun o => ?_
    rw [exec_branch, v6, Core.get_zero]
    simp only [taken, beq_iff_eq, hmis, decide_false, Bool.false_eq_true, if_false]; rfl
  refine ⟨g6, .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5
    (.single (q _ k5) s6))))), ⟨rfl, k6, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self, alu]
  · simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self, alu]
  · simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self, alu]
  · simp only [g6, Core.goto_get]; exact v6
  · simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self, alu]
  · intro r hr
    have h5 : r ≠ 5 := fun e => hr (by subst e; decide)
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h16 : r ≠ 16 := fun e => hr (by subst e; decide)
    have h17 : r ≠ 17 := fun e => hr (by subst e; decide)
    simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, h5, h6, h13, h16, h17]

/-! ## The three misalignments together -/

theorem start_any (c : Core) (R : Word → BitVec 8) (o : Nat) (ho : 0 < o ∧ o < 4) (hpc : c.pc = 0x80020e64)
    (hq : Quiet c) (h6 : c.get 6 = BitVec.ofNat 32 o) (hSo : (c.get 5).toNat % 4 = o)
    (hsr : B.inRam (c.get 5) (4 - o) = true)
    (hT : (c.get 2 + 0x14#32).toNat % 4 = 0) (hTr : B.inRam (c.get 2 + 0x14#32) 4 = true)
    (hsep : (c.get 5).toNat + (4 - o) ≤ (c.get 2 + 0x14#32).toNat ∨ (c.get 2 + 0x14#32).toNat + 4 ≤ (c.get 5).toNat)
    (hlp : (c.get 30 + 0x4#32).ult (c.get 13) = true) :
    ∃ n g R', QRun B img n ⟨c, R⟩ ⟨g, R'⟩ ∧ AtLoop c g R R' o := by
  have hsr' := (B_ram _ _).mp hsr
  rcases (by omega : o = 1 ∨ o = 2 ∨ o = 3) with rfl | rfl | rfl
  · obtain ⟨g, R', hr, ha⟩ := start1 c R hpc hq h6 hsr (by bv_omega) hT hTr hsep hlp
    exact ⟨_, g, R', hr, ha⟩
  · obtain ⟨g, R', hr, ha⟩ := start2 c R hpc hq h6 hsr (by omega) hT hTr hsep hlp
    exact ⟨_, g, R', hr, ha⟩
  · obtain ⟨g, R', hr, ha⟩ := start3 c R hpc hq h6 hsr hT hTr (by omega) hlp
    exact ⟨_, g, R', hr, ha⟩

theorem end_any (g : Core) (R0 : Word → BitVec 8) (o : Nat) (ho : 0 < o ∧ o < 4) (hpc : g.pc = 0x80020f4c)
    (hq : Quiet g) (h6 : g.get 6 = BitVec.ofNat 32 o) (h28 : g.get 28 = BitVec.ofNat 32 (8 * o))
    (h5 : (g.get 5).toNat % 2 = o % 2)
    (hprev : ∀ k, o ≤ k → k < 4 → byteOf (g.get 15) k = R0 (g.get 11 + BitVec.ofNat 32 k))
    (hsrc : B.inRam (g.get 11 + 4#32) o = true)
    (ht10 : B.inRam (g.get 2 + 0x10#32) 1 = true) (ht0e : B.inRam (g.get 2 + 0xe#32) 1 = true)
    (hsep : ∀ j < o, g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0x10#32 ∧
      g.get 11 + 4#32 + BitVec.ofNat 32 j ≠ g.get 2 + 0xe#32)
    (hD : (g.get 30).toNat % 4 = 0) (hDr : B.inRam (g.get 30) 4 = true) :
    ∃ n g' R', QRun B img n ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtTail g g' R0 R' o := by
  rcases (by omega : o = 1 ∨ o = 2 ∨ o = 3) with rfl | rfl | rfl
  · obtain ⟨g', R', hr, ha⟩ := end1 g R0 hpc hq h6 h28 (by omega) hprev hsrc ht10 ht0e hsep hD hDr
    exact ⟨_, g', R', hr, ha⟩
  · obtain ⟨g', R', hr, ha⟩ := end2 g R0 hpc hq h6 h28 (by omega) hprev hsrc ht10 ht0e hsep hD hDr
    exact ⟨_, g', R', hr, ha⟩
  · obtain ⟨g', R', hr, ha⟩ := end3 g R0 hpc hq h6 h28 (by omega) hprev hsrc ht10 ht0e hsep hD hDr
    exact ⟨_, g', R', hr, ha⟩

/-! ## The whole misaligned forward path -/

/-- memmove's own stack frame below `sp`. -/
def InFrame (sp x : Word) : Prop := sp.toNat - 48 ≤ x.toNat ∧ x.toNat < sp.toNat

/-- The misaligned path's stack temporaries: sp' + 0xe .. sp' + 0x18 with sp' = sp - 48. -/
def InTemps (sp x : Word) : Prop := sp.toNat - 34 ≤ x.toNat ∧ x.toNat < sp.toNat - 24

/-- The RAM of the misaligned path, outside memmove's frame (abstract, small context). -/
theorem mis_ram (R0 R2 Rt : Word → BitVec 8) (s d sp H W T : Word) (n j : Nat)
    (hsum : H.toNat + W.toNat + T.toNat = n) (hj : 4 * (j + 1) + 4 = W.toNat) (hH : H.toNat < 4)
    (hs : s.toNat + n ≤ 0x81000000) (hd : d.toNat + n ≤ 0x81000000)
    (hs0 : 0x80029bc8 ≤ s.toNat) (hd0 : 0x80029bc8 ≤ d.toNat)
    (hfr : 0x80029bc8 + 48 ≤ sp.toNat ∧ sp.toNat ≤ 0x81000000)
    (hdir : d.toNat ≤ s.toNat ∨ s.toNat + n ≤ d.toNat)
    (hsepd : d.toNat + n + 48 ≤ sp.toNat ∨ sp.toNat ≤ d.toNat)
    (hseps : s.toNat + n + 48 ≤ sp.toNat ∨ sp.toNat ≤ s.toNat)
    (hal : (d + H).toNat % 4 = 0)
    (hZ2 : ∀ y, ¬ InTemps sp y → R2 y = fwd R0 s d H.toNat y)
    (hRt : ∀ y, ¬ InTemps sp y → Rt y = words R2 (s + H) (d + H) (j + 1) y) :
    ∀ x, ¬ InTemps sp x →
      fwd (ramWrite Rt (d + H + BitVec.ofNat 32 (4 * (j + 1)))
          (ramRead (words R2 (s + H) (d + H) (j + 1)) (s + H + BitVec.ofNat 32 (4 * (j + 1))) .w) .w)
        (s + H + W) (d + H + W) T.toNat x = fwd R0 s d n x := by
  intro x hx
  let Z := InTemps sp
  let R1 := fwd R0 s d H.toNat
  let F1 := fwd R1 (s + H) (d + H) (4 * (j + 1))
  have nZs : ∀ i, i < n - H.toNat → ¬ Z (s + H + BitVec.ofNat 32 i) := by
    intro i hi hz; simp only [Z, InTemps] at hz; bv_omega
  have nZd : ∀ i, i < n - H.toNat → ¬ Z (d + H + BitVec.ofNat 32 i) := by
    intro i hi hz; simp only [Z, InTemps] at hz; bv_omega
  have hloop : words R2 (s + H) (d + H) (j + 1) = fwd R2 (s + H) (d + H) (4 * (j + 1)) :=
    words_eq_fwd _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)
  have hZl : ∀ y, ¬ Z y → words R2 (s + H) (d + H) (j + 1) y = F1 y := by
    intro y hy; rw [hloop]
    exact fwd_frame Z _ _ _ _ _ hZ2 (fun i hi => nZs i (by omega)) (fun i hi => nZd i (by omega)) y hy
  have hZ3 : ∀ y, ¬ Z y → ramWrite Rt (d + H + BitVec.ofNat 32 (4 * (j + 1)))
      (ramRead (words R2 (s + H) (d + H) (j + 1)) (s + H + BitVec.ofNat 32 (4 * (j + 1))) .w) .w y =
      fwd F1 (s + H + BitVec.ofNat 32 (4 * (j + 1))) (d + H + BitVec.ofNat 32 (4 * (j + 1))) 4 y := by
    intro y hy
    rw [word_spec2 _ _ _ _ _ (by bv_omega), fwd_spec _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)]
    split
    · exact hZl _ (by intro hz; simp only [Z, InTemps] at hz; bv_omega)
    · rw [hRt y hy]; exact hZl y hy
  have hF2 : fwd F1 (s + H + BitVec.ofNat 32 (4 * (j + 1))) (d + H + BitVec.ofNat 32 (4 * (j + 1))) 4 =
      fwd R1 (s + H) (d + H) (4 * (j + 1) + 4) := by rw [fwd_add]
  rw [fwd_frame Z _ _ (fwd R1 (s + H) (d + H) (4 * (j + 1) + 4)) _ _ (fun y hy => by rw [hZ3 y hy, hF2])
    (fun i hi => by
      have := nZs (W.toNat + i) (by omega)
      rwa [show s + H + BitVec.ofNat 32 (W.toNat + i) = s + H + W + BitVec.ofNat 32 i by bv_omega] at this)
    (fun i hi => by
      have := nZd (W.toNat + i) (by omega)
      rwa [show d + H + BitVec.ofNat 32 (W.toNat + i) = d + H + W + BitVec.ofNat 32 i by bv_omega] at this) x hx]
  rw [show s + H + W = s + H + BitVec.ofNat 32 (4 * (j + 1) + 4) by bv_omega,
    show d + H + W = d + H + BitVec.ofNat 32 (4 * (j + 1) + 4) by bv_omega, ← fwd_add,
    show n = H.toNat + (4 * (j + 1) + 4 + T.toNat) by omega, fwd_add H.toNat]
  show fwd R1 (s + H) (d + H) _ x = fwd R1 _ _ _ x
  rw [show s + BitVec.ofNat 32 H.toNat = s + H by simp, show d + BitVec.ofNat 32 H.toNat = d + H by simp]

set_option maxHeartbeats 40000000 in
theorem big_mis (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : 16 ≤ (c.get 12).toNat) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = false)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true)
    (hnc : (c.get 11).toNat % 4 ≠ (c.get 10).toNat % 4)
    (hsp : (c.get 2).toNat % 4 = 0) (hfr : 0x80029bc8 + 48 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
    (hsepd : (c.get 10).toNat + (c.get 12).toNat + 48 ≤ (c.get 2).toNat ∨ (c.get 2).toNat ≤ (c.get 10).toNat)
    (hseps : (c.get 11).toNat + (c.get 12).toNat + 48 ≤ (c.get 2).toNat ∨ (c.get 2).toNat ≤ (c.get 11).toNat) :
    ∃ k e Rf, QRun B img k ⟨Memmove.pro c, R0⟩ ⟨e, Rf⟩ ∧ e.pc = 0x800210b0 ∧
      Memmove.Frame c e [5, 7, 9, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] ∧
      ∀ x, ¬ InTemps (c.get 2) x → Rf x = fwd R0 (c.get 11) (c.get 10) (c.get 12).toNat x := by
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hHl := Memmove.headN_lt (c.get 10)
  have hHa := Memmove.headN_al (c.get 10)
  have hdirN : (c.get 10).toNat ≤ (c.get 11).toNat ∨ (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat := by
    simp only [BitVec.ult, decide_eq_false_iff_not] at hdir; bv_omega
  obtain ⟨k1, g, hr1, hm⟩ := Memmove.big_entry c R0 hq hn hdir hd hs
  have qg : Quiet g := Quiet.of_sameCsr hm.csr hq
  have hsH3 := Memmove.and3 (c.get 11 + Memmove.headN (c.get 10))
  have hmis : (g.get 11 + g.get 16) &&& 3#32 ≠ 0 := by
    rw [hm.r11, hm.r16]; intro h0
    have := congrArg BitVec.toNat h0; rw [hsH3] at this; simp at this; bv_omega
  obtain ⟨h, hr2, hmi⟩ := mis_mid g (fwd R0 (c.get 11) (c.get 10) (Memmove.headN (c.get 10)).toNat) hm.pc qg hmis
  have qh : Quiet h := Quiet.of_sameCsr (hmi.csr.trans hm.csr) hq
  -- the quantities
  have h5 : h.get 5 = c.get 11 + Memmove.headN (c.get 10) := by rw [hmi.r5, hm.r11, hm.r16]
  have h16 : h.get 16 = c.get 12 - Memmove.headN (c.get 10) := by rw [hmi.r16, hm.r12, hm.r16]
  have h17 : h.get 17 = (c.get 12 - Memmove.headN (c.get 10)) &&& 0xfffffffc#32 := by
    rw [hmi.r17, hm.r12, hm.r16]
  have h6 : h.get 6 = (c.get 11 + Memmove.headN (c.get 10)) &&& 3#32 := by rw [hmi.r6, hm.r11, hm.r16]
  have h30 : h.get 30 = c.get 10 + Memmove.headN (c.get 10) := by
    rw [hmi.frame 30 (by decide), hm.r30]
  have h13 : h.get 13 = c.get 10 + Memmove.headN (c.get 10) + ((c.get 12 - Memmove.headN (c.get 10)) &&& 0xfffffffc#32) := by
    rw [hmi.r13, hm.r30, hm.r12, hm.r16]
  have h2 : h.get 2 = c.get 2 + 0xffffffd0#32 := by rw [hmi.frame 2 (by decide), hm.sp]
  have hW := Memmove.andm4 (c.get 12 - Memmove.headN (c.get 10))
  have hnH : (c.get 12 - Memmove.headN (c.get 10)).toNat = (c.get 12).toNat - (Memmove.headN (c.get 10)).toNat := by
    bv_omega
  -- names
  have hHd : (c.get 10 + Memmove.headN (c.get 10)).toNat = (c.get 10).toNat + (Memmove.headN (c.get 10)).toNat := by
    bv_omega
  have hHs : (c.get 11 + Memmove.headN (c.get 10)).toNat = (c.get 11).toNat + (Memmove.headN (c.get 10)).toNat := by
    bv_omega
  let o := (c.get 11 + Memmove.headN (c.get 10)).toNat % 4
  have ho : 0 < o ∧ o < 4 := by
    constructor
    · have : (c.get 11 + Memmove.headN (c.get 10)).toNat % 4 ≠ 0 := by bv_omega
      omega
    · omega
  have h6o : h.get 6 = BitVec.ofNat 32 o := by
    rw [h6]; apply BitVec.eq_of_toNat_eq; rw [hsH3]; simp; omega
  let W := (c.get 12 - Memmove.headN (c.get 10)) &&& 0xfffffffc#32
  have hWv : W.toNat = (c.get 12).toNat - (Memmove.headN (c.get 10)).toNat -
      ((c.get 12).toNat - (Memmove.headN (c.get 10)).toNat) % 4 := by rw [← hnH]; exact hW
  have hW12 : 12 ≤ W.toNat := by omega
  obtain ⟨j, hj⟩ : ∃ j, 4 * (j + 1) + 4 = W.toNat := ⟨W.toNat / 4 - 2, by omega⟩
  -- the stack temporary
  have hT : (h.get 2 + 0x14#32).toNat % 4 = 0 := by rw [h2]; bv_omega
  have hTr : B.inRam (h.get 2 + 0x14#32) 4 = true := by rw [h2, B_ram]; constructor <;> bv_omega
  obtain ⟨n2, g7, R2, hr3, hl⟩ := start_any h (fwd R0 (c.get 11) (c.get 10) (Memmove.headN (c.get 10)).toNat) o ho
    hmi.pc qh h6o (by rw [h5]) (by rw [h5, B_ram]; constructor <;> bv_omega) hT hTr
    (by rw [h5, h2]; bv_omega)
    (by rw [h30, h13]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega)
  have qg7 : Quiet g7 := Quiet.of_sameCsr (hl.csr.trans (hmi.csr.trans hm.csr)) hq
  have l30 : g7.get 30 = c.get 10 + Memmove.headN (c.get 10) := by rw [hl.frame 30 (by decide), h30]
  have l13 : g7.get 13 = c.get 10 + Memmove.headN (c.get 10) + W := by rw [hl.frame 13 (by decide), h13]
  have l11 : g7.get 11 = c.get 11 + Memmove.headN (c.get 10) - BitVec.ofNat 32 o := by rw [hl.a1, h5]
  have hA : (g7.get 11).toNat % 4 = 0 := by rw [l11]; bv_omega
  obtain ⟨n3, g8, hr4, hpc8, hcs8, h8_11, h8_30, h8_28, h8_13, h8_12, hpv8, hfr8⟩ :=
    mis_loop o ho j g7 R2 hl.pc qg7 hl.t3 hl.a2 (by rw [l13, l30]; bv_omega) (by rw [l30]; bv_omega)
      (by rw [l11]; bv_omega) hA (by rw [l30]; exact hHa) (by rw [l30, l11]; bv_omega)
      (fun k a b => by rw [hl.prev k a b, l11, h5])
      (by rw [l11, B_ram]; constructor <;> bv_omega) (by rw [l30, B_ram]; constructor <;> bv_omega)
  have qg8 : Quiet g8 := Quiet.of_sameCsr hcs8 qg7
  have g8_5 : g8.get 5 = c.get 11 + Memmove.headN (c.get 10) := by
    rw [hfr8 5 (by decide) (by decide) (by decide) (by decide) (by decide), hl.frame 5 (by decide), h5]
  have g8_6 : g8.get 6 = BitVec.ofNat 32 o := by
    rw [hfr8 6 (by decide) (by decide) (by decide) (by decide) (by decide), hl.frame 6 (by decide), h6o]
  have g8_2 : g8.get 2 = c.get 2 + 0xffffffd0#32 := by
    rw [hfr8 2 (by decide) (by decide) (by decide) (by decide) (by decide), hl.frame 2 (by decide), h2]
  have hRl := (B_ram _ _).mp hTr
  obtain ⟨n4, g9, R3, hr5, ht⟩ := end_any g8 (words R2 (g7.get 11 + BitVec.ofNat 32 o) (g7.get 30) (j + 1)) o ho
    hpc8 qg8 g8_6 (by rw [h8_28, hl.t3]) (by rw [g8_5]; omega) hpv8
    (by rw [h8_11, l11, B_ram]; constructor <;> bv_omega)
    (by rw [g8_2, B_ram]; constructor <;> bv_omega) (by rw [g8_2, B_ram]; constructor <;> bv_omega)
    (fun jj hjj => by rw [h8_11, l11, g8_2]; constructor <;> bv_omega)
    (by rw [h8_30, l30]; bv_omega) (by rw [h8_30, l30, B_ram]; constructor <;> bv_omega)
  have qg9 : Quiet g9 := Quiet.of_sameCsr ht.csr qg8
  have g9_5 : g9.get 5 = c.get 11 + Memmove.headN (c.get 10) := by rw [ht.frame 5 (by decide), g8_5]
  have g9_17 : g9.get 17 = W := by
    rw [ht.frame 17 (by decide), hfr8 17 (by decide) (by decide) (by decide) (by decide) (by decide),
      hl.frame 17 (by decide), h17]
  have g9_16 : g9.get 16 = c.get 12 - Memmove.headN (c.get 10) := by
    rw [ht.frame 16 (by decide), hfr8 16 (by decide) (by decide) (by decide) (by decide) (by decide),
      hl.frame 16 (by decide), h16]
  have g9_13 : g9.get 13 = c.get 10 + Memmove.headN (c.get 10) + W := by
    rw [ht.frame 13 (by decide), h8_13, l13]
  have hT3 := Memmove.and3 (c.get 12 - Memmove.headN (c.get 10))
  obtain ⟨n5, e, hr6, hpe, hcse, hfre⟩ := tail_dispatch g9 R3 ht.pc qg9
    (by rw [g9_5, g9_17, g9_16, B_ram]; constructor <;> bv_omega)
    (by rw [g9_13, g9_16, B_ram]; constructor <;> bv_omega)
  refine ⟨k1 + 6 + n2 + n3 + n4 + n5, e, _, ((((hr1.trans hr2).trans hr3).trans hr4).trans hr5).trans hr6, hpe,
    ⟨hcse.trans (ht.csr.trans (hcs8.trans (hl.csr.trans (hmi.csr.trans hm.csr)))), ?_, ?_⟩, ?_⟩
  · rw [hfre 2 (by decide) (by decide) (by decide) (by decide), ht.frame 2 (by decide), g8_2]
  · intro r hr
    have ne : ∀ q : Nat, q ∈ [2, 6, 5, 7, 9, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] → r.val ≠ q := by
      intro q hq e; exact hr (e ▸ hq)
    have r11 : r ≠ 11 := fun e => ne 11 (by simp) (by subst e; rfl)
    have r12 : r ≠ 12 := fun e => ne 12 (by simp) (by subst e; rfl)
    have r13 : r ≠ 13 := fun e => ne 13 (by simp) (by subst e; rfl)
    have r14 : r ≠ 14 := fun e => ne 14 (by simp) (by subst e; rfl)
    have r9 : r ≠ 9 := fun e => ne 9 (by simp) (by subst e; rfl)
    have r15 : r ≠ 15 := fun e => ne 15 (by simp) (by subst e; rfl)
    have r30 : r ≠ 30 := fun e => ne 30 (by simp) (by subst e; rfl)
    rw [hfre r r11 r12 r13 r14, ht.frame r (by
        intro hm'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'; apply hr; simp only [List.mem_cons,
          List.not_mem_nil, or_false]; omega),
      hfr8 r r9 r11 r14 r15 r30, hl.frame r (by
        intro hm'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'; apply hr; simp only [List.mem_cons,
          List.not_mem_nil, or_false]; omega),
      hmi.frame r (by
        intro hm'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'; apply hr; simp only [List.mem_cons,
          List.not_mem_nil, or_false]; omega),
      hm.frame r (by
        intro hm'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'; apply hr; simp only [List.mem_cons,
          List.not_mem_nil, or_false]; omega)]
  · -- RAM: everything outside memmove's frame is the forward copy of n bytes
    intro x hx
    obtain ⟨Rt, hRt, hR3⟩ := ht.ram
    have hl11 : g7.get 11 + BitVec.ofNat 32 o = c.get 11 + Memmove.headN (c.get 10) := by rw [l11]; bv_omega
    have e30 : g8.get 30 = c.get 10 + Memmove.headN (c.get 10) + BitVec.ofNat 32 (4 * (j + 1)) := by rw [h8_30, l30]
    have e11 : g8.get 11 + BitVec.ofNat 32 o =
        c.get 11 + Memmove.headN (c.get 10) + BitVec.ofNat 32 (4 * (j + 1)) := by rw [h8_11, l11]; bv_omega
    rw [hl11, l30] at hR3 hRt
    rw [e30, e11] at hR3
    rw [g9_5, g9_17, g9_13, g9_16, hR3]
    have hT3' : (c.get 12 - Memmove.headN (c.get 10) &&& 3#32).toNat =
        ((c.get 12).toNat - (Memmove.headN (c.get 10)).toNat) % 4 := by rw [hT3, hnH]
    exact mis_ram R0 R2 Rt (c.get 11) (c.get 10) (c.get 2) (Memmove.headN (c.get 10)) W
      (c.get 12 - Memmove.headN (c.get 10) &&& 3#32) (c.get 12).toNat j
      (by rw [hT3']; omega) hj hHl hsr.2 hdr.2 hsr.1 hdr.1 hfr hdirN hsepd hseps hHa
      (fun y hy => hl.ram y (by rw [h2]; intro ht'; apply hy; unfold InTemps; bv_omega))
      (fun y hy => hRt y (by rw [g8_2]; intro e'; apply hy; subst e'; unfold InTemps; bv_omega)
        (by rw [g8_2]; intro e'; apply hy; subst e'; unfold InTemps; bv_omega)) x hx

end E5R.Rmk
