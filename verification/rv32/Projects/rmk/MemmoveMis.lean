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

end E5R.Rmk
