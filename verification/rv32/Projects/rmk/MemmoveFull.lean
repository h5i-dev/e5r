/-
  The emitted memmove (pinned RMK image), every case but one: n < 16 in
  either direction, and n ≥ 16 forward (dst - src ≥ n unsigned) whatever
  the alignment. NOT COVERED: n ≥ 16 backward (dst inside the source,
  above it), the path `park_pending` takes.

  Original e5r code, Apache-2.0.

  The callee's stack frame is the 48 bytes below sp: the misaligned path
  uses stack temporaries there besides the three save slots, so RAM is
  claimed outside [sp - 48, sp), and dst/src must lie outside it.
-/
import Projects.rmk.MemmoveMis
import Projects.rmk.MemmoveContract

set_option maxRecDepth 100000

namespace E5R.Rmk.Memmove
open E5R E5R.Rmk

structure PreF (m : Machine) : Prop where
  pc : m.core.pc = 0x80020c1e
  quiet : Quiet m.core
  case : (m.core.get 12).toNat < 16 ∨ (m.core.get 10 - m.core.get 11).ult (m.core.get 12) = false
  dst : B.inRam (m.core.get 10) (m.core.get 12).toNat = true
  src : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  spAl : (m.core.get 2).toNat % 4 = 0
  stack : 0x80029bc8 + 48 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  dstSep : (m.core.get 10).toNat + (m.core.get 12).toNat + 48 ≤ (m.core.get 2).toNat ∨
    (m.core.get 2).toNat ≤ (m.core.get 10).toNat
  srcSep : (m.core.get 11).toNat + (m.core.get 12).toNat + 48 ≤ (m.core.get 2).toNat ∨
    (m.core.get 2).toNat ≤ (m.core.get 11).toNat
  ra : (m.core.get 1).getLsbD 0 = false

structure PostF (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  regs : ∀ r : Reg, r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : ∀ x, ¬ InFrame (m₀.core.get 2) x →
    m.ram x = moved m₀.ram (m₀.core.get 10) (m₀.core.get 11) (m₀.core.get 12).toNat x

theorem finishC (c : Core) (ram R : Word → BitVec 8) (e : Core) (w : List Nat) (hq : Quiet c)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true)
    (hs : B.inRam (c.get 11) (c.get 12).toNat = true) (hsl : Slots (c.get 2)) (hfr : 0x80029bc8 + 48 ≤ (c.get 2).toNat)
    (hdsep : (c.get 2).toNat ≤ (c.get 10).toNat ∨ (c.get 10).toNat + (c.get 12).toNat + 12 ≤ (c.get 2).toNat)
    (hssep : (c.get 2).toNat ≤ (c.get 11).toNat ∨ (c.get 11).toNat + (c.get 12).toNat + 12 ≤ (c.get 2).toNat)
    (hra : (c.get 1).getLsbD 0 = false) (he : e.pc = 0x800210b0) (hfr : Frame c e w)
    (hw : ∀ r : Reg, r.val ∈ w → r.val ∈ [9, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31])
    (hR : ∀ x, ¬ InTemps (c.get 2) x → R x = moved (saved c ram) (c.get 10) (c.get 11) (c.get 12).toNat x) :
    ∃ m, QRun B img 5 ⟨e, R⟩ m ∧ PostF ⟨c, ram⟩ m := by
  obtain ⟨hcs, hsp, hfr⟩ := hfr
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hslr := hsl.ram
  have e1 : e.get 1 = c.get 1 := hfr 1 (by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    have := hw 1 h; revert this; decide)
  have hep := epilogue e R (c.get 2 + 0xffffffd0#32) he (Quiet.of_sameCsr hcs hq) hsp (by rw [e1]; exact hra)
    (hsl.al' 0x2c (by decide)) (hsl.al' 0x28 (by decide)) (hsl.al' 0x24 (by decide))
    (hsl.in' 0x2c (by decide)) (hsl.in' 0x28 (by decide)) (hsl.in' 0x24 (by decide))
  -- RAM outside the destination is the saved RAM, in particular at the slots.
  have hRout : ∀ x, ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + (c.get 12).toNat) →
      ¬ InTemps (c.get 2) x → R x = saved c ram x := by
    intro x hx ht; rw [hR x ht, moved, if_neg hx]
  have slot : ∀ k, (k = 0x2c ∨ k = 0x28 ∨ k = 0x24) →
      ramRead R (c.get 2 + 0xffffffd0#32 + BitVec.ofNat 32 k) .w =
        ramRead (saved c ram) (c.get 2 + 0xffffffd0#32 + BitVec.ofNat 32 k) .w := by
    intro k hk
    apply ramRead_congr
    intro j hj
    apply hRout
    · rcases hk with rfl | rfl | rfl <;> bv_omega
    · unfold InTemps; rcases hk with rfl | rfl | rfl <;> bv_omega
  obtain ⟨r8, r9, r18⟩ := saved_read c ram
  refine ⟨⟨epi e R (c.get 2 + 0xffffffd0#32), R⟩, hep, ?_, ?_, ?_, ?_⟩
  · show (epi e R _).pc = c.get 1; simp [epi, e1]
  · intro r hr
    by_cases h8 : r = 8
    · subst h8; simp only [epi, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (8 : Reg) ≠ 2 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (8 : Reg) ≠ 18 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (8 : Reg) ≠ 9 by decide), Core.wr_get_self _ (8 : Reg) _ _ (by decide)]
      rw [slot 0x2c (by decide)]; exact r8
    by_cases h9 : r = 9
    · subst h9; simp only [epi, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 2 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 18 by decide), Core.wr_get_self _ (9 : Reg) _ _ (by decide)]
      rw [slot 0x28 (by decide)]; exact r9
    by_cases h18 : r = 18
    · subst h18; simp only [epi, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (18 : Reg) ≠ 2 by decide),
        Core.wr_get_self _ (18 : Reg) _ _ (by decide)]
      rw [slot 0x24 (by decide)]; exact r18
    by_cases h2 : r = 2
    · subst h2; simp only [epi, Core.goto_get, Core.wr_get_self _ (2 : Reg) _ _ (by decide)]
      show c.get 2 + 0xffffffd0#32 + 0x30#32 = c.get 2; bv_omega
    simp only [epi, Core.goto_get, Core.wr_get_ne _ _ _ _ _ h2, Core.wr_get_ne _ _ _ _ _ h18,
      Core.wr_get_ne _ _ _ _ _ h9, Core.wr_get_ne _ _ _ _ _ h8]
    apply hfr r
    intro hm
    have h6 : r.val ≠ 6 := fun e => hr (by simp [e])
    have h2' : r.val ≠ 2 := fun e => h2 (Fin.ext e)
    simp only [List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact h2' hm
    · exact h6 hm
    · have := hw r hm
      have h9' : r.val ≠ 9 := fun e => h9 (Fin.ext e)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this hr
      omega
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans hcs))))
  · intro x hx
    show R x = _
    rw [hR x (by unfold InFrame at hx; unfold InTemps; bv_omega)]; unfold moved; unfold InFrame at hx
    by_cases hin : (c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + (c.get 12).toNat
    · rw [if_pos hin, if_pos hin]
      exact saved_other c ram hsl _ (by unfold InSlots; bv_omega)
    · rw [if_neg hin, if_neg hin]
      exact saved_other c ram hsl _ (by unfold InSlots; bv_omega)

/-- **memmove, forward and small copies.** -/
theorem contractF (m₀ : Machine) (h : PreF m₀) : ∃ k m, QRun B img k m₀ m ∧ PostF m₀ m := by
  obtain ⟨c, ram⟩ := m₀
  obtain ⟨hpc, hq, hcase, hd, hs, hspal, hst, hdsep, hssep, hra⟩ := h
  simp only at hpc hq hcase hd hs hspal hst hdsep hssep hra ⊢
  have hsl : Slots (c.get 2) := ⟨hspal, by omega⟩
  have hpro := prologue c ram hpc hq hsl
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hdsep' : (c.get 2).toNat ≤ (c.get 10).toNat ∨ (c.get 10).toNat + (c.get 12).toNat + 12 ≤ (c.get 2).toNat := by
    omega
  have hssep' : (c.get 2).toNat ≤ (c.get 11).toNat ∨ (c.get 11).toNat + (c.get 12).toNat + 12 ≤ (c.get 2).toNat := by
    omega
  cases hdir : (c.get 10 - c.get 11).ult (c.get 12) with
  | false =>
    have hdirN : (c.get 10).toNat ≤ (c.get 11).toNat ∨ (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat := by
      simp only [BitVec.ult, decide_eq_false_iff_not] at hdir; bv_omega
    have hR : ∀ x, fwd (saved c ram) (c.get 11) (c.get 10) (c.get 12).toNat x =
        moved (saved c ram) (c.get 10) (c.get 11) (c.get 12).toNat x := fun x => by
      rw [fwd_spec _ _ _ _ _ (by omega) (by omega) hdirN]; rfl
    by_cases hsm : (c.get 12).toNat < 16
    · obtain ⟨k, e, hr, he, hfr⟩ := fwd_path c (saved c ram) hq hsm hdir hd hs
      obtain ⟨m, hm, hpost⟩ := finishC c ram (fwd (saved c ram) (c.get 11) (c.get 10) (c.get 12).toNat) e
        [11, 12, 13, 14] hq hd hs hsl hst.1 hdsep' hssep' hra he hfr
        (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega) (fun x _ => hR x)
      exact ⟨7 + k + 5, m, (hpro.trans hr).trans hm, hpost⟩
    · by_cases hcong : (c.get 11).toNat % 4 = (c.get 10).toNat % 4
      · obtain ⟨k, e, hr, he, hfr⟩ := big_aligned c (saved c ram) hq (by omega) hdir hd hs hcong
        obtain ⟨m, hm, hpost⟩ := finishC c ram (fwd (saved c ram) (c.get 11) (c.get 10) (c.get 12).toNat) e
          [5, 9, 11, 12, 13, 14, 15, 16, 17, 30] hq hd hs hsl hst.1 hdsep' hssep' hra he hfr
          (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega) (fun x _ => hR x)
        exact ⟨7 + k + 5, m, (hpro.trans hr).trans hm, hpost⟩
      · obtain ⟨k, e, Rf, hr, he, hfr, hRf⟩ := big_mis c (saved c ram) hq (by omega) hdir hd hs hcong hspal hst
          hdsep hssep
        obtain ⟨m, hm, hpost⟩ := finishC c ram Rf e
          [5, 7, 9, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] hq hd hs hsl hst.1 hdsep' hssep' hra he hfr
          (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
          (fun x hx => by rw [hRf x hx]; exact hR x)
        exact ⟨7 + k + 5, m, (hpro.trans hr).trans hm, hpost⟩
  | true =>
    have hsm : (c.get 12).toNat < 16 := by
      rcases hcase with h | h
      · exact h
      · rw [hdir] at h; cases h
    obtain ⟨k, e, hr, he, hfr⟩ := bwd_path c (saved c ram) hq hsm hdir hd hs
    obtain ⟨m, hm, hpost⟩ := finishC c ram
      (bwd (saved c ram) (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (c.get 12).toNat) e
      [9, 11, 12, 13, 16] hq hd hs hsl hst.1 hdsep' hssep' hra he hfr
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
      (fun x _ => by
        have hle : (c.get 11).toNat ≤ (c.get 10).toNat := by
          simp only [BitVec.ult, decide_eq_true_iff] at hdir; bv_omega
        rw [bwd_spec _ _ _ _ _ (by bv_omega) (by bv_omega)]
        unfold moved
        have hq : (c.get 10 + c.get 12).toNat = (c.get 10).toNat + (c.get 12).toNat := by bv_omega
        rw [hq, show (c.get 10).toNat + (c.get 12).toNat - (c.get 12).toNat = (c.get 10).toNat by omega]
        split
        · exact congrArg _ (by bv_omega)
        · rfl)
    exact ⟨7 + k + 5, m, (hpro.trans hr).trans hm, hpost⟩

end E5R.Rmk.Memmove
