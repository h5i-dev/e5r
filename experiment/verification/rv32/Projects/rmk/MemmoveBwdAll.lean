/-
  memmove (pinned RMK image): the backward misaligned path composed, and
  the contract for every size, direction and alignment.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.MemmoveBwdMis

set_option maxRecDepth 100000

namespace E5R.Rmk.Memmove
open E5R E5R.Rmk E5R.Rmk.MemmoveFetch

/-- The tail-byte arithmetic of the backward paths (no alignment premise). -/
theorem btail_arith (d s n H A W T : Word)
    (hdr : 0x80029bc8 ≤ d.toNat ∧ d.toNat + n.toNat ≤ 0x81000000)
    (hsr : 0x80029bc8 ≤ s.toNat ∧ s.toNat + n.toNat ≤ 0x81000000)
    (hn : 16 ≤ n.toNat) (hle : s.toNat ≤ d.toNat)
    (hH : H.toNat = (d + n).toNat % 4) (hA : A.toNat = (d + n).toNat - (d + n).toNat % 4)
    (hW : W.toNat = (n - H).toNat - (n - H).toNat % 4) (hT : T.toNat = (n - H).toNat % 4) :
    T.toNat ≤ (A - W).toNat ∧ T.toNat ≤ (s + n - H - W).toNat ∧
    B.inRam (A - W - T) T.toNat = true ∧ B.inRam (s + n - H - W - T) T.toNat = true ∧
    12 ≤ W.toNat ∧ W.toNat % 4 = 0 := by
  have hD : (d + n).toNat = d.toNat + n.toNat := by bv_omega
  have hH4 : H.toNat < 4 := by omega
  have hM : (n - H).toNat = n.toNat - H.toNat := by bv_omega
  have kA : A.toNat + H.toNat = d.toNat + n.toNat := by omega
  have kW : W.toNat + T.toNat + H.toNat = n.toNat := by omega
  have kT : T.toNat < 4 := by omega
  have kW4 : W.toNat % 4 = 0 := by omega
  clear hH hA hW hT hD hM
  refine ⟨by bv_omega, by bv_omega, (B_ram _ _).mpr ⟨by bv_omega, by bv_omega⟩,
    (B_ram _ _).mpr ⟨by bv_omega, by bv_omega⟩, by omega, kW4⟩

theorem inTB_of (sp y : Word) (k : Nat) (hk : k = 0x1a ∨ k = 0x20)
    (hst : 0x80029bc8 + 48 ≤ sp.toNat ∧ sp.toNat ≤ 0x81000000)
    (h : (sp + 0xffffffd0#32 + BitVec.ofNat 32 k).toNat ≤ y.toNat ∧
      y.toNat < (sp + 0xffffffd0#32 + BitVec.ofNat 32 k).toNat + 4) : InTB sp y := by
  unfold InTB; rcases hk with rfl | rfl <;> bv_omega

/-- Backward, n ≥ 16, src and dst NOT congruent mod 4: the whole path. -/
theorem bwd_mis (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : 16 ≤ (c.get 12).toNat) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = true)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true)
    (hnc : (c.get 11).toNat % 4 ≠ (c.get 10).toNat % 4)
    (hspa : (c.get 2).toNat % 4 = 0) (hst : 0x80029bc8 + 48 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
    (hdsep : (c.get 10).toNat + (c.get 12).toNat + 48 ≤ (c.get 2).toNat ∨ (c.get 2).toNat ≤ (c.get 10).toNat)
    (hssep : (c.get 11).toNat + (c.get 12).toNat + 48 ≤ (c.get 2).toNat ∨ (c.get 2).toNat ≤ (c.get 11).toNat) :
    ∃ k e Rf, QRun B img k ⟨pro c, R0⟩ ⟨e, Rf⟩ ∧ e.pc = 0x800210b0 ∧
      Frame c e [5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 28, 29, 30, 31] ∧
      ∀ x, ¬ InTB (c.get 2) x →
        Rf x = bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (c.get 12).toNat x := by
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hle : (c.get 11).toNat ≤ (c.get 10).toNat := by
    simp only [BitVec.ult, decide_eq_true_iff] at hdir; bv_omega
  obtain ⟨t1, t2, t3, t4, tW, tW4⟩ := btail_arith (c.get 10) (c.get 11) (c.get 12) (bH c) (bA c) (bW c)
    ((c.get 12 - bH c) &&& 3#32) hdr hsr hn hle (and3 _) (andm4 _) (andm4 _) (and3 _)
  let j := (bW c).toNat / 4 - 2
  have hJ : 4 * (j + 1 + 1) = (bW c).toNat := by omega
  let o := (c.get 11 + c.get 12 - bH c).toNat % 4
  have am := bmis_arith (c.get 10) (c.get 11) (c.get 12) (c.get 2) (bH c) (bA c) (bW c)
    ((c.get 12 - bH c) &&& 3#32) o (j + 1) hdr hsr hn hle hnc (and3 _) (andm4 _) (andm4 _) (and3 _)
    hspa hst hdsep hssep rfl hJ
  obtain ⟨k1, g, hr1, hb⟩ := bwd_entry c R0 hq hn hdir hd hs
  let R1 := bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (bH c).toNat
  obtain ⟨g6, hr2, hm⟩ := bwd_mid c g R1 hq hb
  have q6 : Quiet g6 := Quiet.of_sameCsr hm.csr hq
  -- start block
  obtain ⟨k3, g', R', hr3, hl⟩ := bstart_any g6 R1 o am.ho hm.pc q6 (by rw [hm.r6]; exact am.o6)
    (by rw [hm.r5]; try exact am.o56) (by rw [hm.r5]; exact am.sr) (by rw [hm.sp]; exact am.t1a)
    (by rw [hm.r5, hm.sp]; exact am.sep1) (by rw [hm.r5]; exact am.s1) (by rw [hm.r28, hm.r7]; exact am.lp)
  have qg' : Quiet g' := Quiet.of_sameCsr hl.csr q6
  have v9 : g'.get 9 = c.get 10 + c.get 12 := by rw [hl.frame 9 (by decide), hm.r9]
  have v18 : g'.get 18 = 0 - bH c := by rw [hl.frame 18 (by decide), hm.r18]
  have v28 : g'.get 28 = bA c - bW c + 4#32 := by rw [hl.t3, hm.r28]
  have v30 : g'.get 30 = c.get 12 - BitVec.ofNat 32 o + c.get 11 := by rw [hl.t5, hm.r12, hm.r11]
  -- loop
  obtain ⟨k4, c3, hr4, hpc3, hcs3, h30, h9, hpv, h11, hfr3⟩ := bmis_loop o am.ho j g' R' hl.pc qg' hl.t4 hl.a2
    (by rw [v9, v18, v28]; exact am.D) (by rw [v28]; exact am.dl) (by rw [v30, v18]; exact am.lo)
    (by rw [v30, v18]; exact am.L0a) (by rw [v28]; exact am.Ta) (by rw [v30, v18, v9]; exact am.dir)
    (fun k hk => by rw [v30, v18, am.L0, hl.prev k hk, hm.r5])
    (by rw [v30, v18]; exact am.hs) (by rw [v28]; exact am.hd)
  rw [v30, v18, v9] at hr4
  rw [h30, v30, v18, v9] at hpv
  let p0 := c.get 12 - BitVec.ofNat 32 o + c.get 11 + (0 - bH c) + 0xfffffffc#32 + BitVec.ofNat 32 o
  let R2 := wordsB R' p0 (c.get 10 + c.get 12 + (0 - bH c)) (j + 1)
  have q3 : Quiet c3 := Quiet.of_sameCsr hcs3 qg'
  have w18 : c3.get 18 = 0 - bH c := by rw [hfr3 18 (by decide) (by decide) (by decide) (by decide) (by decide), v18]
  have w2 : c3.get 2 = c.get 2 + 0xffffffd0#32 := by
    rw [hfr3 2 (by decide) (by decide) (by decide) (by decide) (by decide), hl.frame 2 (by decide), hm.sp]
  -- end block
  let Lq := c.get 12 - BitVec.ofNat 32 o + c.get 11 - BitVec.ofNat 32 (4 * (j + 1)) + (0 - bH c)
  obtain ⟨k5, c4, R3, hr5, ht⟩ := bend_any c3 R2 Lq o am.ho hpc3 q3
    (by rw [h30, v30, w18])
    (by rw [hfr3 6 (by decide) (by decide) (by decide) (by decide) (by decide), hl.frame 6 (by decide), hm.r6, am.o6])
    (by rw [hfr3 29 (by decide) (by decide) (by decide) (by decide) (by decide), hl.t4])
    (fun k hk => hpv k hk) am.La am.L4 am.src (by rw [w2]; exact am.t20) (by rw [w2]; exact am.t20a)
    (by rw [w2]; exact am.sep2)
    (by rw [h11, h9, v9, v18, am.e11]; exact am.AWa) (by rw [h11, h9, v9, v18, am.e11]; exact am.AWr)
  have q4 : Quiet c4 := Quiet.of_sameCsr ht.csr q3
  have u : ∀ r : Reg, r.val ∉ [6, 9, 12, 13, 14, 30, 11, 15, 8, 28, 29, 31] → c4.get r = g6.get r := by
    intro r hr
    rw [ht.frame r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)),
      hfr3 r (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
        (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide)),
      hl.frame r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))]
  -- tail bytes
  obtain ⟨k6, e, hr6, hpe, hcse, hfre⟩ := btail c4 R3 (bA c) (bW c) (c.get 11 + c.get 12 - bH c)
    (c.get 12 - bH c) ht.pc q4 (by rw [u 7 (by decide), hm.r7]) (by rw [u 16 (by decide), hm.r16])
    (by rw [u 5 (by decide), hm.r5]) (by rw [u 17 (by decide), hm.r17]) t1 t2 t3 t4
  -- RAM
  obtain ⟨Rt, hRt, hR3⟩ := ht.ram
  have hfin := bmis_ram (InTB (c.get 2)) R0 R1 R' R2 Rt R3 _
    (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) p0 (bA c) (bW c)
    (c.get 11 + c.get 12 - bH c - bW c + 0xffffffff#32) (bH c).toNat (j + 1) ((c.get 12 - bH c) &&& 3#32).toNat
    rfl (fun y hy => hl.ram y (fun h => hy (by rw [hm.sp] at h; exact inTB_of _ _ 0x1a (by decide) hst h)))
    (by show wordsB R' p0 (c.get 10 + c.get 12 + (0 - bH c)) (j + 1) = _; rw [am.q])
    (fun y hy => hRt y (fun h => hy (by rw [w2] at h; exact inTB_of _ _ 0x20 (by decide) hst h)))
    (by rw [hR3, h11, h9, v9, v18, am.e11, ← am.p0'])
    rfl hJ.symm am.p0 am.A' am.Sx am.AW am.c1 am.c2 am.c3 am.c4 am.c5 am.c6 am.zr am.zw am.zr' am.zt am.zt'
  refine ⟨k1 + 6 + k3 + k4 + k5 + k6, e, _, (((((hr1.trans hr2).trans hr3).trans hr4).trans hr5).trans hr6), hpe,
    ⟨hcse.trans (ht.csr.trans (hcs3.trans (hl.csr.trans hm.csr))), ?_, ?_⟩, ?_⟩
  · rw [hfre 2 (by decide) (by decide) (by decide) (by decide) (by decide), u 2 (by decide), hm.sp]
  · intro r hr
    have h9' : r ≠ 9 := fun e => hr (by subst e; decide)
    have h11' : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12' : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13' : r ≠ 13 := fun e => hr (by subst e; decide)
    have h16' : r ≠ 16 := fun e => hr (by subst e; decide)
    rw [hfre r h9' h11' h12' h13' h16', u r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))]
    exact hm.frame r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))
  · intro x hx
    rw [hfin x hx, ← am.nT]

/-! ## The contract: every size, direction and alignment -/

/-- What memmove needs: the PreF premises without any restriction on the case. -/
structure PreM (m : Machine) : Prop where
  pc : m.core.pc = 0x80020c1e
  quiet : Quiet m.core
  dst : B.inRam (m.core.get 10) (m.core.get 12).toNat = true
  src : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  spAl : (m.core.get 2).toNat % 4 = 0
  stack : 0x80029bc8 + 48 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  dstSep : (m.core.get 10).toNat + (m.core.get 12).toNat + 48 ≤ (m.core.get 2).toNat ∨
    (m.core.get 2).toNat ≤ (m.core.get 10).toNat
  srcSep : (m.core.get 11).toNat + (m.core.get 12).toNat + 48 ≤ (m.core.get 2).toNat ∨
    (m.core.get 2).toNat ≤ (m.core.get 11).toNat
  ra : (m.core.get 1).getLsbD 0 = false

/-- **memmove, every case.** From the trampoline 0x80020c1e with `a0 = dst`,
    `a1 = src`, `a2 = n` (both ranges in RAM and outside the callee's
    48-byte frame below sp), the emitted code returns to `ra` with the
    callee-saved registers and sp restored, and RAM outside that frame
    is exactly the memmove result (overlapping or not). -/
theorem contractAll (m₀ : Machine) (h : PreM m₀) : ∃ k m, QRun B img k m₀ m ∧ PostF m₀ m := by
  by_cases hG : (m₀.core.get 12).toNat < 16 ∨ (m₀.core.get 10 - m₀.core.get 11).ult (m₀.core.get 12) = false ∨
      (m₀.core.get 11).toNat % 4 = (m₀.core.get 10).toNat % 4
  · exact contractG m₀ ⟨h.pc, h.quiet, hG, h.dst, h.src, h.spAl, h.stack, h.dstSep, h.srcSep, h.ra⟩
  obtain ⟨c, ram⟩ := m₀
  obtain ⟨hpc, hq, hd, hs, hspal, hst, hdsep, hssep, hra⟩ := h
  simp only at hpc hq hd hs hspal hst hdsep hssep hra hG ⊢
  have hn : 16 ≤ (c.get 12).toNat := by omega
  have hdir : (c.get 10 - c.get 11).ult (c.get 12) = true := by
    cases h : (c.get 10 - c.get 11).ult (c.get 12)
    · exact absurd (Or.inr (Or.inl h)) hG
    · rfl
  have hnc : (c.get 11).toNat % 4 ≠ (c.get 10).toNat % 4 := fun h => hG (Or.inr (Or.inr h))
  have hsl : Slots (c.get 2) := ⟨hspal, by omega⟩
  have hpro := prologue c ram hpc hq hsl
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  obtain ⟨k, e, Rf, hr, he, hfr, hRf⟩ := bwd_mis c (saved c ram) hq hn hdir hd hs hnc hspal hst hdsep hssep
  obtain ⟨m, hm, hpost⟩ := finishZ InTB
    (fun sp x h1 h2 => by unfold InSlots at h1; unfold InTB at h2; omega)
    (fun sp x h1 h2 => h1 (by unfold InFrame; unfold InTB at h2; omega))
    c ram Rf e [5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 28, 29, 30, 31] hq hd hs hsl hst.1
    (by omega) (by omega) hra he hfr
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
    (fun x hx => by rw [hRf x hx]; exact bwd_moved _ _ _ _ hdir hdr hsr x)
  exact ⟨7 + k + 5, m, (hpro.trans hr).trans hm, hpost⟩

end E5R.Rmk.Memmove
