/-
  The session's Some path from 0x80003e70, on the pinned RMK image: the first branch, proved.

  Original e5r code, Apache-2.0.

  At 0x80003e70 the code loads the message's header halfword (0x8002a588 = s6+0xcb, written by
  `RynkMessage::from_decoded`), stores it at s6+0x2eb and, if it is negative as an i16, jumps
  straight to the unpark call site 0x80003fd8, with no dispatch and no response.

  PROVED here: `some_neg`: from `SomeAt` with the header's high byte ≥ 0x80, a quiet run back to the
  loop head with `SessInv`.

  NOT PROVED: the other header values, which run `RynkService::dispatch` (0x800001f2, a 12.6 KB
  async state machine, polled at 0x80003e9a), `encode_frame` (0x80008d5c), the response send and
  the yields to the executor.
-/
import Projects.rmk.Deframer.SessionInv
import Projects.rmk.Deframer.SomeSegs

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.SomeP
open E5R E5R.Rmk E5R.Rmk.Deframer.Tail E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI

/-- A halfword whose high byte is ≥ 0x80 is negative as an i16. -/
theorem neg_h (x y : BitVec 8) (h : 0x80 ≤ y.toNat) :
    taken .lt (extend .h true (BitVec.ofNat 32 (x.toNat + 256 * y.toNat))) 0 = true := by
  have hx := x.isLt
  have hy := y.isLt
  have hm : ((BitVec.ofNat 32 (x.toNat + 256 * y.toNat)).setWidth 16).msb = true := by
    rw [BitVec.msb_eq_true_iff_two_mul_ge]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  simp only [taken, extend]
  generalize (BitVec.ofNat 32 (x.toNat + 256 * y.toNat)).setWidth 16 = z at hm
  rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_signExtend_of_le (by decide)]
  rw [BitVec.toInt_eq_msb_cond, hm]
  simp
  omega

theorem wr_h_other (M : Word → BitVec 8) (a v x : Word) (h1 : x ≠ a) (h2 : x ≠ a + 1) :
    ramWrite M a v .h x = M x := by
  simp [ramWrite, ramPut, h1]
  intro e; exact absurd e h2

/-- **The negative-header branch of the Some path.** -/
theorem some_neg (m : Machine) (h : SomeAt m) (hneg : 0x80 ≤ (m.ram 0x8002a589).toNat) :
    ∃ k m', QRun B img k m m' ∧ m'.core.pc = 0x80003e1a ∧ SessInv m' := by
  obtain ⟨c, M⟩ := m
  have h22 : c.get 22 = s6v := h.s6
  have r1 := sNeg c M h.pc h.quiet (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [h22]; decide)
    (by rw [h22]
        show taken .lt (extend .h true (BitVec.ofNat 32 ((M 0x8002a588).toNat + 256 * (M 0x8002a589).toNat))) 0 = true
        exact neg_h _ _ hneg)
  let K := sNegCore c M
  let R := sNegRam c M
  have csK : K.sameCsr c := by unfold K sNegCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
  have gK : ∀ r : Reg, r ≠ 10 → K.get r = c.get r := fun r a => by simp [K, sNegCore, Core.wr_get_ne, a]
  have hR : R = ramWrite M 0x8002a7a8 (extend .h true (ramRead M (c.get 22 + 0x000000cb#32) .h)) .h := by
    simp only [R, sNegRam, h22]; rfl
  have hsp : K.get 2 = c.get 2 := gK 2 (by decide)
  have h1 : 0x8002a798 + 0x70 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := h.sp
  have keep : ∀ y, ¬ SW (c.get 2) y → R y = M y := by
    intro y hy
    rw [hR]
    apply wr_h_other
    · intro e; apply hy; subst e; unfold SW; right; right; right; left; decide
    · intro e; apply hy; subst e; unfold SW; right; right; right; left; decide
  have UA : UnparkAt ⟨K, R⟩ := by
    refine ⟨rfl, Quiet.of_sameCsr csK h.quiet, (gK 22 (by decide)).trans h22,
      (gK 23 (by decide)).trans h.s7, by show (K.get 2).toNat % 4 = 0; rw [hsp]; exact h.spAl,
      by show _ ∧ _; rw [hsp]; exact h.sp, ?_, ?_⟩
    · show (ramRead R 0x8002a798 .w).toNat ≤ bufLen
      rw [hR, rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide)]
      have hp : (ramRead M 0x8002a798 .w).toNat + 4 ≤ bufLen := h.parked
      omega
    · show (R (dfr + 8)).toNat ≤ 1
      rw [hR, wr_h_other _ _ _ _ (by decide) (by decide)]
      exact h.disc
  have E : Extras ⟨K, R⟩ := extras_keep ⟨c, M⟩ ⟨K, R⟩ h.ext h.sp hsp (gK 26 (by decide)) fun y hy _ => keep y hy
  obtain ⟨k, m', r2, hpc, hI⟩ := unpark_round ⟨K, R⟩ UA E
  exact ⟨_, m', r1.trans r2, hpc, hI⟩

end E5R.Rmk.Deframer.SomeP
