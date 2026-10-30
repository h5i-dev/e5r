/-
  The UART send loop (Uart/SendRound.lean) continued through the unpark site to the session loop head,
  with main's `unpark_round` and `extras_keep` (Deframer/SessionInv.lean, support-lean4 bf1723f), on the
  pinned RMK image. No callee contract is assumed (memmove and COBS inside unpark are discharged by
  main's `copy_contract`/`cobs_report`); the yield poll stays an explicit boundary.

  Original e5r code, Apache-2.0.

  PROVED here: `send_to_loop`: from `SendAt` with the session's `Extras` and the deframer facts the
  unpark step needs (parked ≤ 488, discarding ≤ 1), every behaviour reaches the loop head 0x80003e1a
  with `SessInv`, or the yield poll's entry 0x8001e14a (executor boundary). `w_sendLoop`: the four
  hypotheses hold together on a concrete machine, so the theorem is not vacuous.

  NOT proved: that the Some path establishes `SendAt` at 0x8000429e (main's; see
  rmk-audit/SEND-INTERFACE.md), the yield poll and the executor, interrupt preservation, `SessionSafe`.
-/
import Projects.rmk.Uart.SendRound
import Projects.rmk.Deframer.SessionInv

namespace E5R.Rmk.Uart
open E5R E5R.Rmk E5R.Rmk.Deframer E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI

theorem sendW_SW {sp y : Word} (h : SendW sp y) : SW sp y := by
  unfold SendW InSlots at h; unfold SW; omega

/-- Where the send path, continued through the unpark site, stops. -/
def SendLoopQ (m₀ m : Machine) : Prop :=
  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨
  (Kept m₀ m ∧ m.core.pc = 0x8001e14a ∧ m.core.get 1 = 0x80004324 ∧ m.core.get 10 = 0x8002a7ec ∧
    m.ram 0x8002a7ec = 0 ∧ m.core.get 11 = m₀.core.get 2 + 0x00000030#32)

theorem send_to_loop (m₀ : Machine) (h : SendAt m₀) (E : Extras m₀)
    (hpk : (ramRead m₀.ram 0x8002a798 .w).toNat ≤ bufLen) (hdc : discarding m₀.ram dfr ≤ 1) :
    Lands B img (SendLoopQ m₀) m₀ := by
  have hsp := h.sp
  refine lands_seq (fun m hq => ?_) (send_round m₀ h)
  obtain ⟨K, hd | hy⟩ := hq
  · have sp := K.sp
    have nW : ∀ x : Word, x.toNat < 0x8002a7c4 → ¬ SendW (m₀.core.get 2) x := fun x hx hw => by
      unfold SendW InSlots at hw; omega
    have U : UnparkAt m := ⟨hd.1, K.quiet, (K.regs 22 (by decide)).trans h.s6, (K.regs 23 (by decide)).trans h.s7,
      by rw [sp]; exact h.spAl, by rw [sp]; omega, ?_, ?_⟩
    · have Ex : Extras m := extras_keep m₀ m E (by omega) sp (K.regs 26 (by decide))
        fun y hy _ => K.ram y fun hw => hy (sendW_SW hw)
      obtain ⟨k, m', r, hpc, hs⟩ := unpark_round m U Ex
      exact lands_of_qrun r (.inl ⟨hpc, hs⟩)
    · rw [ramRead_w_congr (ram := m₀.ram) _ fun k hk => K.ram _ (nW _ (by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega))]
      exact hpk
    · show (m.ram (dfr + 8)).toNat ≤ 1
      rw [K.ram _ (nW _ (by decide))]; exact hdc
  · exact .done (.inr ⟨K, hy⟩)

/-- The send entry, the session extras and the unpark facts hold together (`wCore`/`wRam`). -/
theorem w_sendLoop : SendAt ⟨wCore, wRam⟩ ∧ Extras ⟨wCore, wRam⟩ ∧
    (ramRead wRam 0x8002a798 .w).toNat ≤ bufLen ∧ discarding wRam dfr ≤ 1 :=
  ⟨w_sendAt, ⟨by decide, by decide, ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩, by decide, by decide⟩

end E5R.Rmk.Uart
