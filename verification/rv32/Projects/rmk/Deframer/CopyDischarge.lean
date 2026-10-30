/-
  The memmove dependency of the deframer, discharged: `CopyContract` (Deframer/Spec.lean) from the
  peer's proved contract of the emitted memmove for every size, direction and alignment
  (`E5R.Rmk.Memmove.contractAll`, Projects/rmk/MemmoveBwdAll.lean), and with it every deframer
  method and session step UNCONDITIONALLY.

  Original e5r code, Apache-2.0.

  The bridge is exact, with no weakening:
  * `CopyEnv` gives `PreM` field by field. The callee frame `B.inRam (sp - 48) 48` gives
    `PreM.stack`; dst/src + n ≤ sp - 48 gives `dstSep`/`srcSep`. `PreM` needs no size bound.
  * `PostF` is `CopyPost`: the same pc, the same register frame (t0-t6, a1-a7 may change), the same
    CSRs, and RAM outside the 48-byte frame equal to `Memmove.moved` of the entry RAM.

  PROVED here: `copy_contract : CopyContract`, and from it `tail_contract`, `park_contract`,
  `unpark_contract`, `next_contract`, `recv_step'` and `unpark_step'`.
-/
import Projects.rmk.Deframer.SessionLoop
import Projects.rmk.MemmoveBwdAll

namespace E5R.Rmk.Deframer
open E5R E5R.Rmk

theorem copy_contract : CopyContract := by
  intro m₀ E
  have hst := Tail.stack_nat (m₀.core.get 2) memmoveFrame E.frame
  have hds : (m₀.core.get 10).toNat + (m₀.core.get 12).toNat ≤ (m₀.core.get 2).toNat - memmoveFrame := E.dstSep
  have hss : (m₀.core.get 11).toNat + (m₀.core.get 12).toNat ≤ (m₀.core.get 2).toNat - memmoveFrame := E.srcSep
  rw [show memmoveFrame = 48 from rfl] at hst hds hss
  obtain ⟨k, m, r, P⟩ := Memmove.contractAll m₀
    ⟨E.pc, E.quiet, E.dst, E.src, E.spAl, ⟨by omega, by omega⟩, .inl (by omega), .inl (by omega), E.ra⟩
  exact ⟨k, m, r, P.pc, P.regs, P.csr, P.ram⟩

/-- `tail`'s contract, with the 80-byte frame. -/
theorem tail_contract : TailContract tailStack := Tail.tail_from_copy copy_contract
theorem park_contract : ParkContract := Park.park_from_copy copy_contract
theorem unpark_contract : UnparkContract := Unpark.unpark_from_copy copy_contract
theorem next_contract : NextContract := next_from_copy copy_contract

/-- The session receive step (Deframer/Session.lean), without hypotheses. -/
theorem recv_step' (m₀ : Machine) (h : Session.SessPre m₀) : ∃ k m, QRun B img k m₀ m ∧ Session.RecvOut m₀ m :=
  Session.recv_step copy_contract m₀ h

/-- The session's unpark step (Deframer/SessionLoop.lean), without hypotheses. -/
theorem unpark_step' (m₀ : Machine) (h : Session.UnparkAt m₀) :
    ∃ k m, QRun B img k m₀ m ∧ Session.SessPre m ∧ m.core.get 2 = m₀.core.get 2 ∧
      filled m.ram Session.dfr = (ramRead m₀.ram 0x8002a798 .w).toNat ∧
      ∀ x, ¬ ((Session.dfr.toNat ≤ x.toNat ∧ x.toNat < Session.dfr.toNat + 12) ∨
              (Session.bufA.toNat ≤ x.toNat ∧ x.toNat < Session.bufA.toNat + bufLen) ∨
              ((m₀.core.get 2).toNat - 0x40 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat)) →
        m.ram x = m₀.ram x :=
  Session.unpark_step copy_contract m₀ h

end E5R.Rmk.Deframer
