/-
  RMK session steps (main's Projects/rmk/Deframer/{Session,SessionLoop}.lean), CONDITIONAL, on
  the image the job runner generates (`jobs/rmk/rmk-session-conditional.json`).
  Original e5r code, Apache-2.0.

  NOT a safety claim and NOT `SessionSafe`. Every statement takes memmove's `CopyContract` as an
  explicit hypothesis (discharged separately by `CopyDischarge.copy_contract`). The COBS
  dependency is discharged (main's `cobs_report`; also `E5R.Rmk.Cobs.cobs_report_contract`).
  Not covered at all: the path 0x80003e70 -> 0x80003fd8 (dispatch, encode, UART send, yields),
  the path 0x80003f7c -> loop head (UART read future, executor), interrupts (`Quiet` is assumed
  at every point). See verification/rv32/rmk-audit/SESSION-BOUNDARY.md.

  Image and board: the runner's (`E5R.RmkDeframer.img_eq`, `board_eq`).
-/
import Projects.ramimage.Deframer
import Projects.rmk.Deframer.SessionLoop
import Projects.rmk.Cobs.Bridge

namespace E5R.RmkSession
open E5R E5R.Rmk.Deframer E5R.Rmk.Deframer.Session
open E5R.Rmk (QRun QRun.trans)

/-- **CONDITIONAL on `CopyContract`**: the receive step from the loop head. -/
theorem recv_conditional :
    CopyContract → ∀ m₀, SessPre m₀ → ∃ k m, QRun B img k m₀ m ∧ RecvOut m₀ m :=
  recv_step

/-- **CONDITIONAL on `CopyContract`**: the unpark call site back to the loop head. -/
theorem unpark_conditional :
    CopyContract → ∀ m₀, UnparkAt m₀ → ∃ k m, QRun B img k m₀ m ∧ SessPre m ∧
      m.core.get 2 = m₀.core.get 2 ∧ filled m.ram dfr = (ramRead m₀.ram 0x8002a798 .w).toNat :=
  fun hC m₀ h => by
    obtain ⟨k, m, hr, hs, hsp, -, hf, -⟩ := unpark_step hC m₀ h
    exact ⟨k, m, hr, hs, hsp, hf⟩

/-- **CONDITIONAL on `CopyContract`**: the two proved steps compose. From the unpark call site,
    one quiet run goes through `unpark_pending`, the loop head and the receive step, ending at
    0x80003e70 (a message) or 0x80003f7c (no frame yet), at the same sp. The gaps in between
    (0x80003e70 -> 0x80003fd8, 0x80003f7c -> 0x80003e1a) are NOT closed, so this is not a loop
    invariant. -/
theorem unpark_then_recv (hC : CopyContract) (m₀ : Machine) (h : UnparkAt m₀) :
    ∃ k m₁ m, QRun B img k m₀ m ∧ SessPre m₁ ∧ RecvOut m₁ m ∧ m.core.get 2 = m₀.core.get 2 := by
  obtain ⟨k₁, m₁, h₁, hs, hsp, -, -, -⟩ := unpark_step hC m₀ h
  obtain ⟨k₂, m, h₂, ho⟩ := recv_step hC m₁ hs
  exact ⟨k₁ + k₂, m₁, m, QRun.trans h₁ h₂, hs, ho, ho.sp.trans hsp⟩

/-- Main's COBS discharge and the independent one state the same interface. -/
theorem cobs_both : CobsReportContract ∧ CobsReportContract :=
  ⟨cobs_report, E5R.Rmk.Cobs.cobs_report_contract⟩

end E5R.RmkSession
