/-
  RMK Deframer methods with the COBS dependency DISCHARGED: `next` conditional only on memmove's
  `CopyContract` (`jobs/rmk/rmk-deframer-cobs-discharged.json`). Original e5r code, Apache-2.0.

  `CobsReportContract` (main's interface) is a theorem here: `E5R.Rmk.Cobs.cobs_report_contract`,
  proved from the machine-code contract of `decode_in_place_report` (Projects/rmk/Cobs). STILL NOT
  a safety claim: every method is conditional on `CopyContract` (memmove's backward and misaligned
  paths are open). Image and board: the runner's (`E5R.RmkDeframer.img_eq`, `board_eq`).
-/
import Projects.ramimage.Deframer
import Projects.rmk.Cobs.Bridge

namespace E5R.RmkDeframerCobs
open E5R E5R.Rmk.Deframer

/-- **CONDITIONAL on `CopyContract` only.** -/
theorem conditional_copy :
    CopyContract → TailContract tailStack ∧ ParkContract ∧ UnparkContract ∧ NextContract :=
  fun hC => ⟨Tail.tail_from_copy hC, Park.park_from_copy hC, Unpark.unpark_from_copy hC,
    Next.next_from_deps hC E5R.Rmk.Cobs.cobs_report_contract⟩

end E5R.RmkDeframerCobs
