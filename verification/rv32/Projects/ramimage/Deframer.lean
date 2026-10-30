/-
  RMK Deframer methods (main's Projects/rmk/Deframer/*), CONDITIONAL, on the image the job runner
  generates (`jobs/rmk/rmk-deframer-conditional.json`). Original e5r code, Apache-2.0.

  NOT a safety claim. `conditional` is an implication: IF memmove meets `CopyContract` (open: the
  backward and misaligned memmove paths are not proved) and IF `decode_in_place_report` meets
  `CobsReportContract` (main's interface; the COBS contract proved in Projects/rmk/Cobs still has
  to be shown to imply it), THEN `tail`, `park_pending`, `unpark_pending` and `next` meet their
  contracts. Nothing here proves either hypothesis.

  The image and board in every contract are the runner's: `img_eq` and `board_eq` are checked
  equalities with `RamElf.imageOf` of the generated packed file and the QEMU virt board at its
  rwBase (Projects/rmk/ElfFidelity.lean).
-/
import Projects.rmk.ElfFidelity
import Projects.rmk.Deframer.Next
import Projects.rmk.Deframer.Unpark

namespace E5R.RmkDeframer
open E5R E5R.Rmk.Deframer

theorem img_eq : E5R.Rmk.Deframer.img = E5R.Rmk.Image.image.ro := rfl

theorem board_eq : E5R.Rmk.Deframer.B = QemuVirtRv32.board E5R.Rmk.Image.image.rwBase := by
  rw [E5R.Rmk.Image.image_rwBase]

/-- **CONDITIONAL** on the open memmove and COBS-interface contracts. -/
theorem conditional :
    (CopyContract → TailContract tailStack ∧ ParkContract ∧ UnparkContract) ∧
    (CopyContract → CobsReportContract → NextContract) :=
  ⟨fun hC => ⟨Tail.tail_from_copy hC, Park.park_from_copy hC, Unpark.unpark_from_copy hC⟩, Next.next_from_deps⟩

end E5R.RmkDeframer
