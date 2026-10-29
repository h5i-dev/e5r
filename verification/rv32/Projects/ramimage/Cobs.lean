/-
  The COBS decoder contract (Projects/rmk/Cobs/Decode.lean) stated on the image the job
  runner generates (`jobs/rmk/rmk-cobs-decode.json`). Original e5r code, Apache-2.0.

  The runner writes the pinned ELF as `E5R.Rmk.Image.elf` (Projects/rmk/Elf.lean) and binds
  `E5R.Rmk.Image.image := RamElf.imageOf 0x80000000 0x1000000 elf` with kernel-checked
  `image_accepted`, `image_agrees`, `image_rwBase` (Projects/rmk/ElfFidelity.lean). The
  proofs' `img` and `B` are that image and the QEMU virt board at its rwBase (checked
  equalities below); `decode` is the proofs' contract over them.

  Scope: `cobs::dec::decode_in_place_report` (0x8001e02e) for len ≤ 488 under `CobsEnv`.
  Not a property of RMK as a whole.
-/
import Projects.rmk.ElfFidelity
import Projects.rmk.Cobs.Decode

namespace E5R.RmkCobs
open E5R

theorem img_eq : E5R.Rmk.img = E5R.Rmk.Image.image.ro := rfl

theorem board_eq : E5R.Rmk.B = QemuVirtRv32.board E5R.Rmk.Image.image.rwBase := by
  rw [E5R.Rmk.Image.image_rwBase]

/-- The decoder on the runner's image and board. -/
theorem decode (m₀ : Machine) (h : E5R.Rmk.Cobs.CobsEnv m₀) :
    ∃ k m, E5R.Rmk.QRun (QemuVirtRv32.board E5R.Rmk.Image.image.rwBase) E5R.Rmk.Image.image.ro k m₀ m ∧
      E5R.Rmk.Cobs.Returns m₀ m ∧ E5R.Rmk.Cobs.Res m₀ m := by
  rw [← img_eq, ← board_eq]
  exact E5R.Rmk.Cobs.decode m₀ h

end E5R.RmkCobs
