/-
  The RMK memmove contract (Projects/rmk/MemmoveSmall.lean, n < 16) stated on
  the image the job runner generates (`jobs/rmk/rmk-memmove-small.json`).

  Original e5r code, Apache-2.0.

  The runner writes the pinned ELF as `E5R.Rmk.Image.elf` (Projects/rmk/Elf.lean,
  the module the proofs import, so there is one image input) and binds
  `E5R.Rmk.Image.image := RamElf.imageOf 0x80000000 0x1000000 elf` with
  kernel-checked `image_accepted`, `image_agrees` and `image_rwBase`
  (Projects/rmk/ElfFidelity.lean). The two equalities below connect the
  proofs' `img` and `B` to that image and to the QEMU virt board at its
  rwBase; `contract` is then the proofs' contract over them.

  Scope: the emitted memmove for copies of fewer than 16 bytes, from the
  trampoline at 0x80020c1e, under `Memmove.Pre` (quiet core, n < 16, dst and
  src in model RAM, aligned save slots in RAM separated from dst/src, even
  return address). It is not a property of RMK as a whole.
-/
import Projects.rmk.ElfFidelity
import Projects.rmk.MemmoveSmall

namespace E5R.RmkMemmove
open E5R

/-- The proofs fetch from exactly the runner's image. -/
theorem img_eq : E5R.Rmk.img = E5R.Rmk.Image.image.ro := rfl

/-- The proofs' board is QEMU virt with model RAM from the runner's image's rwBase. -/
theorem board_eq : E5R.Rmk.B = QemuVirtRv32.board E5R.Rmk.Image.image.rwBase := by
  rw [E5R.Rmk.Image.image_rwBase]

/-- memmove of n < 16 bytes on the runner's image and board: from every machine meeting
    `Pre`, a quiet deterministic run reaches a machine meeting `Post`. -/
theorem contract (m₀ : Machine) (h : E5R.Rmk.Memmove.Pre m₀) :
    ∃ k m, E5R.Rmk.QRun (QemuVirtRv32.board E5R.Rmk.Image.image.rwBase) E5R.Rmk.Image.image.ro k m₀ m ∧
      E5R.Rmk.Memmove.Post m₀ m := by
  rw [← img_eq, ← board_eq]
  exact E5R.Rmk.Memmove.contract m₀ h

end E5R.RmkMemmove
