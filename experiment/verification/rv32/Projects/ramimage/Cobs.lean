/-
  The COBS decoder contract (Projects/rmk/Cobs/Decode.lean) stated on the image the job
  runner generates (`jobs/rmk/rmk-cobs-decode.json`). Original nocompiler code, Apache-2.0.

  The runner writes the pinned ELF as `NoCompiler.Rmk.Image.elf` (Projects/rmk/Elf.lean) and binds
  `NoCompiler.Rmk.Image.image := RamElf.imageOf 0x80000000 0x1000000 elf` with kernel-checked
  `image_accepted`, `image_agrees`, `image_rwBase` (Projects/rmk/ElfFidelity.lean). The
  proofs' `img` and `B` are that image and the QEMU virt board at its rwBase (checked
  equalities below); `decode` is the proofs' contract over them.

  Scope: `cobs::dec::decode_in_place_report` (0x8001e02e) for len ≤ 488 under `CobsEnv`, and
  its caller `cobs::dec::decode_in_place` (0x8001e006, what `next` calls) under `WEnv`.
  Not a property of RMK as a whole.
-/
import Projects.rmk.ElfFidelity
import Projects.rmk.Cobs.Wrapper

namespace NoCompiler.RmkCobs
open NoCompiler

theorem img_eq : NoCompiler.Rmk.img = NoCompiler.Rmk.Image.image.ro := rfl

theorem board_eq : NoCompiler.Rmk.B = QemuVirtRv32.board NoCompiler.Rmk.Image.image.rwBase := by
  rw [NoCompiler.Rmk.Image.image_rwBase]

/-- The decoder on the runner's image and board. -/
theorem decode (m₀ : Machine) (h : NoCompiler.Rmk.Cobs.CobsEnv m₀) :
    ∃ k m, NoCompiler.Rmk.QRun (QemuVirtRv32.board NoCompiler.Rmk.Image.image.rwBase) NoCompiler.Rmk.Image.image.ro k m₀ m ∧
      NoCompiler.Rmk.Cobs.Returns m₀ m ∧ NoCompiler.Rmk.Cobs.Res m₀ m := by
  rw [← img_eq, ← board_eq]
  exact NoCompiler.Rmk.Cobs.decode m₀ h

/-- `decode_in_place` (the function `next` calls) on the runner's image and board. -/
theorem decode_in_place (m₀ : Machine) (h : NoCompiler.Rmk.Cobs.WEnv m₀) :
    ∃ k m, NoCompiler.Rmk.QRun (QemuVirtRv32.board NoCompiler.Rmk.Image.image.rwBase) NoCompiler.Rmk.Image.image.ro k m₀ m ∧
      NoCompiler.Rmk.Cobs.WReturns m₀ m ∧ NoCompiler.Rmk.Cobs.WRes m₀ m := by
  rw [← img_eq, ← board_eq]
  exact NoCompiler.Rmk.Cobs.decode_in_place m₀ h

end NoCompiler.RmkCobs
