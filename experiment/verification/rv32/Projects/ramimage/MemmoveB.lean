/-
  The RMK memmove `contractB` (Projects/rmk/MemmoveContract.lean, peer) stated on
  the image the job runner generates (`jobs/rmk/rmk-memmove-contractB.json`).

  Original e5r code, Apache-2.0.

  BOUNDED, not full memmove: `PreB` admits n < 16 in either direction, or
  n ≥ 16 copied forward ((dst - src) ≥ n unsigned) with src ≡ dst (mod 4).
  The n ≥ 16 backward path and the misaligned forward path are not covered.
  Every other `PreB` condition is kept as the peer states it (pc at the
  trampoline 0x80020c1e, quiet core, dst and src in model RAM, aligned save
  slots in RAM, stack separated from dst and src, even return address);
  `PostB` is the ABI frame (all but t0-t6, a1-a7 preserved), CSRs unchanged,
  and RAM outside the three save slots equal to the memmove of the entry RAM.

  The image and board are the runner's, through the equalities `img_eq` and
  `board_eq` of Projects/ramimage/Memmove.lean (checked, not assumed).
-/
import Projects.ramimage.Memmove
import Projects.rmk.MemmoveContract

namespace E5R.RmkMemmoveB
open E5R

/-- memmove under `PreB` on the runner's image and board. -/
theorem contractB (m₀ : Machine) (h : E5R.Rmk.Memmove.PreB m₀) :
    ∃ k m, E5R.Rmk.QRun (QemuVirtRv32.board E5R.Rmk.Image.image.rwBase) E5R.Rmk.Image.image.ro k m₀ m ∧
      E5R.Rmk.Memmove.PostB m₀ m := by
  rw [← E5R.RmkMemmove.img_eq, ← E5R.RmkMemmove.board_eq]
  exact E5R.Rmk.Memmove.contractB m₀ h

end E5R.RmkMemmoveB
