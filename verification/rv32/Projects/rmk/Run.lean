/-
  Quiet deterministic runs, for machine-code contracts on the RMK firmware.

  Original e5r code, Apache-2.0.

  On QEMU virt the RMK firmware may run with `mstatus.MIE` set while the
  `mie` CSR is zero, so "masked" (`mie_ = false`, Theories/Hybrid/Basic) is
  the wrong premise there. A quiet machine is one at which no interrupt is
  enabled (`irqEnabled` is false for every code), which is all the model's
  `Step.irq` looks at; it is preserved by every step that leaves the CSRs
  alone (`sameCsr`). A `QRun` is a sequence of deterministic steps (every
  oracle gives the same successor, no event, no fault) each from a quiet
  machine, so it is the only behaviour of `Step` from its first machine.
-/
import Theories.Logic

namespace E5R.Rmk
open E5R

def Quiet (c : Core) : Prop := ∀ code, irqEnabled c code = false

theorem Quiet.of_sameCsr {c d : Core} (h : c.sameCsr d) (hq : Quiet d) : Quiet c := by
  intro code
  have := congrArg (fun t => (t.1, t.2.2.2.1)) h
  simp only [Core.ctl, Prod.mk.injEq] at this
  have e := hq code
  unfold irqEnabled at *
  rw [this.1, this.2]; exact e

inductive QRun (B : Board) (img : List Segment) : Nat → Machine → Machine → Prop
  | refl (m) : QRun B img 0 m m
  | step {n m m₁ m₂} : Quiet m.core → DetStep B img m m₁ → QRun B img n m₁ m₂ → QRun B img (n+1) m m₂

theorem QRun.trans {B img a b m₁ m₂ m₃} (h₁ : QRun B img a m₁ m₂) (h₂ : QRun B img b m₂ m₃) :
    QRun B img (a + b) m₁ m₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | step hq hs _ ih => rw [Nat.add_right_comm]; exact .step hq hs (ih h₂)

theorem QRun.single {B img m m'} (hq : Quiet m.core) (h : DetStep B img m m') : QRun B img 1 m m' :=
  .step hq h (.refl _)

/-- A quiet run is a run of deterministic steps. -/
theorem QRun.toDetSteps {B img n m m'} (h : QRun B img n m m') : DetSteps B img n m m' := by
  induction h with
  | refl m => exact .refl m
  | step _ hs _ ih => exact .step hs ih

end E5R.Rmk
