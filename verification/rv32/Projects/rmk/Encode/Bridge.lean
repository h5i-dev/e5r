/-
  encode_frame's write-set contract (`EncPost`) in the form main's Some round consumes
  (`SomeP.CallPost` and `SomeP.EncRes`, Deframer/SomeRound.lean). The caller only has to show
  that the cells it keeps (`Kept`) are outside encode_frame's write set (`EncW`).

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.Encode.Spec
import Projects.rmk.Deframer.SomeRound

namespace E5R.Rmk.Encode
open E5R E5R.Rmk

/-- Every register main's ABI frame treats as preserved is zero, ra, or callee-saved here. -/
theorem preserved_regs : ∀ r : Reg, r.val ∉ Deframer.callerSaved →
    r.val = 0 ∨ r.val = 1 ∨ r.val ∈ calleeSaved := by decide

theorem callPost_of_encPost (m₀ m : Machine) (hpre : EncPre m₀) (h : EncPost m₀ m)
    (hK : ∀ x, Deframer.SomeP.Kept m₀ x → ¬ EncW (m₀.core.get 2) x) :
    Deframer.SomeP.CallPost 0x80003f1e m₀ m ∧ Deframer.SomeP.EncRes m₀ m := by
  refine ⟨⟨h.pc, h.quiet, h.saved 2 (by decide), fun r hr => ?_, fun x hx => h.frame x (hK x hx)⟩, h.res⟩
  rcases preserved_regs r hr with h0 | h1 | hc
  · have : r = 0 := Fin.ext h0
    subst this; simp
  · have : r = 1 := Fin.ext h1
    subst this; rw [h.ra, hpre.ra]
  · exact h.saved r hc

/-- **encode_frame, as main's caller needs it**: from the call set-up, every behaviour returns
    with `CallPost` and `EncRes`, provided `Kept` is outside the write set. -/
theorem encode_callPost (m₀ : Machine) (hpre : EncPre m₀)
    (hK : ∀ x, Deframer.SomeP.Kept m₀ x → ¬ EncW (m₀.core.get 2) x) :
    Lands B img (fun m => Deframer.SomeP.CallPost 0x80003f1e m₀ m ∧ Deframer.SomeP.EncRes m₀ m) m₀ :=
  lands_seq (fun m hm => .done (callPost_of_encPost m₀ m hpre hm hK)) (encode_spec m₀ hpre)

end E5R.Rmk.Encode
