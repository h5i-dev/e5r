import Crosscheck
import Fp.Theorems.Addition
import Fp.Theorems.Subtraction
import Fp.Theorems.Multiplication
import Fp.Theorems.Division
import Fp.Theorems.FMA
import Fp.Theorems.Sqrt

namespace Crosscheck
open Ptx.Fp

/-- Upstream's rational SMT-LIB reference, distinct from E5R's Rat model.
    sqrtSpec uses a noncomputable bracket specification. This is a proof target,
    never imported by the executable comparison runner. -/
noncomputable def rationalReference (F : Fmt) (m : RMode) (op : Op)
    (a b c : Nat) : Option Nat :=
  let x := unpack F a
  let y := unpack F b
  let z := unpack F c
  let round := Fp.SmtLibSemanticsQ.smtLibRoundMethodQ F.eb F.fb
  observe <| match op with
  | .add => Fp.SmtLibSemantics.SmtLibFunctions.add round (mode m) x y
  | .sub => Fp.SmtLibSemantics.SmtLibFunctions.sub round (mode m) x y
  | .mul => Fp.SmtLibSemantics.SmtLibFunctions.mul round (mode m) x y
  | .div => Fp.SmtLibSemantics.SmtLibFunctions.div round (mode m) x y
  | .fma => Fp.SmtLibSemantics.SmtLibFunctions.fma round (mode m) x y z
  | .sqrt => Fp.sqrtSpec (mode m) x

/-- The upstream packed circuit agrees with its rational reference under exactly
    the observation used by our tests. This does not assert agreement with PTX. -/
theorem reference_eq_upstream (F : Fmt) (he : 1 < F.eb) (hs : 0 < F.fb)
    (m : RMode) (op : Op) (a b c : Nat) :
    rationalReference F m op a b c = upstream F m op a b c := by
  cases op with
  | add => exact observe_equiv (Fp.add_eq_add hs he _ _ _)
  | sub => exact observe_equiv (Fp.sub_eq_sub hs he _ _ _)
  | mul => exact observe_equiv (Fp.mul_eq_mul hs he _ _ _)
  | div => exact observe_equiv (Fp.div_eq_div hs he _ _ _)
  | fma => exact observe_equiv (Fp.fma_eq_fma hs he _ _ _ _)
  | sqrt => exact observe_equiv (Fp.sqrt_eq_sqrt hs he _ _)

theorem f32_reference (m : RMode) (op : Op) (a b c : Nat) :
    rationalReference Fmt.f32 m op a b c = upstream Fmt.f32 m op a b c :=
  reference_eq_upstream _ (by decide) (by decide) m op a b c

theorem f64_reference (m : RMode) (op : Op) (a b c : Nat) :
    rationalReference Fmt.f64 m op a b c = upstream Fmt.f64 m op a b c :=
  reference_eq_upstream _ (by decide) (by decide) m op a b c
/-- Reduce the remaining production equivalence obligation to the rational
    reference, removing packed-circuit correctness from the remaining work. -/
theorem agrees_iff_reference (F : Fmt) (he : 1 < F.eb) (hs : 0 < F.fb)
    (m : RMode) (op : Op) :
    Agrees F m op ↔ ∀ a b c, a < 2^(1+F.eb+F.fb) → b < 2^(1+F.eb+F.fb) →
      c < 2^(1+F.eb+F.fb) → rationalReference F m op a b c = production F m op a b c := by
  simp only [Agrees, reference_eq_upstream F he hs]
end Crosscheck
