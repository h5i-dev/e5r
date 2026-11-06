import Ptx.Semantics.Instruction
import TableSign

namespace FP4Sign
open Ptx Ptx.Fp

/-- Scope proposed for the first whole-kernel theorem: finite binary32 block
scales. This explicitly excludes NaN and infinity; the public decoder can also
be called with those patterns and the old GPU tests cover some of them. -/
def Finite32 (bits : Nat) : Prop :=
  Fmt.f32.isNaN bits = false ∧ Fmt.f32.isInf bits = false

instance (bits : Nat) : Decidable (Finite32 bits) := by
  unfold Finite32
  infer_instance

theorem flush_finite32 (a : Nat) (ha : Finite32 a) :
    Finite32 (Fmt.f32.flush true a) := by
  unfold Fmt.flush
  split
  · cases Fmt.f32.sgn a <;> decide
  · exact ha

/-- A finite multiply has a specified result in the existing PTX model,
including signed zeros, FTZ and possible rounded overflow to infinity. -/
theorem finite_mul_some (a b : Nat) (ha : Finite32 a) (hb : Finite32 b) :
    ∃ bits, fmul .f32 .rn true false a b = some bits := by
  obtain ⟨han, hai⟩ := flush_finite32 a ha
  obtain ⟨hbn, hbi⟩ := flush_finite32 b hb
  simp only [fmul, han, hbn, hai, hbi, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.not_false, ↓reduceIte, Fmt.sat]
  exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem inserted_finite : ∀ i : Fin 8, ∀ negative : Bool,
    Finite32 (inserted i negative) := by decide +kernel

theorem scale_some (i : Fin 8) (negative : Bool) (scale : Nat)
    (finite : Finite32 scale) :
    ∃ bits, fmul .f32 .rn true false scale (inserted i negative) = some bits :=
  finite_mul_some _ _ finite (inserted_finite i negative)

/-- A specified result does not query the launch's state/PC-indexed NaN
oracle. The two states and contexts need not have the same PCs or registers. -/
theorem specified_oracle_independent (bits : Nat) (c₀ c₁ : Ctx) (s₀ s₁ : TState) :
    fres c₀ s₀ .f32 (some bits) = fres c₁ s₁ .f32 (some bits) := rfl

/-- At every reachable scale multiply whose inputs satisfy the table and
finite-scale invariants, changed instruction positions require no NaN oracle
coupling assumption. Reachability of those invariants is still a whole-kernel
obligation, not a premise that the checker may silently assume. -/
theorem scale_oracle_independent (i : Fin 8) (negative : Bool) (scale : Nat)
    (finite : Finite32 scale) (c₀ c₁ : Ctx) (s₀ s₁ : TState) :
    fres c₀ s₀ .f32 (fmul .f32 .rn true false scale (inserted i negative)) =
    fres c₁ s₁ .f32 (fmul .f32 .rn true false scale (inserted i negative)) := by
  obtain ⟨bits, h⟩ := scale_some i negative scale finite
  rw [h]
  rfl

#print axioms finite_mul_some
#print axioms scale_oracle_independent
end FP4Sign
