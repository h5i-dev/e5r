/-
Float element functions for the map class (docs/verification-ptx.md,
"Floating point: specs").

A float map spec states each output element of `.f32` as an expression of
the model's own operations on the input elements and scalars (`F32.fma .rn
…`), so the claim is bit-exact: the kernel's output has exactly the bits
the expression has, except that where the expression is a NaN the output is
some NaN (`feq32`). That exception is forced by PTX, which leaves the bits
of a NaN result unspecified (`Ptx/Semantics/Float.lean`); the model takes
them from the launch's NaN oracle and `MapSpec.Correct` quantifies over it.

`within32 k` is the error-bound form: both NaN, or both the same infinity,
or both finite at most `k` representable numbers apart (`ulps32`).

`ptx_fvalue` closes the value goal of a float map obligation. After the
symbolic run, the kernel's element is `lo32 (fres c s .f32 R)` for an
operation tree `R` whose leaves are loaded words and scalars and whose
inner nodes read earlier results through `fbits .f32 (fres …)`; the spec's
is `F32.lift R'` for the same tree with `(F32.lift …).toNat` inside. The
two trees agree up to the bits of inner NaNs, and every operation of
`Float.lean` gives the same result for any two NaN inputs (`*_congr`),
so `R = R'` and the value relation holds (`feq_of_eq`).
-/
import Ptx.Auto.Tactic

set_option linter.unusedSimpArgs false

namespace Ptx.Fp

/-- Equal patterns, or two NaNs. -/
def NanEq (F : Fmt) (a b : Nat) : Prop := a = b ∨ (F.isNaN a = true ∧ F.isNaN b = true)

theorem NanEq.refl (F : Fmt) (a : Nat) : NanEq F a a := .inl rfl

/-- The output relation of a bit-exact float map. -/
def feq32 (x y : BitVec 32) : Prop := NanEq Fmt.f32 x.toNat y.toNat

instance (x y : BitVec 32) : Decidable (feq32 x y) := by unfold feq32 NanEq; infer_instance

/-- Ordinal of a non-NaN `.f32` pattern: patterns in numeric order, `-0` and
`+0` both 0. -/
def ord32 (x : Nat) : Int := if Fmt.f32.sgn x then -((x - Fmt.f32.signBit : Nat) : Int) else x

/-- Representable `.f32` numbers between two finite patterns. -/
def ulps32 (x y : BitVec 32) : Nat := (ord32 x.toNat - ord32 y.toNat).natAbs

/-- The error-bound relation: within `k` units in the last place. -/
def within32 (k : Nat) (x y : BitVec 32) : Prop :=
  (Fmt.f32.isNaN x.toNat = true ∧ Fmt.f32.isNaN y.toNat = true) ∨
  (Fmt.f32.isInf x.toNat = true ∧ x = y) ∨
  (Fmt.f32.isNaN x.toNat = false ∧ Fmt.f32.isInf x.toNat = false ∧
    Fmt.f32.isNaN y.toNat = false ∧ Fmt.f32.isInf y.toNat = false ∧ ulps32 x y ≤ k)

instance (k : Nat) (x y : BitVec 32) : Decidable (within32 k x y) := by unfold within32; infer_instance

theorem within32_of_feq {k : Nat} {x y : BitVec 32} (h : feq32 x y) : within32 k x y := by
  rcases h with h | h
  · have : x = y := BitVec.eq_of_toNat_eq h
    subst this
    by_cases hn : Fmt.f32.isNaN x.toNat = true
    · exact .inl ⟨hn, hn⟩
    by_cases hi : Fmt.f32.isInf x.toNat = true
    · exact .inr (.inl ⟨hi, rfl⟩)
    · simp only [Bool.not_eq_true] at hn hi
      exact .inr (.inr ⟨hn, hi, hn, hi, by simp [ulps32]⟩)
  · exact .inl h

end Ptx.Fp

namespace Ptx.Auto
open Ptx Ptx.Fp

/-- A float result as a 32-bit word, NaN as `Fmt.qnan`. -/
def F32.lift (r : Option Nat) : BitVec 32 := BitVec.ofNat 32 (r.getD Fmt.f32.qnan)

def F32.add (m : RMode) (ftz sat : Bool) (a b : BitVec 32) : BitVec 32 :=
  F32.lift (fadd Fmt.f32 m ftz sat a.toNat b.toNat)
def F32.sub (m : RMode) (ftz sat : Bool) (a b : BitVec 32) : BitVec 32 :=
  F32.lift (fsub Fmt.f32 m ftz sat a.toNat b.toNat)
def F32.mul (m : RMode) (ftz sat : Bool) (a b : BitVec 32) : BitVec 32 :=
  F32.lift (fmul Fmt.f32 m ftz sat a.toNat b.toNat)
def F32.div (m : RMode) (ftz : Bool) (a b : BitVec 32) : BitVec 32 :=
  F32.lift (fdiv Fmt.f32 m ftz a.toNat b.toNat)
def F32.fma (m : RMode) (ftz sat : Bool) (a b c : BitVec 32) : BitVec 32 :=
  F32.lift (ffma Fmt.f32 m ftz sat a.toNat b.toNat c.toNat)
def F32.sqrt (m : RMode) (ftz : Bool) (a : BitVec 32) : BitVec 32 :=
  F32.lift (fsqrt Fmt.f32 m ftz a.toNat)
def F32.rcp (m : RMode) (ftz : Bool) (a : BitVec 32) : BitVec 32 :=
  F32.lift (frcp Fmt.f32 m ftz a.toNat)
def F32.neg (ftz : Bool) (a : BitVec 32) : BitVec 32 := F32.lift (fneg Fmt.f32 ftz a.toNat)
def F32.abs (ftz : Bool) (a : BitVec 32) : BitVec 32 := F32.lift (fabs Fmt.f32 ftz a.toNat)
def F32.minmax (isMax ftz nan : Bool) (a b : BitVec 32) : BitVec 32 :=
  F32.lift (fminmax Fmt.f32 isMax ftz nan a.toNat b.toNat)

/-! ### NaN inputs: every operation sees only that they are NaN -/

section
variable {F : Fmt}

theorem isNaN_isSub {a : Nat} (hm : F.expMax ≠ 0) (h : F.isNaN a = true) : F.isSub a = false := by
  simp only [Fmt.isNaN, Fmt.isSub, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at *
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  left; rw [h.1]; exact hm

theorem flush_nan {a : Nat} (ftz : Bool) (hm : F.expMax ≠ 0) (h : F.isNaN a = true) :
    F.flush ftz a = a := by
  simp [Fmt.flush, isNaN_isSub hm h]

theorem isNaN_isInf {a : Nat} (h : F.isNaN a = true) : F.isInf a = false := by
  simp only [Fmt.isNaN, Fmt.isInf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at *
  simp [h.2]

theorem isNaN_isZero {a : Nat} (hm : F.expMax ≠ 0) (h : F.isNaN a = true) : F.isZero a = false := by
  simp only [Fmt.isNaN, Fmt.isZero, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at *
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  left; rw [h.1]; exact hm

end

theorem f32_expMax : Fmt.f32.expMax ≠ 0 := by decide

/-- One NaN-input step: rewrite both flushes and decide the NaN tests. -/
macro "nan_case" : tactic => `(tactic| (
  rcases ‹NanEq _ _ _› with h | ⟨h₁, h₂⟩
  · subst h; rfl
  · simp only [flush_nan _ f32_expMax h₁, flush_nan _ f32_expMax h₂, h₁, h₂, isNaN_isInf h₁,
      isNaN_isInf h₂, isNaN_isZero f32_expMax h₁, isNaN_isZero f32_expMax h₂, Bool.true_or,
      Bool.or_true, ite_true, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true]))

section
variable {m : RMode} {ftz sat nan isMax : Bool} {a a' b b' c c' : Nat}

theorem addCore_congr (ha : NanEq Fmt.f32 a a') (hb : NanEq Fmt.f32 b b') :
    addCore Fmt.f32 m ftz a b = addCore Fmt.f32 m ftz a' b' := by
  rcases ha with rfl | ⟨h₁, h₂⟩ <;> rcases hb with rfl | ⟨k₁, k₂⟩
  · rfl
  all_goals simp [addCore, *]

theorem fadd_congr (ha : NanEq Fmt.f32 a a') (hb : NanEq Fmt.f32 b b') :
    fadd Fmt.f32 m ftz sat a b = fadd Fmt.f32 m ftz sat a' b' := by
  unfold fadd; congr 1
  apply addCore_congr
  · rcases ha with rfl | ⟨h₁, h₂⟩
    · exact .inl rfl
    · exact .inr ⟨by rw [flush_nan _ f32_expMax h₁]; exact h₁, by rw [flush_nan _ f32_expMax h₂]; exact h₂⟩
  · rcases hb with rfl | ⟨h₁, h₂⟩
    · exact .inl rfl
    · exact .inr ⟨by rw [flush_nan _ f32_expMax h₁]; exact h₁, by rw [flush_nan _ f32_expMax h₂]; exact h₂⟩

theorem fsub_congr (ha : NanEq Fmt.f32 a a') (hb : NanEq Fmt.f32 b b') :
    fsub Fmt.f32 m ftz sat a b = fsub Fmt.f32 m ftz sat a' b' := by
  unfold fsub; simp only
  congr 1
  apply addCore_congr
  · rcases ha with rfl | ⟨h₁, h₂⟩
    · exact .inl rfl
    · exact .inr ⟨by rw [flush_nan _ f32_expMax h₁]; exact h₁, by rw [flush_nan _ f32_expMax h₂]; exact h₂⟩
  · rcases hb with rfl | ⟨h₁, h₂⟩
    · exact .inl rfl
    · right
      rw [flush_nan _ f32_expMax h₁, flush_nan _ f32_expMax h₂]
      simp [h₁, h₂]

theorem fmul_congr (ha : NanEq Fmt.f32 a a') (hb : NanEq Fmt.f32 b b') :
    fmul Fmt.f32 m ftz sat a b = fmul Fmt.f32 m ftz sat a' b' := by
  rcases ha with rfl | ⟨h₁, h₂⟩ <;> rcases hb with rfl | ⟨k₁, k₂⟩
  · rfl
  all_goals simp [fmul, flush_nan _ f32_expMax, isNaN_isInf, isNaN_isZero f32_expMax, *]

theorem ffma_congr (ha : NanEq Fmt.f32 a a') (hb : NanEq Fmt.f32 b b') (hc : NanEq Fmt.f32 c c') :
    ffma Fmt.f32 m ftz sat a b c = ffma Fmt.f32 m ftz sat a' b' c' := by
  rcases ha with rfl | ⟨h₁, h₂⟩ <;> rcases hb with rfl | ⟨k₁, k₂⟩ <;> rcases hc with rfl | ⟨l₁, l₂⟩
  · rfl
  all_goals simp [ffma, flush_nan _ f32_expMax, isNaN_isInf, isNaN_isZero f32_expMax, *]

theorem fdiv_congr (ha : NanEq Fmt.f32 a a') (hb : NanEq Fmt.f32 b b') :
    fdiv Fmt.f32 m ftz a b = fdiv Fmt.f32 m ftz a' b' := by
  rcases ha with rfl | ⟨h₁, h₂⟩ <;> rcases hb with rfl | ⟨k₁, k₂⟩
  · rfl
  all_goals simp [fdiv, flush_nan _ f32_expMax, isNaN_isInf, isNaN_isZero f32_expMax, *]

theorem frcp_congr (ha : NanEq Fmt.f32 a a') : frcp Fmt.f32 m ftz a = frcp Fmt.f32 m ftz a' :=
  fdiv_congr (.refl _ _) ha

theorem fsqrt_congr (ha : NanEq Fmt.f32 a a') : fsqrt Fmt.f32 m ftz a = fsqrt Fmt.f32 m ftz a' := by
  rcases ha with rfl | ⟨h₁, h₂⟩
  · rfl
  simp [fsqrt, flush_nan _ f32_expMax, *]

theorem fneg_congr (ha : NanEq Fmt.f32 a a') : fneg Fmt.f32 ftz a = fneg Fmt.f32 ftz a' := by
  rcases ha with rfl | ⟨h₁, h₂⟩
  · rfl
  simp [fneg, flush_nan _ f32_expMax, *]

theorem fabs_congr (ha : NanEq Fmt.f32 a a') : fabs Fmt.f32 ftz a = fabs Fmt.f32 ftz a' := by
  rcases ha with rfl | ⟨h₁, h₂⟩
  · rfl
  simp [fabs, flush_nan _ f32_expMax, *]

theorem fminmax_congr (ha : NanEq Fmt.f32 a a') (hb : NanEq Fmt.f32 b b') :
    fminmax Fmt.f32 isMax ftz nan a b = fminmax Fmt.f32 isMax ftz nan a' b' := by
  rcases ha with rfl | ⟨h₁, h₂⟩ <;> rcases hb with rfl | ⟨k₁, k₂⟩
  · rfl
  all_goals
    simp only [fminmax, flush_nan _ f32_expMax, *]
    by_cases hx : Fmt.f32.isNaN (Fmt.f32.flush ftz a) = true <;>
      by_cases hy : Fmt.f32.isNaN (Fmt.f32.flush ftz b) = true <;> simp_all

end

/-! ### Kernel results against the spec -/

theorem lo32_ofNat64 (x : Nat) : lo32 (BitVec.ofNat 64 x) = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp [lo32, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

theorem qnan32_isNaN : Fmt.f32.isNaN Fmt.f32.qnan = true := by decide

/-- What an `.f32` instruction leaves in its register, read back as
`.f32`, against the spec's value of the same result. -/
theorem fres_nanEq (c : Ctx) (s : TState) (r : Option Nat) :
    NanEq Fmt.f32 (fbits .f32 (fres c s .f32 r)) (F32.lift r).toNat := by
  cases r with
  | some x =>
    left
    simp [fbits, fres, F32.lift, lo32_ofNat64, Ty.width]
  | none =>
    right
    refine ⟨?_, by simp [F32.lift, Nat.mod_eq_of_lt (by decide : Fmt.f32.qnan < 2 ^ 32), qnan32_isNaN]⟩
    simp only [fbits, fres, Ty.width, lo32_ofNat64, Ty.fmt]
    by_cases h : Fmt.f32.isNaN (lo32 (c.nan s)).toNat = true
    · simp [h, Nat.mod_eq_of_lt (BitVec.isLt (lo32 (c.nan s)))]
    · simp [h, Nat.mod_eq_of_lt (by decide : Fmt.f32.qnan < 2 ^ 32), qnan32_isNaN]

theorem feq_of_eq (c : Ctx) (s : TState) {r r' : Option Nat} (h : r = r') :
    feq32 (lo32 (fres c s .f32 r)) (F32.lift r') := by
  subst h
  have := fres_nanEq c s r
  unfold feq32
  simpa [fbits, Ty.width] using this

theorem fres_nanEq_of_eq (c : Ctx) (s : TState) {r r' : Option Nat} (h : r = r') :
    NanEq Fmt.f32 (fbits .f32 (fres c s .f32 r)) (F32.lift r').toNat := h ▸ fres_nanEq c s r

end Ptx.Auto

/-- The value goal of a float map: unfold the spec's operations, then match
the kernel's operation tree against the spec's node by node. -/
macro "ptx_fvalue" : tactic => `(tactic| (
  simp only [Ptx.Auto.MapSpec.val, ptx_spec, Ptx.lo32_ext32, Ptx.lo32_rd_b4, Ptx.Auto.F32.add,
    Ptx.Auto.F32.sub, Ptx.Auto.F32.mul, Ptx.Auto.F32.div, Ptx.Auto.F32.fma, Ptx.Auto.F32.sqrt,
    Ptx.Auto.F32.rcp, Ptx.Auto.F32.neg, Ptx.Auto.F32.abs, Ptx.Auto.F32.minmax]
  first
    | refine Ptx.Fp.within32_of_feq (Ptx.Auto.feq_of_eq _ _ ?_)
    | refine Ptx.Auto.feq_of_eq _ _ ?_
  repeat' first
    | rfl
    | exact Ptx.Fp.NanEq.refl _ _
    | refine Ptx.Auto.fres_nanEq_of_eq _ _ ?_
    | apply Ptx.Auto.fadd_congr
    | apply Ptx.Auto.fsub_congr
    | apply Ptx.Auto.fmul_congr
    | apply Ptx.Auto.ffma_congr
    | apply Ptx.Auto.fdiv_congr
    | apply Ptx.Auto.frcp_congr
    | apply Ptx.Auto.fsqrt_congr
    | apply Ptx.Auto.fneg_congr
    | apply Ptx.Auto.fabs_congr
    | apply Ptx.Auto.fminmax_congr))

/-- Float specs: `ptx_value` falls back to `ptx_fvalue`. -/
macro_rules | `(tactic| ptx_value) => `(tactic| ptx_fvalue)
