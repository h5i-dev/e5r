/-
The algebras of accumulator cells (Ptx/Logic/Phases.lean, `CellAlg`): the
commutative and associative atomics of PTX at 32 and 64 bits, each with its
unit, and the lemma that the instruction's update (`atomVal`) combines the
old value with the operand by the algebra's operation (`Accum`).

* `add` (unit 0), `and` (all ones), `or` and `xor` (0);
* `min.u`, `max.u`, `min.s`, `max.s` (units: the largest and smallest values
  of the order).

`exch` and `cas` are not here: the value they leave depends on the order of
the threads, so no commutative fold describes it (docs/verification-ptx.md,
"Atomics").
-/
import Ptx.Logic.Phases

namespace Ptx

theorem trunc_b4 (v : Val) : Size.b4.trunc v = ext32 (lo32 v) := rfl

@[simp] theorem lo32_ext32' (x : BitVec 32) : lo32 (ext32 x) = x := lo32_ext32 x

theorem trunc_b4_ext32 (x : BitVec 32) : Size.b4.trunc (ext32 x) = ext32 x := by
  rw [trunc_b4, lo32_ext32]

theorem ext32_lo32_of_trunc {v : Val} (h : Size.b4.trunc v = v) : ext32 (lo32 v) = v := h

/-! ### A 32-bit algebra from an operation on `BitVec 32` -/

/-- The cell algebra of a commutative monoid `f`, `u` on `BitVec 32`. -/
def alg32 (f : BitVec 32 → BitVec 32 → BitVec 32) (u : BitVec 32)
    (comm : ∀ x y, f x y = f y x) (assoc : ∀ x y z, f (f x y) z = f x (f y z))
    (unit : ∀ x, f x u = x) : CellAlg where
  sz := .b4
  op x y := ext32 (f (lo32 x) (lo32 y))
  e := ext32 u
  comm x y := by rw [comm]
  assoc x y z := by simp only [lo32_ext32, assoc]
  unit x hx := by rw [lo32_ext32, unit, ext32_lo32_of_trunc hx]
  closed x y := trunc_b4_ext32 _
  e_ok := trunc_b4_ext32 _

/-- The cell algebra of a commutative monoid on `BitVec 64`. -/
def alg64 (f : BitVec 64 → BitVec 64 → BitVec 64) (u : BitVec 64)
    (comm : ∀ x y, f x y = f y x) (assoc : ∀ x y z, f (f x y) z = f x (f y z))
    (unit : ∀ x, f x u = x) : CellAlg where
  sz := .b8
  op := f
  e := u
  comm := comm
  assoc := assoc
  unit x _ := unit x
  closed _ _ := rfl
  e_ok := rfl

/-! ### Minimum and maximum of a total order given by a Boolean `le` -/

section
variable {w : Nat} (le : BitVec w → BitVec w → Bool)
  (total : ∀ x y, le x y = true ∨ le y x = true)
  (antisymm : ∀ x y, le x y = true → le y x = true → x = y)
  (trans : ∀ x y z, le x y = true → le y z = true → le x z = true)

def bmin (x y : BitVec w) : BitVec w := if le x y then x else y

include total antisymm in
theorem bmin_comm (x y : BitVec w) : bmin le x y = bmin le y x := by
  unfold bmin
  cases h1 : le x y <;> cases h2 : le y x <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rcases total x y with h | h <;> simp_all
  · exact antisymm x y h1 h2

include total antisymm trans in
theorem bmin_assoc (x y z : BitVec w) : bmin le (bmin le x y) z = bmin le x (bmin le y z) := by
  cases h1 : le x y <;> cases h2 : le y z <;> cases h3 : le x z <;>
    simp only [bmin, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
  · -- z ≤ y ≤ x and x ≤ z
    have hyx : le y x = true := by rcases total x y with h | h <;> simp_all
    have hzy : le z y = true := by rcases total y z with h | h <;> simp_all
    exact (antisymm x z h3 (trans z y x hzy hyx)).symm
  · have := trans x y z h1 h2; simp_all

theorem bmin_unit (u : BitVec w) (hu : ∀ x, le x u = true) (x : BitVec w) : bmin le x u = x := by
  simp [bmin, hu x]

end

/-! ### The orders of PTX `min`/`max` -/

theorem ule_total {w} (x y : BitVec w) : x.ule y = true ∨ y.ule x = true := by
  simp only [BitVec.ule, decide_eq_true_eq]; omega
theorem ule_antisymm {w} (x y : BitVec w) (h : x.ule y = true) (h' : y.ule x = true) : x = y := by
  simp only [BitVec.ule, decide_eq_true_eq] at h h'; exact BitVec.eq_of_toNat_eq (by omega)
theorem ule_trans {w} (x y z : BitVec w) (h : x.ule y = true) (h' : y.ule z = true) : x.ule z = true := by
  simp only [BitVec.ule, decide_eq_true_eq] at *; omega

theorem sle_total {w} (x y : BitVec w) : x.sle y = true ∨ y.sle x = true := by
  simp only [BitVec.sle, decide_eq_true_eq]; omega
theorem sle_antisymm {w} (x y : BitVec w) (h : x.sle y = true) (h' : y.sle x = true) : x = y := by
  simp only [BitVec.sle, decide_eq_true_eq] at h h'
  exact BitVec.eq_of_toInt_eq (by omega)
theorem sle_trans {w} (x y z : BitVec w) (h : x.sle y = true) (h' : y.sle z = true) : x.sle z = true := by
  simp only [BitVec.sle, decide_eq_true_eq] at *; omega

/-- The reversed orders, for `max`. -/
theorem rev_total {w} {le : BitVec w → BitVec w → Bool} (t : ∀ x y, le x y = true ∨ le y x = true) :
    ∀ x y, le y x = true ∨ le x y = true := fun x y => (t x y).symm
theorem rev_antisymm {w} {le : BitVec w → BitVec w → Bool}
    (a : ∀ x y, le x y = true → le y x = true → x = y) :
    ∀ x y, le y x = true → le x y = true → x = y := fun x y h h' => a x y h' h
theorem rev_trans {w} {le : BitVec w → BitVec w → Bool}
    (t : ∀ x y z, le x y = true → le y z = true → le x z = true) :
    ∀ x y z, le y x = true → le z y = true → le z x = true := fun x y z h h' => t z y x h' h

theorem ule_max {w} (x : BitVec w) : x.ule (BitVec.allOnes w) = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_allOnes]; have := x.isLt; omega
theorem ule_zero {w} (x : BitVec w) : (0#w).ule x = true := by
  simp [BitVec.ule]

/-- The largest and smallest signed values. -/
def smax (w : Nat) : BitVec w := BitVec.ofInt w (2 ^ (w - 1) - 1)
def smin (w : Nat) : BitVec w := BitVec.ofInt w (-(2 ^ (w - 1)))

theorem smax32_toInt : (smax 32).toInt = 2 ^ 31 - 1 := by decide
theorem smin32_toInt : (smin 32).toInt = -(2 ^ 31) := by decide
theorem smax64_toInt : (smax 64).toInt = 2 ^ 63 - 1 := by decide
theorem smin64_toInt : (smin 64).toInt = -(2 ^ 63) := by decide

theorem sle_smax32 (x : BitVec 32) : x.sle (smax 32) = true := by
  simp only [BitVec.sle, decide_eq_true_eq, smax32_toInt]
  have := BitVec.toInt_lt (x := x); simp at this; omega
theorem smin_sle32 (x : BitVec 32) : (smin 32).sle x = true := by
  simp only [BitVec.sle, decide_eq_true_eq, smin32_toInt]
  have := BitVec.le_toInt (x := x); simp at this; omega
theorem sle_smax64 (x : BitVec 64) : x.sle (smax 64) = true := by
  simp only [BitVec.sle, decide_eq_true_eq, smax64_toInt]
  have := BitVec.toInt_lt (x := x); simp at this; omega
theorem smin_sle64 (x : BitVec 64) : (smin 64).sle x = true := by
  simp only [BitVec.sle, decide_eq_true_eq, smin64_toInt]
  have := BitVec.le_toInt (x := x); simp at this; omega

/-! ### The algebras -/

def add32 : CellAlg := alg32 (· + ·) 0 BitVec.add_comm BitVec.add_assoc BitVec.add_zero
def and32 : CellAlg := alg32 (· &&& ·) (BitVec.allOnes 32) BitVec.and_comm BitVec.and_assoc
  (fun _ => BitVec.and_allOnes)
def or32 : CellAlg := alg32 (· ||| ·) 0 BitVec.or_comm BitVec.or_assoc (fun _ => BitVec.or_zero)
def xor32 : CellAlg := alg32 (· ^^^ ·) 0 BitVec.xor_comm BitVec.xor_assoc (fun _ => BitVec.xor_zero)
def minu32 : CellAlg := alg32 (bmin BitVec.ule) (BitVec.allOnes 32)
  (bmin_comm _ ule_total ule_antisymm) (bmin_assoc _ ule_total ule_antisymm ule_trans)
  (bmin_unit _ _ ule_max)
def maxu32 : CellAlg := alg32 (bmin fun x y => BitVec.ule y x) 0
  (bmin_comm _ (rev_total ule_total) (rev_antisymm ule_antisymm))
  (bmin_assoc _ (rev_total ule_total) (rev_antisymm ule_antisymm) (rev_trans ule_trans))
  (bmin_unit _ _ ule_zero)
def mins32 : CellAlg := alg32 (bmin BitVec.sle) (smax 32)
  (bmin_comm _ sle_total sle_antisymm) (bmin_assoc _ sle_total sle_antisymm sle_trans)
  (bmin_unit _ _ sle_smax32)
def maxs32 : CellAlg := alg32 (bmin fun x y => BitVec.sle y x) (smin 32)
  (bmin_comm _ (rev_total sle_total) (rev_antisymm sle_antisymm))
  (bmin_assoc _ (rev_total sle_total) (rev_antisymm sle_antisymm) (rev_trans sle_trans))
  (bmin_unit _ _ smin_sle32)

def add64 : CellAlg := alg64 (· + ·) 0 BitVec.add_comm BitVec.add_assoc BitVec.add_zero
def and64 : CellAlg := alg64 (· &&& ·) (BitVec.allOnes 64) BitVec.and_comm BitVec.and_assoc
  (fun _ => BitVec.and_allOnes)
def or64 : CellAlg := alg64 (· ||| ·) 0 BitVec.or_comm BitVec.or_assoc (fun _ => BitVec.or_zero)
def xor64 : CellAlg := alg64 (· ^^^ ·) 0 BitVec.xor_comm BitVec.xor_assoc (fun _ => BitVec.xor_zero)
def minu64 : CellAlg := alg64 (bmin BitVec.ule) (BitVec.allOnes 64)
  (bmin_comm _ ule_total ule_antisymm) (bmin_assoc _ ule_total ule_antisymm ule_trans)
  (bmin_unit _ _ ule_max)
def maxu64 : CellAlg := alg64 (bmin fun x y => BitVec.ule y x) 0
  (bmin_comm _ (rev_total ule_total) (rev_antisymm ule_antisymm))
  (bmin_assoc _ (rev_total ule_total) (rev_antisymm ule_antisymm) (rev_trans ule_trans))
  (bmin_unit _ _ ule_zero)
def mins64 : CellAlg := alg64 (bmin BitVec.sle) (smax 64)
  (bmin_comm _ sle_total sle_antisymm) (bmin_assoc _ sle_total sle_antisymm sle_trans)
  (bmin_unit _ _ sle_smax64)
def maxs64 : CellAlg := alg64 (bmin fun x y => BitVec.sle y x) (smin 64)
  (bmin_comm _ (rev_total sle_total) (rev_antisymm sle_antisymm))
  (bmin_assoc _ (rev_total sle_total) (rev_antisymm sle_antisymm) (rev_trans sle_trans))
  (bmin_unit _ _ smin_sle64)

@[simp] theorem add32_sz : add32.sz = .b4 := rfl
@[simp] theorem add32_e : add32.e = 0 := rfl
theorem add32_op (x y : Val) : add32.op x y = ext32 (lo32 x + lo32 y) := rfl

/-! ### What the instructions combine -/

/-- A 32-bit update `old ↦ f old b` combines by `alg32 f`. -/
theorem accum32 {f : BitVec 32 → BitVec 32 → BitVec 32} {u : BitVec 32} {c a n} (b : Val) :
    Accum (alg32 f u c a n) (fun old => ext32 (f (lo32 old) (lo32 b))) (ext32 (lo32 b)) := by
  intro w _
  show Size.b4.trunc _ = ext32 (f (lo32 w) (lo32 (ext32 (lo32 b))))
  rw [trunc_b4_ext32, lo32_ext32]

/-- A 64-bit update `old ↦ f old b` combines by `alg64 f`. -/
theorem accum64 {f : BitVec 64 → BitVec 64 → BitVec 64} {u : BitVec 64} {c a n} (b : Val) :
    Accum (alg64 f u c a n) (fun old => f old b) b := fun _ _ => rfl

/-! ### Folds of contributions -/

/-- `e ∘ f 0 ∘ … ∘ f (k-1)`. -/
def afold (A : CellAlg) (f : Nat → Val) : Nat → Val
  | 0 => A.e
  | k + 1 => A.op (afold A f k) (f k)

/-- The combination of `f t` over a list of threads. -/
def tfold (A : CellAlg) (l : List Tid) (f : Tid → Val) : Val := (l.map f).foldr A.op A.e

theorem afold_trunc (A : CellAlg) (f : Nat → Val) : ∀ k, A.sz.trunc (afold A f k) = afold A f k
  | 0 => A.e_ok
  | _ + 1 => A.closed _ _

theorem tfold_trunc (A : CellAlg) (l : List Tid) (f : Tid → Val) :
    A.sz.trunc (tfold A l f) = tfold A l f := by
  cases l with
  | nil => exact A.e_ok
  | cons a l => exact A.closed _ _

theorem tfold_congr {A : CellAlg} {l : List Tid} {f g : Tid → Val} (h : ∀ t ∈ l, f t = g t) :
    tfold A l f = tfold A l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [tfold, List.map_cons, List.foldr_cons] at ih ⊢
    rw [h a (by simp), ih fun t ht => h t (by simp [ht])]

theorem op_e_e (A : CellAlg) : A.op A.e A.e = A.e := A.unit _ A.e_ok

theorem tfold_e (A : CellAlg) (l : List Tid) : tfold A l (fun _ => A.e) = A.e := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [tfold, List.map_cons, List.foldr_cons] at ih ⊢; rw [ih, op_e_e]

/-- Changing one member of a list without duplicates by combining `δ`
combines `δ` into the fold. -/
theorem tfold_update {A : CellAlg} {l : List Tid} (hl : l.Nodup) {t : Tid} (ht : t ∈ l)
    {f g : Tid → Val} {δ : Val} (hg : ∀ u ∈ l, u ≠ t → g u = f u) (hgt : g t = A.op (f t) δ) :
    tfold A l g = A.op (tfold A l f) δ := by
  induction l with
  | nil => simp at ht
  | cons a l ih =>
    simp only [tfold, List.map_cons, List.foldr_cons] at ih ⊢
    rw [List.nodup_cons] at hl
    by_cases hta : t = a
    · subst hta
      have : tfold A l g = tfold A l f :=
        tfold_congr fun u hu => hg u (by simp [hu]) fun h => hl.1 (h ▸ hu)
      simp only [tfold] at this
      rw [this, hgt, A.assoc, A.comm δ, ← A.assoc]
    · have hm : t ∈ l := by simp [hta] at ht; exact ht
      rw [ih hl.2 hm (fun u hu hut => hg u (by simp [hu]) hut), hg a (by simp) (Ne.symm hta),
        A.assoc]

end Ptx
