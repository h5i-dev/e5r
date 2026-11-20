import E5R.Auto

/-
The specification of `u64 sum(const u64 *a, u64 n)` (demo/src/sum.c, the
same source as examples/sum.c), shared by Demo/SumB.lean (e5r build) and
Demo/SumA.lean (ordinary build). It is the specification of
lean/Examples/Sum.lean, restated without that file's image.
-/
namespace Demo.Sum
open E5R

/-- The sum of a list of words, modulo 2^64. -/
def sumW (xs : List Word) : Word := xs.foldl (· + ·) 0

structure Args where
  a : Word
  xs : List Word

/-- a0 = a, a1 = n; returns the sum in a0. It may read the array and nothing
    else, and uses no stack. -/
def spec : Spec Args where
  pre := fun ⟨a, xs⟩ s => s.reg Reg.a0 = a ∧ s.reg Reg.a1 = BitVec.ofNat 64 xs.length ∧
    8 * xs.length < 2^64 ∧ aligned a 8 ∧ arr64 s.mem a xs
  post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs
  reads := fun ⟨a, xs⟩ _ => [arrRegion a xs]

/-! Facts about `sumW` the proofs use: one more element, counted from the end. -/

theorem sumW_step (xs : List Word) (m : Nat) (h : 0 < m) (h' : m ≤ xs.length) :
    sumW (xs.take (xs.length - (m - 1))) = sumW (xs.take (xs.length - m)) + xs[xs.length - m] := by
  rw [show xs.length - (m - 1) = xs.length - m + 1 by omega, List.take_add_one,
    List.getElem?_eq_getElem (by omega)]
  simp only [sumW, Option.toList, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sumW_last (xs : List Word) (m : Nat) (h : m = 1) (h' : m ≤ xs.length) :
    sumW xs = sumW (xs.take (xs.length - m)) + xs[xs.length - m] := by
  subst h
  have := sumW_step xs 1 (by omega) h'
  rwa [Nat.sub_self, Nat.sub_zero, List.take_length] at this

theorem sumW_nil (xs : List Word) (h : xs.length = 0) : sumW xs = 0 := by
  simp_all [List.length_eq_zero_iff, sumW]

end Demo.Sum
