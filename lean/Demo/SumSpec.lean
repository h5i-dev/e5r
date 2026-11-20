import NoCompiler.Vocab

/-
The specification of `u64 sum(const u64 *a, u64 n)` (demo/src/sum.c, the
same source as examples/sum.c), shared by Demo/SumB.lean (nocompiler build) and
Demo/SumA.lean (ordinary build). It is the specification of
lean/Examples/Sum.lean, restated without that file's image.
-/
namespace Demo.Sum
open NoCompiler NoCompiler.Vocab

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
    sumW (xs.take (xs.length - (m - 1))) = sumW (xs.take (xs.length - m)) + xs[xs.length - m] :=
  foldl_take_sub_pred _ _ xs m h h'

theorem sumW_last (xs : List Word) (m : Nat) (h : m = 1) (h' : m ≤ xs.length) :
    sumW xs = sumW (xs.take (xs.length - m)) + xs[xs.length - m] := foldl_eq_last _ _ xs m h h'

theorem sumW_nil (xs : List Word) (h : xs.length = 0) : sumW xs = 0 := foldl_of_length_zero _ _ xs h

end Demo.Sum
