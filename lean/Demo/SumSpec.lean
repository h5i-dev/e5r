import NoCompiler.Vocab

/-
The specification of `u64 sum(const u64 *a, u64 n)` (examples/demo/src/sum.c, the
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

/-! `u64 sum2(const u64 *a, u64 n, const u64 *b, u64 m)`: `sum(a, n) + sum(b, m)`,
the caller (the specification of lean/Examples/Sum2.lean). -/

structure Args2 where
  a : Word
  xs : List Word
  b : Word
  ys : List Word

/-- a0, a1 = the first array, a2, a3 = the second; returns the sum of both. It
    reads only the arrays and uses 32 bytes of stack, which the arrays must not
    overlap. -/
def spec2 : Spec Args2 where
  pre := fun ⟨a, xs, b, ys⟩ s =>
    s.reg Reg.a0 = a ∧ s.reg Reg.a1 = BitVec.ofNat 64 xs.length ∧
    s.reg Reg.a2 = b ∧ s.reg Reg.a3 = BitVec.ofNat 64 ys.length ∧
    8 * xs.length < 2 ^ 64 ∧ 8 * ys.length < 2 ^ 64 ∧ aligned a 8 ∧ aligned b 8 ∧
    arr64 s.mem a xs ∧ arr64 s.mem b ys ∧
    (∀ x, (arrRegion a xs).mem x → ¬ (Spec.stackRegion s 32).mem x) ∧
    (∀ x, (arrRegion b ys).mem x → ¬ (Spec.stackRegion s 32).mem x)
  post := fun ⟨_, xs, _, ys⟩ _ s' => s'.reg Reg.a0 = sumW xs + sumW ys
  reads := fun ⟨a, xs, b, ys⟩ _ => [arrRegion a xs, arrRegion b ys]
  stack := 32

/-! Facts about `sumW` the proofs use: one more element, counted from the end. -/

theorem sumW_step (xs : List Word) (m : Nat) (h : 0 < m) (h' : m ≤ xs.length) :
    sumW (xs.take (xs.length - (m - 1))) = sumW (xs.take (xs.length - m)) + xs[xs.length - m] :=
  foldl_take_sub_pred _ _ xs m h h'

theorem sumW_last (xs : List Word) (m : Nat) (h : m = 1) (h' : m ≤ xs.length) :
    sumW xs = sumW (xs.take (xs.length - m)) + xs[xs.length - m] := foldl_eq_last _ _ xs m h h'

theorem sumW_nil (xs : List Word) (h : xs.length = 0) : sumW xs = 0 := foldl_of_length_zero _ _ xs h

end Demo.Sum
