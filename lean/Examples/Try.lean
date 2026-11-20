import Examples.Sum
import NoCompiler.Auto

namespace Examples.Sum2
open NoCompiler Examples.Sum.Image
open Examples.Sum (sumW Args spec sum_verified)

/-- The logical arguments: two arrays. -/
structure Args2 where
  a : Word
  xs : List Word
  b : Word
  ys : List Word

/-- `sum2`: a0, a1 = the first array, a2, a3 = the second; returns the sum of
    both. It reads only the arrays and uses 32 bytes of stack, which the arrays
    must not overlap. -/
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

/-- `sum2` as compiled: correct, memory-safe, terminating, ABI-preserving,
    from `sum`'s specification. -/
set_option maxHeartbeats 400000 in
set_option nocompiler.auto.traceFile "/mnt/scratch/ec2-user/tmp/try/sum2.trace" in
theorem sum2_verified' : Verified code sum2_dom sum2_entry spec2 := by
  rintro ⟨a, xs, b, ys⟩ s he ⟨ha0, ha1, ha2, ha3, hl1, hl2, hal1, hal2, harr1, harr2, hd1, hd2⟩
  nocompiler_auto sum2_func s he [Auto.arr64_writeLE_of_outside hd1, Auto.arr64_writeLE_of_outside hd2] calls [sum_verified]
  all_goals trace_state
  all_goals sorry

end Examples.Sum2
