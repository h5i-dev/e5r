/-
`u64 sum2(const u64 *a, u64 n, const u64 *b, u64 m)` from examples/sum.c:
`sum(a, n) + sum(b, m)`, as clang -O2 compiled it:

    111b4  addi sp, sp, -32          frame
    111b8  sd   ra, 24(sp)           save ra, s0, s1, s2
    111bc  sd   s0, 16(sp)
    111c0  sd   s1, 8(sp)
    111c4  sd   s2, 0(sp)
    111c8  addi s0, a3, 0            keep m and b across the first call
    111cc  addi s1, a2, 0
    111d0  auipc ra, 0               call sum(a, n)
    111d4  jalr ra, -64(ra)
    111d8  addi s2, a0, 0
    111dc  addi a0, s1, 0
    111e0  addi a1, s0, 0
    111e4  auipc ra, 0               call sum(b, m)
    111e8  jalr ra, -84(ra)
    111ec  add  a0, a0, s2
    111f0  ld   ra, 24(sp)           restore
    111f4  ld   s0, 16(sp)
    111f8  ld   s1, 8(sp)
    111fc  ld   s2, 0(sp)
    11200  addi sp, sp, 32
    11204  jalr zero, 0(ra)

The proof never looks at `sum`'s code: `nocompiler_auto ... calls
[sum_verified]` takes both calls through `VerifiedImg.call` with
`sum_verified`, using only `sum`'s specification (its result, the registers
it preserves, and that it writes no memory). The frame (four saves and their
restores), the registers `sum2` must give back and the arrays' separation
from the stack are the tactic's: the proof states only what `nocompiler_auto`
cannot know, that the two sums commute.
-/
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
theorem sum2_verified : VerifiedImg code sum2_dom sum2_entry spec2 := by
  rintro ⟨a, xs, b, ys⟩ s he ⟨ha0, ha1, ha2, ha3, hl1, hl2, hal1, hal2, harr1, harr2, hd1, hd2⟩
  nocompiler_auto sum2_func s he calls [sum_verified]
  case entry_ret_x50 => exact BitVec.add_comm _ _

end Examples.Sum2
