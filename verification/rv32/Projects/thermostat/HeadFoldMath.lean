import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.Literal
namespace E5R.Thermostat.HeadFoldMath
open E5R E5R.Thermostat HttpRequestSpec

/-- The exact four ALU effects emitted for ASCII folding in parse_head. -/
def word (b : BitVec 8) : Word :=
  let v := BitVec.ofNat 32 b.toNat
  alu .or v (alu .sll (alu .sltu (alu .add v 0xffffffbf#32) 26#32) 5#32)

theorem lower_word : ∀ b : BitVec 8, word b=BitVec.ofNat 32 (lower b.toNat) := by decide +kernel

theorem lower_bound : ∀ b : BitVec 8, lower b.toNat<256 := by decide +kernel

theorem comparison (actual expected : BitVec 8) :
    taken .ne (word actual) (BitVec.ofNat 32 expected.toNat)=decide (lower actual.toNat≠expected.toNat) := by
  rw [lower_word]
  change decide (BitVec.ofNat 32 (lower actual.toNat)≠BitVec.ofNat 32 expected.toNat)=_
  have injective : BitVec.ofNat 32 (lower actual.toNat)=BitVec.ofNat 32 expected.toNat ↔ lower actual.toNat=expected.toNat := by
    constructor
    · intro eq
      have values := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := lower_bound actual;omega : lower actual.toNat<2^32),
        Nat.mod_eq_of_lt (by have := expected.isLt;omega : expected.toNat<2^32)] at values
      exact values
    · intro eq;rw [eq]
  simp only [ne_eq,injective]
end E5R.Thermostat.HeadFoldMath
