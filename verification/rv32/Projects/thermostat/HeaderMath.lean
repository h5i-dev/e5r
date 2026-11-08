import Projects.thermostat.HeaderSpec
import Projects.thermostat.Literal
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderMath
open E5R E5R.Thermostat

def upperFlag (b : BitVec 8) : Word := alu .sltu (BitVec.ofNat 32 b.toNat+0xffffffbf#32) 26#32

theorem flag : ∀ b : BitVec 8, upperFlag b = (if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then 1#32 else 0#32) := by decide +kernel

theorem folded : ∀ b : BitVec 8,
    ((upperFlag b <<< 5) ||| BitVec.ofNat 32 b.toNat) = BitVec.ofNat 32 (HeaderSpec.lower b).toNat := by decide +kernel

theorem compare (a b : BitVec 8) :
    taken .ne ((upperFlag a <<< 5) ||| BitVec.ofNat 32 a.toNat)
      ((upperFlag b <<< 5) ||| BitVec.ofNat 32 b.toNat) = decide (HeaderSpec.lower a ≠ HeaderSpec.lower b) := by
  rw [folded,folded]
  change decide (BitVec.ofNat 32 (HeaderSpec.lower a).toNat ≠ BitVec.ofNat 32 (HeaderSpec.lower b).toNat) = _
  simp only [ne_eq,Literal.byte_injective]

theorem same_cons (a b : BitVec 8) (as bs : List (BitVec 8)) :
    HeaderSpec.same (a::as) (b::bs) = (decide (HeaderSpec.lower a = HeaderSpec.lower b) && HeaderSpec.same as bs) := by
  by_cases he : HeaderSpec.lower a = HeaderSpec.lower b <;> simp [HeaderSpec.same,he]
end E5R.Thermostat.HeaderMath
