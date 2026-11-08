import Theories.Logic
namespace E5R.Thermostat.HeadByteFacts
open E5R

theorem lf : ∀ b : BitVec 8, taken .eq (BitVec.ofNat 32 b.toNat) 10#32=decide (b.toNat=10) := by decide +kernel
theorem cr : ∀ b : BitVec 8, taken .eq (BitVec.ofNat 32 b.toNat) 13#32=decide (b.toNat=13) := by decide +kernel
end E5R.Thermostat.HeadByteFacts
