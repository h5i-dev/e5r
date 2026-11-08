import Projects.thermostat.MainMethodSpec
import Projects.thermostat.Memory
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestByteValue
open E5R E5R.Thermostat

theorem ofNat (n : Nat) (bound : n≤255) : byteOf (BitVec.ofNat 32 n) 0=BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,Nat.pow_zero,Nat.div_one,Nat.mod_eq_of_lt (by omega : n<2^32)]

theorem tag (m : MainMethodSpec.Method) : MainMethodSpec.tag m≤6 := by
  cases m <;> decide
end E5R.Thermostat.MainRequestByteValue
