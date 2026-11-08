import Projects.thermostat.HttpDecMath
import Projects.thermostat.DecimalDigits
namespace E5R.Thermostat.HttpDecOnesMath
open E5R E5R.Thermostat

def high (n : Nat) : Word := muldiv .mulhu (BitVec.ofNat 32 n) 3435973837#32

def byteWord (n : Nat) : Word :=
  ((BitVec.ofNat 32 n-(high n &&& 248#32))-((high n >>> 2) &&& 0xfffffffe#32)) ||| 48#32

/-- Checked bounded arithmetic for the emitted byte, including the deliberate
    low-byte truncation after the reciprocal remainder calculation. -/
theorem value (n : Nat) (hn : n≤832) : byteOf (byteWord n) 0=DecimalDigits.digit (n%10) := by
  have h : ∀ k : Fin 833, byteOf (byteWord k.val) 0=DecimalDigits.digit (k.val%10) := by decide +kernel
  exact h ⟨n,by omega⟩
end E5R.Thermostat.HttpDecOnesMath
