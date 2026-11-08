import Projects.thermostat.HttpDecMath
import Projects.thermostat.DecimalDigits
namespace E5R.Thermostat.HttpDecTensMath
open E5R E5R.Thermostat

def word (n : Nat) : Word :=
  BitVec.ofNat 32 (n/10)-((BitVec.ofNat 32 (n/100) <<< 3)+(BitVec.ofNat 32 (n/100) <<< 1))

theorem value (n : Nat) (hn : n≤832) : word n=BitVec.ofNat 32 ((n/10)%10) := by
  have h : ∀ k : Fin 833, word k.val=BitVec.ofNat 32 ((k.val/10)%10) := by decide +kernel
  exact h ⟨n,by omega⟩

theorem reciprocal (n : Nat) (hn : n≤832) :
    muldiv .mulhu (BitVec.ofNat 32 (n/10)) 429496730#32=BitVec.ofNat 32 (n/100) := by
  simp only [muldiv,BitVec.toNat_ofNat]
  have hq : (n/10)%4294967296=n/10 := Nat.mod_eq_of_lt (by omega)
  rw [hq]
  change BitVec.ofNat 32 ((n/10)*429496730/4294967296)=_
  congr 1
  omega

theorem hundreds_test (n : Nat) (hn : n≤832) :
    taken .eq (BitVec.ofNat 32 (n/100)) (0 : Word)=decide (n<100) := by
  have h : ∀ k : Fin 833, taken .eq (BitVec.ofNat 32 (k.val/100)) (0 : Word)=decide (k.val<100) := by decide +kernel
  exact h ⟨n,by omega⟩

theorem tens_test (n : Nat) (hn : n≤832) :
    taken .ne (BitVec.ofNat 32 (n/10)) (0 : Word)=decide (10≤n) := by
  have h : ∀ k : Fin 833, taken .ne (BitVec.ofNat 32 (k.val/10)) (0 : Word)=decide (10≤k.val) := by decide +kernel
  exact h ⟨n,by omega⟩
end E5R.Thermostat.HttpDecTensMath
