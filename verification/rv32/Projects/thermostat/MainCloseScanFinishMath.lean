import Projects.thermostat.Memory
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseScanFinishMath
open E5R E5R.Thermostat

theorem remaining (total token : Nat) (inside : token<total) (bound : total<2^32) :
    BitVec.ofNat 32 total+~~~(BitVec.ofNat 32 token)=BitVec.ofNat 32 (total-token-1) := by
  rw [BitVec.not_eq_neg_add,←BitVec.neg_add,←BitVec.ofNat_add,BitVec.add_neg_eq_sub,
    BitVec.ofNat_sub_ofNat_of_le total (token+1) (by omega) (by omega)]
  exact congrArg (BitVec.ofNat 32) (by omega)

theorem zeroTest (token : Nat) (bound : token<2^32) : taken .eq (BitVec.ofNat 32 token) (0 : Word)=decide (token=0) := by
  change decide (BitVec.ofNat 32 token=(0 : Word))=_
  have equivalent : BitVec.ofNat 32 token=(0 : Word) ↔ token=0 := by
    constructor
    · intro h
      have numeric := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,show (0 : Word).toNat=0 from rfl] using numeric
    · intro h
      subst token
      rfl
  simp only [equivalent]
end E5R.Thermostat.MainCloseScanFinishMath
