import Projects.thermostat.HeadTeRuleMath
namespace E5R.Thermostat.HeadClFlagsMath
open E5R E5R.Thermostat

theorem trailing (ve le : Nat) (ordered : ve≤le) (bound : le≤2048) :
    alu .sltu (0 : Word) (BitVec.ofNat 32 le-BitVec.ofNat 32 ve)=(if ve≠le then 1#32 else 0#32) := by
  rw [BitVec.ofNat_sub_ofNat_of_le le ve (by omega) ordered]
  change (if (0#32).ult (BitVec.ofNat 32 (le-ve)) then 1#32 else 0#32)=_
  have test : (0#32).ult (BitVec.ofNat 32 (le-ve))=decide (ve≠le) := by
    change decide (0<(BitVec.ofNat 32 (le-ve)).toNat)=_
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq];omega
  rw [test];simp only [decide_eq_true_eq]

theorem flags : ∀ cl te trailing : Bool,
    taken .ne (alu .and (alu .or (if cl then 1#32 else 0#32)
      (alu .or (if trailing then 1#32 else 0#32) (if te then 1#32 else 0#32))) 1#32) (0 : Word)=decide (cl ∨ te ∨ trailing) := by decide +kernel

theorem test (cl te : Bool) (ve le : Nat) (ordered : ve≤le) (bound : le≤2048) :
    taken .ne (alu .and (alu .or (if cl then 1#32 else 0#32)
      (alu .or (alu .sltu (0 : Word) (BitVec.ofNat 32 le-BitVec.ofNat 32 ve)) (if te then 1#32 else 0#32))) 1#32) (0 : Word)=decide (cl ∨ te ∨ ve≠le) := by
  rw [trailing ve le ordered bound]
  have h := flags cl te (decide (ve≠le))
  simpa only [decide_eq_true_eq] using h
end E5R.Thermostat.HeadClFlagsMath
