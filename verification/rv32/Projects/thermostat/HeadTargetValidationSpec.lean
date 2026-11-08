import Projects.thermostat.HeadTargetValidate
import Projects.thermostat.HeadTargetMath
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadTargetValidationSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem word_eq (a b : Nat) (ha : a≤2048) (hb : b≤2048) :
    BitVec.ofNat 32 a=BitVec.ofNat 32 b ↔ a=b := by
  constructor
  · intro eq
    have nat := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^32),Nat.mod_eq_of_lt (by omega : b<2^32)] using nat
  · intro eq;rw [eq]

theorem pc (offset index last remaining : Nat) (stopByte firstByte : BitVec 8)
    (ho : offset≤2048) (hi : index≤2048) (hj : last≤2048) (hr : remaining≤2048) :
    HeadTargetValidate.pc (BitVec.ofNat 32 offset) (BitVec.ofNat 32 index) (BitVec.ofNat 32 last)
      (BitVec.ofNat 32 stopByte.toNat) firstByte (BitVec.ofNat 32 remaining)=
    if offset≠0 ∧ index<last ∧ stopByte.toNat=32 ∧ firstByte.toNat=47 ∧ remaining=9
    then 0x80002e20#32 else 0x80002efc#32 := by
  have hs : stopByte.toNat≤2048 := by have := stopByte.isLt;omega
  have hf : firstByte.toNat≤2048 := by have := firstByte.isLt;omega
  have hoEq : (BitVec.ofNat 32 offset=(0 : Word)) ↔ offset=0 := word_eq offset 0 ho (by decide)
  have hsEq : (BitVec.ofNat 32 stopByte.toNat=32#32) ↔ stopByte.toNat=32 := word_eq stopByte.toNat 32 hs (by decide)
  have hfEq : (BitVec.ofNat 32 firstByte.toNat=47#32) ↔ firstByte.toNat=47 := word_eq firstByte.toNat 47 hf (by decide)
  have hrEq : (BitVec.ofNat 32 remaining=9#32) ↔ remaining=9 := word_eq remaining 9 hr (by decide)
  simp only [HeadTargetValidate.pc,taken,beq_iff_eq,bne_iff_ne,ne_eq,hoEq,hsEq,hfEq,hrEq,
    BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : index<2^32),Nat.mod_eq_of_lt (by omega : last<2^32)]
  by_cases a : offset=0 <;> by_cases b : index<last <;> by_cases c : stopByte.toNat=32 <;>
    by_cases d : firstByte.toNat=47 <;> by_cases e : remaining=9 <;> simp [a,b,c,d,e]

def Good (g : Nat → Nat) (m te j : Nat) : Prop :=
  m+1<te ∧ te<j ∧ g te=32 ∧ g (m+1)=47 ∧ j-te=9

instance (g : Nat → Nat) (m te j : Nat) : Decidable (Good g m te j) := by unfold Good;infer_instance

theorem good_iff (g : Nat → Nat) (m te j : Nat) (hm : m+1≤te) :
    Good g m te j ↔ (te-m-1≠0 ∧ te<j ∧ g te=32 ∧ g (m+1)=47 ∧ j-te=9) := by
  unfold Good
  omega
end E5R.Thermostat.HeadTargetValidationSpec
