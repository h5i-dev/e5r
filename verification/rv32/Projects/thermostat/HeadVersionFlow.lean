import Projects.thermostat.HttpRequestSpec
import Theories.Logic
namespace E5R.Thermostat.HeadVersionFlow
open E5R E5R.Thermostat HttpRequestSpec

def badDigit (b : BitVec 8) : Bool := taken .ltu (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffc6#32) 0xfffffff6#32

theorem digit_test : ∀ b : BitVec 8, badDigit b=decide (b.toNat<48 ∨ 57<b.toNat) := by decide +kernel

theorem dot_test : ∀ b : BitVec 8, taken .ne (BitVec.ofNat 32 b.toNat) 46#32=decide (b.toNat≠46) := by decide +kernel

theorem major_test : ∀ b : BitVec 8, taken .ne (BitVec.ofNat 32 b.toNat) 49#32=decide (b.toNat≠49) := by decide +kernel

theorem one_test : ∀ b : BitVec 8, taken .eq (BitVec.ofNat 32 b.toNat) 49#32=decide (b.toNat=49) := by decide +kernel

theorem zero_test : ∀ b : BitVec 8, taken .ne (BitVec.ofNat 32 b.toNat) 48#32=decide (b.toNat≠48) := by decide +kernel

def flow (major dot minor : BitVec 8) : Nat :=
  if badDigit major then 3
  else if taken .ne (BitVec.ofNat 32 dot.toNat) 46#32 then 3
  else if badDigit minor then 3
  else if taken .ne (BitVec.ofNat 32 major.toNat) 49#32 then 2
  else if taken .eq (BitVec.ofNat 32 minor.toNat) 49#32 then 1
  else if taken .ne (BitVec.ofNat 32 minor.toNat) 48#32 then 2
  else 0

/-- Factor the three-byte check into five separate 256-byte kernel checks
    and ordinary arithmetic; no exhaustive three-byte native evaluation. -/
theorem classification (major dot minor : BitVec 8) : flow major dot minor=versionDigits major.toNat dot.toNat minor.toNat := by
  simp only [flow,digit_test,dot_test,major_test,one_test,zero_test,decide_eq_true_eq]
  unfold versionDigits
  repeat' first | split | omega
end E5R.Thermostat.HeadVersionFlow
