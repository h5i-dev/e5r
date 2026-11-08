import Projects.thermostat.HeadFieldsView
import Projects.thermostat.Usize
namespace E5R.Thermostat.HeadTeRuleMath
open E5R E5R.Thermostat

theorem flag_word : ∀ b : Bool,
    BitVec.ofNat 32 (HeadFieldsView.flag b).toNat=(if b then 1#32 else 0#32) := by decide +kernel

theorem flag_test : ∀ b : Bool,
    taken .ne (alu .and (if b then 1#32 else 0#32) 1#32) (0 : Word)=b := by decide +kernel

theorem version_test (minor : Nat) (te : Bool) (hm : minor≤1) :
    taken .ne (alu .and (alu .or (BitVec.ofNat 32 (1-minor)) (if te then 1#32 else 0#32)) 1#32) (0 : Word)=decide (minor=0 ∨ te) := by
  by_cases zero : minor=0
  · subst minor;cases te <;> decide +kernel
  · have one : minor=1 := by omega
    subst minor;cases te <;> decide +kernel

theorem trailing_test (ve le : Nat) (h : ve≤le) (bound : le≤2048) :
    taken .ne (BitVec.ofNat 32 le-BitVec.ofNat 32 ve) (0 : Word)=decide (ve≠le) := by
  rw [BitVec.ofNat_sub_ofNat_of_le le ve (by omega) h]
  change taken .ne (BitVec.ofNat 32 (le-ve)) (BitVec.ofNat 32 0)=_
  rw [Usize.ne _ _ (by omega) (by decide)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem span_word (s v e : Word) : (s-v)+(e-s)=e-v := by
  rw [BitVec.sub_eq_add_neg s v,BitVec.add_comm s (-v),BitVec.add_assoc,
    BitVec.add_comm s (e-s),BitVec.sub_add_cancel,BitVec.add_comm,←BitVec.sub_eq_add_neg]

theorem span (ns vs le : Nat) (hns : ns≤le) (hvs : vs≤le) (bound : le≤2048) :
    (BitVec.ofNat 32 ns-BitVec.ofNat 32 vs)+BitVec.ofNat 32 (le-ns)=BitVec.ofNat 32 (le-vs) := by
  rw [←BitVec.ofNat_sub_ofNat_of_le le ns (by omega) hns,span_word,
    BitVec.ofNat_sub_ofNat_of_le le vs (by omega) hvs]

theorem width_test (n : Nat) (bound : n≤2048) :
    taken .ne (BitVec.ofNat 32 n+0xfffffff9#32) (0 : Word)=decide (n≠7) := by
  have negative : 0xfffffff9#32= -(7#32) := by decide +kernel
  rw [negative,←BitVec.sub_eq_add_neg]
  change decide (BitVec.ofNat 32 n-7#32≠0#32)=_
  have eq : BitVec.ofNat 32 n-7#32=0#32 ↔ n=7 := by
    rw [BitVec.sub_eq_iff_eq_add]
    simp only [BitVec.zero_add]
    exact Usize.ofNat_eq n 7 (by omega) (by decide)
  simp only [ne_eq,eq]
end E5R.Thermostat.HeadTeRuleMath
