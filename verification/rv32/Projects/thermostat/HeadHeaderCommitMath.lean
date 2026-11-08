import Projects.thermostat.HeaderSetup
import Projects.thermostat.HeadFieldsView
namespace E5R.Thermostat.HeadHeaderCommitMath
open E5R E5R.Thermostat

def slot (sp : Word) (n : Nat) : Word := (sp+56#32)+BitVec.ofNat 32 (16*n)

theorem shift (n : Nat) (hn : n≤16) : alu .sll (BitVec.ofNat 32 n) 4#32=BitVec.ofNat 32 (16*n) := by
  change BitVec.ofNat 32 n <<< 4=BitVec.ofNat 32 (16*n)
  exact HeaderSetup.shift_count n hn

theorem offset (sp : Word) (n k : Nat) : slot sp n+BitVec.ofNat 32 k=sp+BitVec.ofNat 32 (56+16*n+k) := by
  simp only [slot,BitVec.ofNat_add,BitVec.add_assoc]

theorem address (sp : Word) (n : Nat) : slot sp n=sp+BitVec.ofNat 32 (56+16*n) := by
  simpa only [Nat.add_zero,BitVec.add_zero] using offset sp n 0

theorem aligned (sp : Word) (n : Nat) (ha : sp.toNat%4=0) : (slot sp n).toNat%4=0 := by
  rw [address,show 56+16*n=4*(14+4*n) by omega]
  exact Memory.word_aligned sp (14+4*n) ha

theorem block (B : Board) (sp : Word) (n : Nat) (hn : n<16) (hm : Memory.Block B sp 5312) : Memory.Block B (slot sp n) 16 := by
  rw [address]
  exact Memory.sub_block hm (off := 56+16*n) (by decide) (by omega)

theorem line_sum (start le : Nat) (hl : start≤le) :
    BitVec.ofNat 32 (le-start)+BitVec.ofNat 32 start=BitVec.ofNat 32 le := by
  rw [←BitVec.ofNat_add,Nat.sub_add_cancel hl]

theorem next (le : Nat) : BitVec.ofNat 32 le+2#32=BitVec.ofNat 32 (le+2) := (BitVec.ofNat_add le 2).symm

theorem test (le cap : Nat) (hl : le≤2048) (hc : cap≤2048) :
    taken .ltu (BitVec.ofNat 32 (le+2)) (BitVec.ofNat 32 cap)=decide (le+2<cap) := by
  simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : le+2<2^32),Nat.mod_eq_of_lt (by omega : cap<2^32)]

theorem te_guard : ∀ te : Bool,
    taken .eq (BitVec.ofNat 32 (HeadFieldsView.flag te).toNat) 2#32=false := by decide +kernel
theorem te_word : ∀ te : Bool,
    BitVec.ofNat 32 (HeadFieldsView.flag te).toNat=(if te then 1#32 else 0#32) := by decide +kernel
end E5R.Thermostat.HeadHeaderCommitMath
