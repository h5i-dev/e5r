import Projects.thermostat.ResponseHeadSpec
import Theories.Logic
namespace E5R.Thermostat.HttpStatusMath
open E5R E5R.Thermostat

theorem unsigned (n : Nat) (hn : n≤599) : (BitVec.ofNat 32 n).toNat=n := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem signed (n : Nat) (hn : n≤599) : (BitVec.ofNat 32 n).toInt=Int.ofNat n := by
  rw [BitVec.toInt_eq_toNat_cond,unsigned n hn]
  rw [if_pos (show 2*n<2^32 by omega)]
  rfl

theorem signed_lt (a b : Nat) (ha : a≤599) (hb : b≤599) :
    taken .lt (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (a<b) := by
  change decide ((BitVec.ofNat 32 a).toInt<(BitVec.ofNat 32 b).toInt)=_
  rw [signed a ha,signed b hb]
  simp

theorem signed_ge (a b : Nat) (ha : a≤599) (hb : b≤599) :
    taken .ge (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (b≤a) := by
  change (!taken .lt (BitVec.ofNat 32 a) (BitVec.ofNat 32 b))=_
  rw [signed_lt a b ha hb]
  simp only [←decide_not,Nat.not_lt]
theorem unequal (a b : Nat) (ha : a≤599) (hb : b≤599) (hne : a≠b) :
    taken .eq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=false := by
  have hw : (BitVec.ofNat 32 a)≠(BitVec.ofNat 32 b) := by
    intro he
    have hh := congrArg BitVec.toNat he
    rw [unsigned a ha,unsigned b hb] at hh
    exact hne hh
  change (BitVec.ofNat 32 a == BitVec.ofNat 32 b)=false
  exact Bool.eq_false_iff.mpr (fun he => hw (beq_iff_eq.mp he))

theorem not_equal (a b : Nat) (ha : a≤599) (hb : b≤599) (hne : a≠b) :
    taken .ne (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=true := by
  change (!taken .eq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b))=true
  rw [unequal a b ha hb hne]
  rfl
end E5R.Thermostat.HttpStatusMath
