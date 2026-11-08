import Theories.Logic
namespace E5R.Thermostat.FormatBits
open E5R

theorem even (p : Word) (hp : p.toNat%4 = 0) : p &&& 1#32 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change p.toNat &&& 1 = 0
  rw [show (1 : Nat) = 2^1-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_nonzero (b : BitVec 8) (hb : b.toNat ≠ 0) : taken .eq (BitVec.ofNat 32 b.toNat) (0 : Word) = false := by
  change decide (BitVec.ofNat 32 b.toNat = (0 : Word)) = false
  apply decide_eq_false
  intro h
  have hv := congrArg BitVec.toNat h
  change b.toNat%4294967296 = 0 at hv
  have hl := b.isLt
  omega
end E5R.Thermostat.FormatBits

namespace E5R.Thermostat.FormatBits
open E5R

theorem literal_nonnegative (n : Nat) (hn : n < 16) : taken .lt ((BitVec.ofNat 32 n) <<< 24) (0 : Word) = false := by
  have hf : ∀ i : Fin 16, taken .lt ((BitVec.ofNat 32 i.val) <<< 24) (0 : Word) = false := by decide +kernel
  exact hf ⟨n,hn⟩
end E5R.Thermostat.FormatBits

namespace E5R.Thermostat.FormatBits
open E5R

theorem index8 (idx : Nat) (hi : idx < 8) : (BitVec.ofNat 32 idx) <<< 3 = BitVec.ofNat 32 (8*idx) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega
end E5R.Thermostat.FormatBits
