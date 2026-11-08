import Projects.thermostat.Arithmetic
import Projects.thermostat.HttpDecMath
import Projects.thermostat.DigitSmallMath
namespace E5R.Thermostat.ResponseHeadMath
open E5R E5R.Thermostat

def folded (status : Nat) : Word := ((BitVec.ofNat 32 status+0xfffffda8#32) <<< 16) >>> 16

theorem folded_nat (status : Nat) : (folded status).toNat=(status+64936)%65536 := by
  unfold folded
  rw [Arithmetic.trunc16,BitVec.toNat_add,
    show (0xfffffda8#32).toNat=4294966696 by decide +kernel,BitVec.toNat_ofNat]
  have hd : 65536∣4294967296 := ⟨65536,by decide +kernel⟩
  rw [Nat.mod_mod_of_dvd _ hd,Nat.add_mod,Nat.mod_mod_of_dvd _ hd]
  rw [show 4294966696%65536=64936 by decide +kernel]
  symm
  rw [Nat.add_mod,show 64936%65536=64936 by decide +kernel]

theorem folded_value (status : Nat) (hs : status<65536) :
    folded status=BitVec.ofNat 32 ((status+64936)%65536) := by
  apply BitVec.eq_of_toNat_eq
  rw [folded_nat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide : 0<65536)) (by decide : 65536<4294967296))]

theorem range_guard (status : Nat) (hs : status<65536) :
    taken .geu (folded status) 65036#32=decide (100≤status ∧ status≤599) := by
  rw [folded_value status hs]
  change (!decide (((BitVec.ofNat 32 ((status+64936)%65536)).toNat)<65036))=_
  have hr : (status+64936)%65536<4294967296 := by have h := Nat.mod_lt (status+64936) (by decide : 0<65536);omega
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hr,←decide_not]
  have he : ¬(status+64936)%65536<65036 ↔ 100≤status ∧ status≤599 := by omega
  simp only [he]

theorem quotient100 (status : Nat) (hs : status≤599) :
    (((BitVec.ofNat 32 status) >>> 2)*5243#32) >>> 17=BitVec.ofNat 32 (status/100) := by
  rw [HttpDecMath.shift status 2 (by omega)]
  exact DigitSmallMath.reciprocal100 status (by omega)

theorem quotient10 (status : Nat) (hs : status≤599) :
    ((BitVec.ofNat 32 status)*52429#32) >>> 19=BitVec.ofNat 32 (status/10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  change ((status%4294967296*52429)%4294967296)/524288=(status/10)%4294967296
  rw [Nat.mod_eq_of_lt (show status<4294967296 by omega),Nat.mod_eq_of_lt (show status*52429<4294967296 by omega),Nat.mod_eq_of_lt (show status/10<4294967296 by omega)]
  omega

theorem tens_quotient (status : Nat) (hs : status≤599) :
    ((BitVec.ofNat 32 (status/10))*6554#32) >>> 16=BitVec.ofNat 32 (status/100) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  change (((status/10)%4294967296*6554)%4294967296)/65536=(status/100)%4294967296
  rw [Nat.mod_eq_of_lt (show status/10<4294967296 by omega),Nat.mod_eq_of_lt (show status/10*6554<4294967296 by omega),Nat.mod_eq_of_lt (show status/100<4294967296 by omega)]
  omega

def ones (status : Nat) : Word := BitVec.ofNat 32 status-
  ((BitVec.ofNat 32 (status/10) <<< 1)+(BitVec.ofNat 32 (status/10) <<< 3))

theorem ones_value (status : Nat) (hs : status≤599) : ones status=BitVec.ofNat 32 (status%10) := by
  have h : ∀ n : Fin 600, ones n.val=BitVec.ofNat 32 (n.val%10) := by decide +kernel
  exact h ⟨status,by omega⟩
end E5R.Thermostat.ResponseHeadMath
