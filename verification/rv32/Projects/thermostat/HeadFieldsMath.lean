import Projects.thermostat.HeadVersionMath
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadFieldsMath
open E5R E5R.Thermostat

theorem relative (i t length : Nat) :
    (BitVec.ofNat 32 i-BitVec.ofNat 32 length)+BitVec.ofNat 32 t=
      BitVec.ofNat 32 (i+t)-BitVec.ofNat 32 length := by
  rw [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.add_comm (-BitVec.ofNat 32 length) (BitVec.ofNat 32 t),
    ←BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.sub_eq_add_neg]

theorem guard (i t length : Nat) (hi : i+t<length) (hlen : length≤2048) :
    taken .eq ((BitVec.ofNat 32 i-BitVec.ofNat 32 length)+BitVec.ofNat 32 t) (0 : Word)=false := by
  rw [relative]
  have ne : BitVec.ofNat 32 (i+t)-BitVec.ofNat 32 length≠(0 : Word) := by
    intro eq
    have nat := congrArg BitVec.toNat eq
    rw [HeadVersionMath.offset_nat (i+t) length hi hlen] at nat
    change 2^32-length+(i+t)=0 at nat
    omega
  simpa [taken] using ne

theorem pointer (buf : Word) (i t : Nat) :
    (buf+BitVec.ofNat 32 t)+BitVec.ofNat 32 i=buf+BitVec.ofNat 32 (i+t) := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_comm t i]

theorem index_next (i t : Nat) :
    BitVec.ofNat 32 (i+t)+1#32=BitVec.ofNat 32 (i+(t+1)) := by
  rw [←BitVec.ofNat_add,Nat.add_assoc]

theorem count_next (t : Nat) : BitVec.ofNat 32 t+1#32=BitVec.ofNat 32 (t+1) := (BitVec.ofNat_add t 1).symm

theorem inverse_next (t : Nat) :
    (BitVec.ofNat 32 t+0xffffffff#32)+1#32=BitVec.ofNat 32 (t+1)+0xffffffff#32 := by
  rw [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_assoc,
    show 0xffffffff#32+1#32=0#32 by decide +kernel,show 1#32+0xffffffff#32=0#32 by decide +kernel]

theorem pointer_next (buf : Word) (t : Nat) :
    (buf+BitVec.ofNat 32 t)+1#32=buf+BitVec.ofNat 32 (t+1) := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add]

theorem next_test (i t cap : Nat) (hi : i+t<cap) (hn : cap≤2048) :
    taken .ltu (BitVec.ofNat 32 (i+(t+1))) (BitVec.ofNat 32 cap)=decide (i+(t+1)<cap) := by
  simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i+(t+1)<2^32),Nat.mod_eq_of_lt (by omega : cap<2^32)]
end E5R.Thermostat.HeadFieldsMath
