import Projects.thermostat.HttpRequestSpec
import Theories.Logic
namespace E5R.Thermostat.HeadMethodSpaceFlow
open E5R E5R.Thermostat

def byteDiff (b : BitVec 8) : Word := alu .add (BitVec.ofNat 32 b.toNat) 0xffffffe0#32
def byteFlag (b : BitVec 8) : Word := alu .sltu (0 : Word) (byteDiff b)

def flags (m j : Word) (b : BitVec 8) : Word :=
  alu .or (alu .or (alu .sltu m 1#32) (alu .xor (alu .sltu m j) 1#32)) (byteFlag b)

theorem byte_flag : ∀ b : BitVec 8, byteFlag b=(if b.toNat=32 then 0#32 else 1#32) := by decide +kernel

theorem index_flag (m : Nat) (hm : m≤2048) :
    alu .sltu (BitVec.ofNat 32 m) 1#32=(if m=0 then 1#32 else 0#32) := by
  by_cases zero : m=0
  · subst m;decide +kernel
  · have lt : ¬m<1 := by omega
    simp [alu,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : m<2^32),zero,lt]

theorem inside_flag (m j : Nat) (hm : m<j) (hj : j≤2048) :
    alu .sltu (BitVec.ofNat 32 m) (BitVec.ofNat 32 j)=1#32 := by
  simp only [alu,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : m<2^32),
    Nat.mod_eq_of_lt (by omega : j<2^32),hm,decide_true,ite_true]
  decide +kernel

theorem bad_test (m j : Nat) (b : BitVec 8) (hm : m<j) (hj : j≤2048) :
    taken .ne (flags (BitVec.ofNat 32 m) (BitVec.ofNat 32 j) b) (0 : Word)=decide (m=0 ∨ b.toNat≠32) := by
  unfold flags
  rw [index_flag m (by omega),inside_flag m j hm hj,byte_flag]
  by_cases zero : m=0 <;> by_cases space : b.toNat=32 <;> simp [zero,space,alu,taken]
end E5R.Thermostat.HeadMethodSpaceFlow
