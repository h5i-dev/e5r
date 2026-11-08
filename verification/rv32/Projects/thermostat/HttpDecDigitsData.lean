import Projects.thermostat.HttpDecBigTens
import Projects.thermostat.HttpDecTensStore
import Projects.thermostat.HttpDecOnesData
import Projects.thermostat.HttpDecDigitsSpec
import Projects.thermostat.ByteWrite
namespace E5R.Thermostat.HttpDecDigitsData
open E5R E5R.Thermostat

theorem byte_nat (n : Nat) : byteOf (BitVec.ofNat 32 n) 0=BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,Nat.pow_zero,Nat.div_one]
  omega

theorem hundreds (ram : Word → BitVec 8) (sp : Word) (n : Nat) :
    HttpDecBigTens.memory ram sp n=ramPut ram (sp+4#32) (DecimalDigits.digit (n/100)) := by
  unfold HttpDecBigTens.memory
  change ramPut ram _ (byteOf (BitVec.ofNat 32 (48+n/100)) 0)=_
  rw [byte_nat]
  rfl

theorem tens (ram : Word → BitVec 8) (sp : Word) (n index : Nat) :
    HttpDecTensStore.memory ram sp n index=ramPut ram (sp+BitVec.ofNat 32 (4+index)) (DecimalDigits.digit ((n/10)%10)) := by
  unfold HttpDecTensStore.memory
  change ramPut ram _ (byteOf (BitVec.ofNat 32 (48+(n/10)%10)) 0)=_
  rw [byte_nat]
  rfl

theorem one (ram : Word → BitVec 8) (sp : Word) (n : Nat) (hn : n<10) :
    HttpDecOnes.memory ram sp n 0=ByteWrite.write ram (sp+4#32) (ReplyJson.decimal n) := by
  rw [HttpDecOnesData.memory_eq ram sp n 0 (by omega),HttpDecDigitsSpec.cases n (by omega),if_pos hn]
  rfl

theorem two (ram : Word → BitVec 8) (sp : Word) (n : Nat) (hlo : 10≤n) (hhi : n<100) :
    HttpDecOnes.memory (HttpDecTensStore.memory ram sp n 0) sp n 1=
      ByteWrite.write ram (sp+4#32) (ReplyJson.decimal n) := by
  rw [HttpDecOnesData.memory_eq _ sp n 1 (by omega),tens,HttpDecDigitsSpec.cases n (by omega),if_neg (show ¬n<10 by omega),if_pos hhi]
  simp only [ByteWrite.write,BitVec.add_assoc]
  rfl

theorem three (ram : Word → BitVec 8) (sp : Word) (n : Nat) (hlo : 100≤n) (hhi : n≤832) :
    HttpDecOnes.memory (HttpDecTensStore.memory (HttpDecBigTens.memory ram sp n) sp n 1) sp n 2=
      ByteWrite.write ram (sp+4#32) (ReplyJson.decimal n) := by
  rw [HttpDecOnesData.memory_eq _ sp n 2 hhi,tens,hundreds,HttpDecDigitsSpec.cases n hhi,if_neg (show ¬n<10 by omega),if_neg (show ¬n<100 by omega)]
  simp only [ByteWrite.write,BitVec.add_assoc]
  rfl
end E5R.Thermostat.HttpDecDigitsData
