import Projects.thermostat.HttpDecOnes
import Projects.thermostat.StoreBytes
namespace E5R.Thermostat.HttpDecOnesData
open E5R E5R.Thermostat

theorem memory_eq (ram : Word → BitVec 8) (sp : Word) (n count : Nat) (hn : n≤832) :
    HttpDecOnes.memory ram sp n count=ramPut ram (sp+BitVec.ofNat 32 (4+count)) (DecimalDigits.digit (n%10)) := by
  unfold HttpDecOnes.memory
  change ramPut ram _ (byteOf (HttpDecOnesMath.byteWord n) 0)=_
  rw [HttpDecOnesMath.value n hn]

theorem frame (ram : Word → BitVec 8) (sp x : Word) (n count : Nat)
    (hx : x≠sp+BitVec.ofNat 32 (4+count)) : HttpDecOnes.memory ram sp n count x=ram x := by
  apply StoreBytes.frame
  intro i
  have hi : i.val=0 := by have hh := i.isLt;change i.val<1 at hh;omega
  simpa only [hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero] using hx
end E5R.Thermostat.HttpDecOnesData
