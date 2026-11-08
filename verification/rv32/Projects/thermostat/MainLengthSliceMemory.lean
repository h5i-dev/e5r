import Projects.thermostat.MainLengthSliceSetup
import Projects.thermostat.StoreBytes
namespace E5R.Thermostat.MainLengthSliceMemory
open E5R E5R.Thermostat

theorem frame (ram : Word → BitVec 8) (fp filled buf waker x : Word)
    (apart : ∀ i : Fin 13, x≠fp+BitVec.ofNat 32 (456+i.val)) :
    MainLengthSliceSetup.memory ram fp filled buf waker x=ram x := by
  unfold MainLengthSliceSetup.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 456+(12+j.val)=468+j.val by omega] using apart ⟨12+j.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 456+(8+j.val)=464+j.val by omega] using apart ⟨8+j.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 456+(4+j.val)=460+j.val by omega] using apart ⟨4+j.val,by omega⟩)]
  exact StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using apart ⟨j.val,by omega⟩)
end E5R.Thermostat.MainLengthSliceMemory
