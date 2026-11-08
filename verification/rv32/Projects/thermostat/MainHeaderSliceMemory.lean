import Projects.thermostat.MainHeaderSliceSetup
import Projects.thermostat.StoreBytes
namespace E5R.Thermostat.MainHeaderSliceMemory
open E5R E5R.Thermostat

theorem frame (ram : Word → BitVec 8) (fp filled buf waker x : Word)
    (apart : ∀ i : Fin 13, x≠fp+BitVec.ofNat 32 (452+i.val)) :
    MainHeaderSliceSetup.memory ram fp filled buf waker x=ram x := by
  unfold MainHeaderSliceSetup.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 452+(12+j.val)=464+j.val by omega] using apart ⟨12+j.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 452+(8+j.val)=460+j.val by omega] using apart ⟨8+j.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 452+(4+j.val)=456+j.val by omega] using apart ⟨4+j.val,by omega⟩)]
  exact StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using apart ⟨j.val,by omega⟩)
end E5R.Thermostat.MainHeaderSliceMemory
