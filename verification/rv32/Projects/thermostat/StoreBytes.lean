import Projects.thermostat.Bytes
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StoreBytes
open E5R E5R.Thermostat

theorem frame (ram : Word → BitVec 8) (a v x : Word) (w : Width)
    (hx : ∀ i : Fin w.bytes, x ≠ a+BitVec.ofNat 32 i.val) : ramWrite ram a v w x = ram x := by
  cases w with
  | b =>
    have h0 : x ≠ a := by simpa only [BitVec.add_zero] using hx ⟨0,by decide⟩
    exact ramPut_ne _ h0
  | h =>
    have h0 : x ≠ a := by simpa only [BitVec.add_zero] using hx ⟨0,by decide⟩
    have h1 : x ≠ a+1#32 := hx ⟨1,by decide⟩
    change ramPut (ramPut ram a (byteOf v 0)) (a+1#32) (byteOf v 1) x = _
    rw [ramPut_ne _ h1,ramPut_ne _ h0]
  | w => exact ramWrite_w_other ram a v x (fun i hi => hx ⟨i,hi⟩)
end E5R.Thermostat.StoreBytes
