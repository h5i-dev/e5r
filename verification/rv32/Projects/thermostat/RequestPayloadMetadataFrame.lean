import Projects.thermostat.RequestPayloadMetadata
import Projects.thermostat.MainRequestStoreFrames
namespace E5R.Thermostat.RequestPayloadMetadataFrame
open E5R E5R.Thermostat
theorem metadata (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) (off size : Nat) (bound : off+size≤5232)
    (apart0 : off+size≤3312 ∨ 3344≤off)
    (apart1 : off+size≤3616 ∨ 3632≤off)
    : ViewFrame.Region ram (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold RequestPayloadMetadata.memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3340 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3336 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3332 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3328 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 3320 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3316 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3312 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 3326 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 3324 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 3322 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3628 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3624 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3620 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3616 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]

end E5R.Thermostat.RequestPayloadMetadataFrame
