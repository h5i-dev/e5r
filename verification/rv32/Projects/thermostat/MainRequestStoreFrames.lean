import Projects.thermostat.MainRequestBodyStores
import Projects.thermostat.MainRequestMetadataStores
import Projects.thermostat.MainRequestPaddingStores
import Projects.thermostat.MainRequestMinorRawStores
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestStoreFrames
open E5R E5R.Thermostat

theorem body (ram : Word → BitVec 8) (sp bodyPtr bodyLen method : Word) (off size : Nat) (bound : off+size≤5232)
    (apart0 : off+size≤3632 ∨ 3640≤off)
    (apart1 : off+size≤3684 ∨ 3685≤off)
    : ViewFrame.Region ram (MainRequestBodyStores.memory ram sp bodyPtr bodyLen method) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold MainRequestBodyStores.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3684 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3636 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3632 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]

theorem metadata (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) (off size : Nat) (bound : off+size≤5232)
    (apart0 : off+size≤3312 ∨ 3344≤off)
    (apart1 : off+size≤3616 ∨ 3632≤off)
    : ViewFrame.Region ram (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold MainRequestMetadataStores.memory
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

theorem padding (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) (off size : Nat) (bound : off+size≤5232)
    (apart0 : off+size≤3609 ∨ 3616≤off)
    : ViewFrame.Region ram (MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold MainRequestPaddingStores.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3615 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3614 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3613 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3612 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3611 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3610 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3609 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]

theorem minor (ram : Word → BitVec 8) (sp minor rx used : Word) (off size : Nat) (bound : off+size≤5232)
    (apart0 : off+size≤3608 ∨ 3609≤off)
    (apart1 : off+size≤3640 ∨ 3648≤off)
    : ViewFrame.Region ram (MainRequestMinorRawStores.memory ram sp minor rx used) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold MainRequestMinorRawStores.memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3644 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3640 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3608 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
end E5R.Thermostat.MainRequestStoreFrames
