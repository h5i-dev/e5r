import Projects.thermostat.RejectResponseSetup
import Projects.thermostat.SharedResponseView
import Projects.thermostat.FrameOffsets
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RejectResponseView
open E5R E5R.Thermostat

theorem descriptor (ram : Word → BitVec 8) (io : Word) (status : Nat) (hi : status≤599) :
    SharedResponseView.Descriptor (RejectResponseSetup.memory ram io (BitVec.ofNat 32 status))
      0x80fff878#32 0x80fff414#32 io 1#32 0 status [] true false := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change (_ : Word → BitVec 8) (0x80fff814#32+145#32)=0#8
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.byte _ 0x80fff814#32 (0#32) 145 146 .b (by decide) (by decide) (by decide)]
    rfl
  · change ramRead _ (0x80fff814#32+108#32) .w=_
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 108 146 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 108 145 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 108 142 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (BitVec.ofNat 32 status) 108 140 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 108 136 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 108 132 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 108 128 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (io) 108 124 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1024#32) 108 112 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · change ramRead _ (0x80fff814#32+112#32) .w=_
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 112 146 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 112 145 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 112 142 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (BitVec.ofNat 32 status) 112 140 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 112 136 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 112 132 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 112 128 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (io) 112 124 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · change ramRead _ (0x80fff814#32+124#32) .w=_
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 124 146 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 124 145 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 124 142 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (BitVec.ofNat 32 status) 124 140 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 124 136 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 124 132 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 124 128 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · change ramRead _ (0x80fff814#32+128#32) .w=_
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 128 146 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 128 145 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 128 142 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (BitVec.ofNat 32 status) 128 140 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 128 136 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 128 132 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · change ramRead _ (0x80fff814#32+132#32) .w=_
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 132 146 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 132 145 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 132 142 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (BitVec.ofNat 32 status) 132 140 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 132 136 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · change ramRead _ (0x80fff814#32+136#32) .w=_
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 136 146 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (0#32) 136 145 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (1#32) 136 142 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ 0x80fff814#32 (BitVec.ofNat 32 status) 136 140 .h (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · apply ResponseWordBytes.half
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : status<2^32)]
      omega
    · intro i
      have cases : i.val=0 ∨ i.val=1 := by have := i.isLt;omega
      rcases cases with e|e
      · change (_ : Word → BitVec 8) ((0x80fff814#32+140#32)+BitVec.ofNat 32 i.val)=_
        rw [e]
        change (_ : Word → BitVec 8) (0x80fff814#32+140#32)=_
        unfold RejectResponseSetup.memory
        rw [FrameOffsets.byte _ 0x80fff814#32 (0#32) 140 146 .b (by decide) (by decide) (by decide)]
        rw [FrameOffsets.byte _ 0x80fff814#32 (0#32) 140 145 .b (by decide) (by decide) (by decide)]
        rw [FrameOffsets.byte _ 0x80fff814#32 (1#32) 140 142 .b (by decide) (by decide) (by decide)]
        change ramPut (ramPut _ (0x80fff814#32+140#32) (byteOf (BitVec.ofNat 32 status) 0)) ((0x80fff814#32+140#32)+1#32) (byteOf (BitVec.ofNat 32 status) 1) (0x80fff814#32+140#32)=_
        rw [ramPut_ne _ (by decide)]
        rfl
      · change (_ : Word → BitVec 8) ((0x80fff814#32+140#32)+BitVec.ofNat 32 i.val)=_
        rw [e]
        change (_ : Word → BitVec 8) (0x80fff814#32+141#32)=_
        unfold RejectResponseSetup.memory
        rw [FrameOffsets.byte _ 0x80fff814#32 (0#32) 141 146 .b (by decide) (by decide) (by decide)]
        rw [FrameOffsets.byte _ 0x80fff814#32 (0#32) 141 145 .b (by decide) (by decide) (by decide)]
        rw [FrameOffsets.byte _ 0x80fff814#32 (1#32) 141 142 .b (by decide) (by decide) (by decide)]
        rfl
  · rw [Memory.load_byte]
    change BitVec.ofNat 32 ((_ : Word → BitVec 8) (0x80fff814#32+142#32)).toNat=_
    unfold RejectResponseSetup.memory
    rw [FrameOffsets.byte _ 0x80fff814#32 (0#32) 142 146 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.byte _ 0x80fff814#32 (0#32) 142 145 .b (by decide) (by decide) (by decide)]
    rfl
  · rw [Memory.load_byte]
    change BitVec.ofNat 32 ((_ : Word → BitVec 8) (0x80fff814#32+146#32)).toNat=_
    unfold RejectResponseSetup.memory
    rfl

/-- Descriptor stores preserve all caller recurrence metadata below the object. -/
theorem caller_frame (ram : Word → BitVec 8) (io status : Word) :
    ViewFrame.Region ram (RejectResponseSetup.memory ram io status) 0x80ffeb90#32 3304 := by
  intro i
  unfold RejectResponseSetup.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3350+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3350 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3349+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3349 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3346+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3346 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3344+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3344 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<2 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3340+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3340 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3336+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3336 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3332+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3332 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3328+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3328 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3316+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3316 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    change 0x80ffeb90#32+BitVec.ofNat 32 i.val≠0x80ffeb90#32+BitVec.ofNat 32 3312+BitVec.ofNat 32 j.val
    simpa only [BitVec.add_zero] using FrameOffsets.ne 0x80ffeb90#32 0 3312 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega)
      (by have := i.isLt;have := j.isLt;omega))]
end E5R.Thermostat.RejectResponseView
