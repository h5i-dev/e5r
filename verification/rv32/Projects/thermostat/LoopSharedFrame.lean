import Projects.thermostat.SharedResponseStore
import Projects.thermostat.SharedResponseFlags
import Projects.thermostat.MainWriteFlagsFrame
import Projects.thermostat.FrameOffsets
set_option autoImplicit false
namespace E5R.Thermostat.LoopSharedFrame
open E5R E5R.Thermostat
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Actual shared response stores preserve G6's capacity, route table and
    low serve words. The source-level saved scratch word at SP+20 is excluded. -/
theorem stores (ram : Word → BitVec 8) (io0 io1 io2 saved status mimeLength mime close methodMinus used : Word)
    (off n : Nat) (bound : off+n≤3312) (apart : off+n≤20 ∨ 24≤off) :
    ViewFrame.Region ram (SharedResponseStore.memory ram sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used)
      (sp+BitVec.ofNat 32 off) n := by
  intro i
  have index := i.isLt
  have address : (sp+BitVec.ofNat 32 off)+BitVec.ofNat 32 i.val=sp+BitVec.ofNat 32 (off+i.val) := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
  rw [address]
  unfold SharedResponseStore.memory
  rw [show fp+146#32=sp+3350#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3350 .b (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+145#32=sp+3349#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3349 .b (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+143#32=sp+3347#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3347 .b (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 20 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+142#32=sp+3346#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3346 .b (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+140#32=sp+3344#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3344 .h (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+136#32=sp+3340#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3340 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+132#32=sp+3336#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3336 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+128#32=sp+3332#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3332 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+124#32=sp+3328#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3328 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+112#32=sp+3316#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3316 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [show fp+108#32=sp+3312#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3312 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]

theorem write_flags (ram : Word → BitVec 8) (off n : Nat) (bound : off+n≤3312) :
    ViewFrame.Region ram (MainWriteFlags.memory ram fp) (sp+BitVec.ofNat 32 off) n := by
  intro i
  have index := i.isLt
  have address : (sp+BitVec.ofNat 32 off)+BitVec.ofNat 32 i.val=sp+BitVec.ofNat 32 (off+i.val) := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
  rw [address]
  unfold MainWriteFlags.memory
  rw [show fp+532#32=sp+3736#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3736 .b (by omega) (by decide) (by omega)]

theorem read_flags (ram : Word → BitVec 8) (off n : Nat) (bound : off+n≤3312) :
    ViewFrame.Region ram (SharedResponseFlags.memory ram fp) (sp+BitVec.ofNat 32 off) n := by
  intro i
  have index := i.isLt
  have address : (sp+BitVec.ofNat 32 off)+BitVec.ofNat 32 i.val=sp+BitVec.ofNat 32 (off+i.val) := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
  rw [address]
  unfold SharedResponseFlags.memory SharedResponseFlags.first
  rw [show fp+532#32=sp+3736#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3736 .b (by omega) (by decide) (by omega)]
  rw [show fp+576#32=sp+3780#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3780 .b (by omega) (by decide) (by omega)]
  rw [show fp+620#32=sp+3824#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3824 .b (by omega) (by decide) (by omega)]
  rw [show fp+664#32=sp+3868#32 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (off+i.val) 3868 .b (by omega) (by decide) (by omega)]
end E5R.Thermostat.LoopSharedFrame
