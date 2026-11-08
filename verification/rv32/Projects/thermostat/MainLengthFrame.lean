import Projects.thermostat.MainLengthAppend
import Projects.thermostat.FrameOffsets
namespace E5R.Thermostat.MainLengthFrame
open E5R E5R.Thermostat
abbrev fp := 0x80fff814#32
abbrev rx := 0x80ffec14#32

def At (before after : Word → BitVec 8) (filled : Nat) : Prop :=
  ∀ x, x≠rx+BitVec.ofNat 32 filled → (∀ i : Fin 4, x≠(fp+84#32)+BitVec.ofNat 32 i.val) → x≠fp+468#32 → after x=before x

/-- A received byte and count/poll stores preserve every disjoint subregion
    of the actual future, including the copied Head and consumed/target lengths. -/
theorem region {before after filled} (frame : At before after filled) (room : filled<2048)
    (off len : Nat) (bound : off+len≤468) (apart : off+len≤84 ∨ 88≤off) :
    ViewFrame.Region before after (fp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  apply frame
  · have different := WordZero.separated rx fp 2048 469 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ ⟨off+i.val,by omega⟩
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using Ne.symm different
  · intro j
    exact FrameOffsets.ne fp off 84 i.val j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;rcases apart with h|h <;> omega)
  · have different := FrameOffsets.ne fp off 468 i.val 0 (by omega) (by decide) (by omega)
    simpa only [BitVec.add_zero] using different
end E5R.Thermostat.MainLengthFrame
