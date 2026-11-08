import Projects.thermostat.MainServeLayout
import Projects.thermostat.FrameOffsets
import Projects.thermostat.WordZero
namespace E5R.Thermostat.MainServeMemoryFrames
open E5R E5R.Thermostat
abbrev fp := MainServeLayout.fp
abbrev rx := 0x80ffec14#32

theorem whole {before after : Word → BitVec 8} {size : Nat} (frame : ViewFrame.Region before after fp size) (bound : 92≤size) : MainServeLayout.Frame before after := by
  intro off mem
  exact ViewFrame.word frame off (Nat.le_trans (MainServeLayout.bounds off mem).1 bound)

/-- Actual RX-byte/count/poll updates preserve every static serve slot and
    the request counter, whose word88 is disjoint from the filled word84. -/
theorem received {before after : Word → BitVec 8} {filled flag : Nat} (room : filled<2048) (lo : 92≤flag) (hi : flag<65536)
    (frame : ∀ x, x≠rx+BitVec.ofNat 32 filled → (∀ j : Fin 4, x≠(fp+84#32)+BitVec.ofNat 32 j.val) →
      x≠fp+BitVec.ofNat 32 flag → after x=before x) : MainServeLayout.Frame before after := by
  intro off mem
  have bounds := MainServeLayout.bounds off mem
  have region : ViewFrame.Region before after (fp+BitVec.ofNat 32 off) 4 := by
    intro i
    have index := i.isLt
    apply frame
    · have different := WordZero.separated rx fp 2048 96 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ ⟨off+i.val,by omega⟩
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using Ne.symm different
    · intro j
      exact FrameOffsets.ne fp off 84 i.val j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;rcases bounds.2 with h|h <;> omega)
    · have different := FrameOffsets.ne fp off flag i.val 0 (by omega) (by omega) (by omega)
      simpa only [BitVec.add_zero] using different
  simpa only [BitVec.add_zero] using ViewFrame.word region 0 (by decide)
end E5R.Thermostat.MainServeMemoryFrames
