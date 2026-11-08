import Projects.thermostat.FormatValue
import Projects.thermostat.SignedMagnitude
import Projects.thermostat.ViewHalf
namespace E5R.Thermostat.FormatSource
open E5R E5R.Thermostat

inductive At (B : Board) (ram : Word → BitVec 8) : FormatValue.Value → Prop
  | signed (ptr : Word) (v : BitVec 16) (object : Memory.Block B ptr 2) (aligned : ptr.toNat%2 = 0)
      (value : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v) : At B ram (.signed ptr v)
  | boolean (ptr : Word) (v : Bool) (value : ReadBytes.Byte B img ram ptr (Encoding.boolByte v)) : At B ram (.boolean ptr v)
  | mode (ptr : Word) (v : Spec.Mode) (object : Memory.Block B ptr 8) (aligned : ptr.toNat%4 = 0)
      (pointer : ramRead ram ptr .w = ModeLiterals.pointer v)
      (length : ramRead ram (ptr+4#32) .w = BitVec.ofNat 32 (ReplyJson.mode v).length) : At B ram (.mode ptr v)

theorem frame {B before after value} (h : At B before value)
    (hf : ViewFrame.Region before after (FormatValue.pointer value) (FormatValue.size value)) : At B after value := by
  cases h with
  | signed ptr v hm ha hv =>
    change ViewFrame.Region before after ptr 2 at hf
    apply At.signed ptr v hm ha
    have hh := ViewFrame.half hf 0 (by decide)
    simp only [BitVec.add_zero] at hh
    rw [hh];exact hv
  | boolean ptr v hv =>
    change ViewFrame.Region before after ptr 1 at hf
    apply At.boolean ptr v
    apply hv.frame
    have hh := hf ⟨0,by decide⟩
    simpa only [BitVec.add_zero] using hh
  | mode ptr v hm ha hp hl =>
    change ViewFrame.Region before after ptr 8 at hf
    apply At.mode ptr v hm ha
    · have hh := ViewFrame.word hf 0 (by decide)
      simp only [BitVec.add_zero] at hh
      exact hh.trans hp
    · exact (ViewFrame.word hf 4 (by decide)).trans hl
end E5R.Thermostat.FormatSource
