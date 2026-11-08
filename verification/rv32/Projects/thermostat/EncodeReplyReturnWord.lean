import Projects.thermostat.EncodeReplyMemory
namespace E5R.Thermostat.EncodeReplyMemory
open E5R E5R.Thermostat

theorem return_word (ram : Word → BitVec 8) (p reply dst : Word) (cap : Nat) (c : Core) (s : Spec.Snapshot) :
    ramRead (memory ram p reply dst cap c s) ((p+224#32)+92#32) .w = c.get 1 := by
  let q := p+224#32
  let initial := EncodeReplyStart.memory ram q dst (BitVec.ofNat 32 cap) c
  have hreg : ViewFrame.Region initial (memory ram p reply dst cap c s) (q+92#32) 4 := by
    intro i
    exact EncodeReplyConstruct.frame initial q reply (ModeLiterals.pointer s.mode) (BitVec.ofNat 32 (ReplyJson.mode s.mode).length) _
      (FormatSpace.offsets_disjoint q 92 4 20 72 (by decide) (by decide) (by decide) i)
  have hh := ViewFrame.word hreg 0 (by decide)
  simp only [BitVec.add_zero] at hh
  exact hh.trans (EncodeReplyStart.words ram q dst (BitVec.ofNat 32 cap) c).1
end E5R.Thermostat.EncodeReplyMemory
