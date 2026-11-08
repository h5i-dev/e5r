import Projects.thermostat.MainRequestPayloadWords
import Projects.thermostat.MainRamHalves
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestPayloadHalves
open E5R E5R.Thermostat

theorem contract (ram : Word → BitVec 8) (sp : Word) (h : MainServeNextPayloadWords.At ram sp) :
    extend .h true (ramRead ram (sp+4512#32) .h)=0#32 ∧
      extend .h true (ramRead ram (sp+4514#32) .h)=0#32 ∧
      extend .h true (ramRead ram (sp+4516#32) .h)=0#32 := by
  refine ⟨MainRamHalves.zero_low ram _ h.1 true,?_,h.2⟩
  simpa only [BitVec.add_assoc,show 4512#32+2#32=4514#32 by decide +kernel] using MainRamHalves.high ram (sp+4512#32) 0#32 h.1 (by decide) true
end E5R.Thermostat.MainRequestPayloadHalves
