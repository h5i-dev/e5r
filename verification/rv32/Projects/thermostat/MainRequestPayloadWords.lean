import Projects.thermostat.MainServeNextPayloadWords
import Projects.thermostat.MainRequestCounterMemory
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestPayloadWords
open E5R E5R.Thermostat

theorem counter (ram : Word → BitVec 8) (sp count used : Word) (h : MainServeNextPayloadWords.At ram sp) :
    MainServeNextPayloadWords.At (MainRequestCounter.memory ram sp count used) sp := by
  have region := MainRequestCounterMemory.frame ram sp count used 4512 6 (by decide) (Or.inr (by decide))
  refine ⟨?_,?_⟩
  · have word := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at word
    exact word.trans h.1
  · have half := MainHalfMemory.frame region 4 (by decide)
    simp only [BitVec.add_assoc,show 4512#32+4#32=4516#32 by decide +kernel] at half
    rw [half]
    exact h.2
/-- Readback of the high payload's first actual stored word after acquisition. -/
theorem counter_word (ram : Word → BitVec 8) (sp count used : Word) (h : MainServeNextPayloadWords.At ram sp) :
    ramRead (MainRequestCounter.memory ram sp count used) (sp+4512#32) .w=0#32 :=
  (counter ram sp count used h).1

end E5R.Thermostat.MainRequestPayloadWords
