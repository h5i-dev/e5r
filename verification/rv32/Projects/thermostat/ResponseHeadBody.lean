import Projects.thermostat.ResponseHeadBodyCompute
import Projects.thermostat.ResponseHeadBodyYes
import Projects.thermostat.ResponseHeadBodyNo
import Projects.thermostat.ResponseHeadSources
namespace E5R.Thermostat.ResponseHeadBody
open E5R E5R.Thermostat

def Frame (c d : Core) := ∀ r : Reg, r≠17 → r≠5 → r≠6 → r≠25 → r≠9 → r≠19 → d.get r=c.get r

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (status : Nat) (hs : status≤599)
    (h12 : c.get 12=BitVec.ofNat 32 status) (h9 : c.get 9=1#32) (h11 : c.get 11=192#32)
    (hp : c.pc=0x80003ee2#32) :
    ∃ d n, n≤15 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003f26#32 ∧
      d.get 9=ResponseHeadSources.clName status ∧ d.get 19=ResponseHeadSources.clEnd status ∧
      d.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) ∧ d.get 17=9#32 ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a17,a5,a6,a25,fa,ka⟩ := ResponseHeadBodyCompute.contract B c ram status hs h12 hp
  have a11 := (fa 11 (by decide) (by decide) (by decide) (by decide)).trans h11
  cases hh : ResponseHeadSpec.hasBody status with
  | false =>
    obtain ⟨d,td,pd,d19,d17,fd,kd⟩ := ResponseHeadBodyNo.contract B a ram (by simpa [hh,ResponseHeadBodyMath.boolWord] using a25) a11 pa
    refine ⟨d,8+4,by decide,ta.trans td,pd,?_,?_,?_,d17,?_,kd.trans ka⟩
    · simpa [ResponseHeadSources.clName,hh] using (fd 9 (by decide) (by decide)).trans ((fa 9 (by decide) (by decide) (by decide) (by decide)).trans h9)
    · simpa [ResponseHeadSources.clEnd,hh,ResponseHeadLiterals.pointer] using d19
    · simpa only [hh] using (fd 25 (by decide) (by decide)).trans a25
    · intro r h17 h5 h6 h25 h9 h19
      exact (fd r h19 h17).trans (fa r h17 h5 h6 h25)
  | true =>
    obtain ⟨d,td,pd,d9,d19,d17,fd,kd⟩ := ResponseHeadBodyYes.contract B a ram (by simpa [hh,ResponseHeadBodyMath.boolWord] using a25) a11 pa
    refine ⟨d,8+7,by decide,ta.trans td,pd,?_,?_,?_,d17,?_,kd.trans ka⟩
    · simpa [ResponseHeadSources.clName,hh,ResponseHeadLiterals.pointer] using d9
    · simpa [ResponseHeadSources.clEnd,hh,ResponseHeadLiterals.pointer] using d19
    · simpa only [hh] using (fd 25 (by decide) (by decide) (by decide)).trans a25
    · intro r h17 h5 h6 h25 h9 h19
      exact (fd r h9 h19 h17).trans (fa r h17 h5 h6 h25)
end E5R.Thermostat.ResponseHeadBody
