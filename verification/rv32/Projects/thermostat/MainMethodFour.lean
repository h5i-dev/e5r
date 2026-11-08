import Projects.thermostat.MainMethodTests
import Projects.thermostat.MainMethodChoice
import Projects.thermostat.MainMethodSuffixes
import Projects.thermostat.MainMethodSpec
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodFour
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (hp : c.pc=0x80000d72#32) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<4 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<4 → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤24 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=BitVec.ofNat 32 (MainMethodSpec.tag (MainMethodSpec.classify 4 (fun i => (bytes i).toNat))) ∧
      MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,first,pa,a16,a17,ar,ac⟩ := MainMethodTests.at2147487090 B c ram base (bytes 0) hp h15 (memory 0 (by decide)) (data 0 (by decide))
  have a14 : a.get 14=6#32 := (ar 14 (by decide) (by decide)).trans h14
  have a15 : a.get 15=base := (ar 15 (by decide) (by decide)).trans h15
  by_cases hit : (bytes 0).toNat=80
  · have atFirst : a.pc=0x8000111e#32 := by simpa only [hit,ite_true] using pa
    obtain ⟨n,d,nb,tail,pd,d14,dr,dc⟩ := MainMethodSuffixes.post B a ram base bytes atFirst a15 a14 memory data
    refine ⟨3+n,d,by omega,first.trans tail,pd,?_,?_,dc.trans ac⟩
    · by_cases good : (bytes 1).toNat=79 ∧ (bytes 2).toNat=83 ∧ (bytes 3).toNat=84
      · simpa [MainMethodSpec.classify,MainMethodSpec.tag,hit,good] using d14
      · simpa [MainMethodSpec.classify,MainMethodSpec.tag,hit,good] using d14
    · intro r h14 h15 h16 h17;exact (dr r h14 h15 h16 h17).trans (ar r h16 h17)
  · have atOther : a.pc=0x80000d7e#32 := by simpa only [hit,ite_false] using pa
    obtain ⟨e,choice,pe,e17,er,ec⟩ := MainMethodChoice.contract B img a ram 0x80000d7e#32 0x3de#32 72 (bytes 0) atOther a16 (by decide) (by decide) (by decide) (by decide) re2147487102
      (by simpa only [show 0x80000d7e#32+4#32=0x80000d82#32 by decide +kernel] using re2147487106)
    have pe' : e.pc=(if (bytes 0).toNat≠72 then 0x80001160#32 else 0x80000d86#32) := by
      simpa only [show 0x80000d7e#32+4#32+0x3de#32=0x80001160#32 by decide +kernel,show 0x80000d7e#32+8#32=0x80000d86#32 by decide +kernel] using pe
    have e14 : e.get 14=6#32 := (er 14 (by decide)).trans a14
    have e15 : e.get 15=base := (er 15 (by decide)).trans a15
    by_cases other : (bytes 0).toNat=72
    · have notUnequal : ¬(bytes 0).toNat≠72 := by omega
      have atSecond : e.pc=0x80000d86#32 := by simpa only [notUnequal,ite_false] using pe'
      obtain ⟨n,d,nb,tail,pd,d14,dr,dc⟩ := MainMethodSuffixes.head B e ram base bytes atSecond e15 e14 memory data
      refine ⟨5+n,d,by omega,(first.trans choice).trans tail,pd,?_,?_,dc.trans (ec.trans ac)⟩
      · by_cases good : (bytes 1).toNat=69 ∧ (bytes 2).toNat=65 ∧ (bytes 3).toNat=68
        · simpa [MainMethodSpec.classify,MainMethodSpec.tag,hit,other,good] using d14
        · simpa [MainMethodSpec.classify,MainMethodSpec.tag,hit,other,good] using d14
      · intro r h14 h15 h16 h17;exact (dr r h14 h15 h16 h17).trans ((er r h17).trans (ar r h16 h17))
    · have atFail : e.pc=0x80001160#32 := by simpa only [if_pos other] using pe'
      refine ⟨5,e,by decide,first.trans choice,atFail,?_,?_,ec.trans ac⟩
      · simpa [MainMethodSpec.classify,MainMethodSpec.tag,hit,other] using e14
      · intro r _ _ h16 h17;exact (er r h17).trans (ar r h16 h17)
end E5R.Thermostat.MainMethodFour
